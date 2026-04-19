package main

import (
	"bufio"
	"context"
	"encoding/json"
	"fmt"
	"html/template"
	"io"
	"log"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

type ClaudeSessionInfo struct {
	SessionID string `json:"sessionId"`
	Cwd       string `json:"cwd"`
	Title     string `json:"title"`
	UpdatedAt string `json:"updatedAt"`
}

type ClaudeMessageView struct {
	Role    string
	Text    string
	HTML    template.HTML
	Model   string
	Loading bool
}

type ClaudeToolView struct {
	ID     string
	Title  string
	Kind   string
	Status string
}

type ClaudePermissionOptionView struct {
	ID   string
	Name string
	Kind string
}

type ClaudePermissionView struct {
	ID        string
	SessionID string
	Title     string
	Options   []ClaudePermissionOptionView
}

type ClaudeConversationView struct {
	SessionID    string
	Title        string
	CurrentModel string
	Messages     []ClaudeMessageView
	Tools        []ClaudeToolView
	Permissions  []ClaudePermissionView
	Running      bool
	StopReason   string
	Error        string
}

type ClaudeViewData struct {
	Enabled      bool
	Available    bool
	Error        string
	Cwd          string
	SelectedID   string
	CurrentModel string
	ModelOptions []string
	Sessions     []ClaudeSessionInfo
	Conversation ClaudeConversationView
}

type acpRPCMessage struct {
	JSONRPC string           `json:"jsonrpc"`
	ID      *json.RawMessage `json:"id,omitempty"`
	Method  string           `json:"method,omitempty"`
	Params  json.RawMessage  `json:"params,omitempty"`
	Result  json.RawMessage  `json:"result,omitempty"`
	Error   *acpRPCError     `json:"error,omitempty"`
}

type acpRPCError struct {
	Code    int    `json:"code"`
	Message string `json:"message"`
}

type acpProcess struct {
	cmd               *exec.Cmd
	stdin             io.WriteCloser
	cancel            context.CancelFunc
	mu                sync.Mutex
	nextID            int
	pending           map[string]chan acpRPCMessage
	notificationFunc  func(json.RawMessage)
	permissionRequest func(json.RawMessage, json.RawMessage) any
}

type acpInitializeResult struct {
	AgentCapabilities struct {
		LoadSession         bool           `json:"loadSession"`
		SessionCapabilities map[string]any `json:"sessionCapabilities"`
	} `json:"agentCapabilities"`
	AgentInfo struct {
		Title   string `json:"title"`
		Version string `json:"version"`
	} `json:"agentInfo"`
}

type acpSessionNewResult struct {
	SessionID string `json:"sessionId"`
}

type acpSessionListResult struct {
	Sessions   []ClaudeSessionInfo `json:"sessions"`
	NextCursor string              `json:"nextCursor"`
}

type acpPromptResult struct {
	StopReason string `json:"stopReason"`
}

type claudeManager struct {
	mu             sync.RWMutex
	active         map[string]*claudeTurnState
	history        map[string]ClaudeConversationView
	historyFetched map[string]time.Time
	sessions       []ClaudeSessionInfo
	sessionsErr    error
	sessionsAt     time.Time
	currentModel   string
}

type claudeTurnState struct {
	mu           sync.RWMutex
	SessionID    string
	Title        string
	CurrentModel string
	Messages     []ClaudeMessageView
	Tools        map[string]ClaudeToolView
	ToolOrder    []string
	Permissions  map[string]*claudePermissionState
	Running      bool
	MuteMessages bool
	StopReason   string
	Error        string
}

type claudePermissionState struct {
	View   ClaudePermissionView
	choice chan string
}

type claudeTranscriptEntry struct {
	Type    string `json:"type"`
	Content string `json:"content"`
	Message *struct {
		Role    string          `json:"role"`
		Model   string          `json:"model"`
		Content json.RawMessage `json:"content"`
	} `json:"message"`
}

var claudeHiddenMessagePatterns = []*regexp.Regexp{
	regexp.MustCompile(`(?is)<local-command-caveat>.*?</local-command-caveat>`),
	regexp.MustCompile(`(?is)<command-name>.*?</command-name>`),
	regexp.MustCompile(`(?is)<command-args>.*?</command-args>`),
}

var (
	claudeLocalCommandStdoutPattern  = regexp.MustCompile(`(?is)<local-command-stdout>(.*?)</local-command-stdout>`)
	claudeCommandMessagePattern      = regexp.MustCompile(`(?is)<command-message>(.*?)</command-message>`)
	claudeModelStdoutPattern         = regexp.MustCompile(`(?is)<local-command-stdout>\s*Set model to\s+([^<\s]+)\s*</local-command-stdout>`)
	claudeModelCommandMessagePattern = regexp.MustCompile(`(?is)<command-message>\s*Set model to\s+([^<\s]+)\s*</command-message>`)
	claudePlainModelPattern          = regexp.MustCompile(`(?im)^\s*(?:Set model to|/model)\s+([A-Za-z0-9._-]+)\s*$`)
)

var (
	mdCodeBlockPattern  = regexp.MustCompile("(?s)```(\\w*)\\n(.*?)```")
	mdInlineCodePattern = regexp.MustCompile("`([^`]+)`")
	mdBoldPattern       = regexp.MustCompile(`\*\*(.+?)\*\*`)
	mdItalicPattern     = regexp.MustCompile(`(?:^|[^*])\*([^*]+?)\*(?:[^*]|$)`)
	mdLinkPattern       = regexp.MustCompile(`\[([^\]]+)\]\(([^)]+)\)`)
)

func newClaudeManager() *claudeManager {
	return &claudeManager{
		active:         make(map[string]*claudeTurnState),
		history:        make(map[string]ClaudeConversationView),
		historyFetched: make(map[string]time.Time),
		currentModel:   "default",
	}
}

func newClaudeTurnState(sessionID string) *claudeTurnState {
	return &claudeTurnState{
		SessionID:   sessionID,
		Tools:       make(map[string]ClaudeToolView),
		Permissions: make(map[string]*claudePermissionState),
		Running:     true,
		StopReason:  "",
		ToolOrder:   []string{},
		Messages:    []ClaudeMessageView{},
	}
}

func claudeACPEnabled(cfg *Config) bool {
	return cfg != nil && cfg.Agents.ClaudeACP.Enabled
}

func claudeACPCwd(cfg *Config) (string, error) {
	if cfg != nil {
		if configured := strings.TrimSpace(cfg.Agents.ClaudeACP.Cwd); configured != "" {
			return filepath.Abs(expandPath(configured))
		}
	}
	return os.Getwd()
}

func claudeACPCommand(cfg *Config) (string, []string, error) {
	if cfg != nil {
		if command := strings.TrimSpace(cfg.Agents.ClaudeACP.Command); command != "" {
			return command, cfg.Agents.ClaudeACP.Args, nil
		}
	}
	if path, err := exec.LookPath("claude-agent-acp"); err == nil {
		return path, nil, nil
	}
	if path, err := exec.LookPath("npx"); err == nil {
		return path, []string{"-y", "@agentclientprotocol/claude-agent-acp"}, nil
	}
	return "", nil, fmt.Errorf("claude-agent-acp not found; install it or configure agents.claude_acp.command")
}

func claudeModelOptions(current string) []string {
	options := []string{
		"default",
		"claude-sonnet-4-6",
		"claude-opus-4-5",
		"sonnet",
		"opus",
	}
	current = strings.TrimSpace(current)
	if current == "" {
		return options
	}
	for _, option := range options {
		if option == current {
			return options
		}
	}
	return append([]string{current}, options...)
}

func (m *claudeManager) currentModelValue() string {
	m.mu.RLock()
	defer m.mu.RUnlock()
	if strings.TrimSpace(m.currentModel) == "" {
		return "default"
	}
	return m.currentModel
}

func (m *claudeManager) setCurrentModel(model string) {
	model = strings.TrimSpace(model)
	if model == "" {
		model = "default"
	}
	m.mu.Lock()
	m.currentModel = model
	m.mu.Unlock()
}

func startACPProcess(ctx context.Context, cfg *Config, onNotification func(json.RawMessage), onPermission func(json.RawMessage, json.RawMessage) any) (*acpProcess, error) {
	command, args, err := claudeACPCommand(cfg)
	if err != nil {
		return nil, err
	}
	cwd, err := claudeACPCwd(cfg)
	if err != nil {
		return nil, err
	}

	processCtx, cancel := context.WithCancel(ctx)
	cmd := exec.CommandContext(processCtx, command, args...)
	cmd.Dir = cwd

	stdin, err := cmd.StdinPipe()
	if err != nil {
		cancel()
		return nil, err
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		cancel()
		return nil, err
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		cancel()
		return nil, err
	}

	p := &acpProcess{
		cmd:               cmd,
		stdin:             stdin,
		cancel:            cancel,
		nextID:            1,
		pending:           make(map[string]chan acpRPCMessage),
		notificationFunc:  onNotification,
		permissionRequest: onPermission,
	}

	if err := cmd.Start(); err != nil {
		cancel()
		return nil, err
	}

	go p.readLoop(stdout)
	go p.logStderr(stderr)
	return p, nil
}

func (p *acpProcess) close() {
	if p == nil {
		return
	}
	if p.cancel != nil {
		p.cancel()
	}
	if p.stdin != nil {
		_ = p.stdin.Close()
	}
	if p.cmd != nil && p.cmd.Process != nil {
		_ = p.cmd.Wait()
	}
}

func (p *acpProcess) logStderr(r io.Reader) {
	scanner := bufio.NewScanner(r)
	scanner.Buffer(make([]byte, 0, 64*1024), 1024*1024)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line != "" {
			log.Printf("Claude ACP: %s", line)
		}
	}
}

func (p *acpProcess) readLoop(r io.Reader) {
	scanner := bufio.NewScanner(r)
	scanner.Buffer(make([]byte, 0, 64*1024), 10*1024*1024)
	for scanner.Scan() {
		line := scanner.Bytes()
		var msg acpRPCMessage
		if err := json.Unmarshal(line, &msg); err != nil {
			log.Printf("Claude ACP: invalid JSON-RPC message: %v", err)
			continue
		}
		if msg.Method != "" {
			p.handleIncomingRequest(msg)
			continue
		}
		if msg.ID == nil {
			continue
		}
		key := string(*msg.ID)
		p.mu.Lock()
		ch := p.pending[key]
		delete(p.pending, key)
		p.mu.Unlock()
		if ch != nil {
			ch <- msg
		}
	}
	if err := scanner.Err(); err != nil {
		log.Printf("Claude ACP read error: %v", err)
	}
}

func (p *acpProcess) handleIncomingRequest(msg acpRPCMessage) {
	if msg.ID == nil {
		if msg.Method == "session/update" && p.notificationFunc != nil {
			p.notificationFunc(msg.Params)
		}
		return
	}

	if msg.Method == "session/request_permission" && p.permissionRequest != nil {
		result := p.permissionRequest(*msg.ID, msg.Params)
		if err := p.writeMessage(map[string]any{
			"jsonrpc": "2.0",
			"id":      json.RawMessage(*msg.ID),
			"result":  result,
		}); err != nil {
			log.Printf("Claude ACP permission response error: %v", err)
		}
		return
	}

	if err := p.writeMessage(map[string]any{
		"jsonrpc": "2.0",
		"id":      json.RawMessage(*msg.ID),
		"error": map[string]any{
			"code":    -32601,
			"message": "method not supported by KindleVibe",
		},
	}); err != nil {
		log.Printf("Claude ACP response error: %v", err)
	}
}

func (p *acpProcess) writeMessage(v any) error {
	payload, err := json.Marshal(v)
	if err != nil {
		return err
	}
	p.mu.Lock()
	defer p.mu.Unlock()
	if _, err := p.stdin.Write(append(payload, '\n')); err != nil {
		return err
	}
	return nil
}

func (p *acpProcess) sendRequest(ctx context.Context, method string, params any, result any) error {
	p.mu.Lock()
	id := p.nextID
	p.nextID++
	rawID := json.RawMessage(strconv.Itoa(id))
	ch := make(chan acpRPCMessage, 1)
	p.pending[string(rawID)] = ch
	p.mu.Unlock()

	request := map[string]any{
		"jsonrpc": "2.0",
		"id":      id,
		"method":  method,
	}
	if params != nil {
		request["params"] = params
	}
	if err := p.writeMessage(request); err != nil {
		p.mu.Lock()
		delete(p.pending, string(rawID))
		p.mu.Unlock()
		return err
	}

	select {
	case <-ctx.Done():
		p.mu.Lock()
		delete(p.pending, string(rawID))
		p.mu.Unlock()
		return ctx.Err()
	case response := <-ch:
		if response.Error != nil {
			return fmt.Errorf("%s: %s", method, response.Error.Message)
		}
		if result == nil || len(response.Result) == 0 || string(response.Result) == "null" {
			return nil
		}
		return json.Unmarshal(response.Result, result)
	}
}

func (p *acpProcess) initialize(ctx context.Context) (acpInitializeResult, error) {
	var result acpInitializeResult
	params := map[string]any{
		"protocolVersion":    1,
		"clientCapabilities": map[string]any{},
		"clientInfo": map[string]string{
			"name":    "kindlevibe",
			"title":   "KindleVibe",
			"version": "0.1.0",
		},
	}
	err := p.sendRequest(ctx, "initialize", params, &result)
	return result, err
}

func (m *claudeManager) viewData(ctx context.Context, cfg *Config, selectedID string) ClaudeViewData {
	currentModel := m.currentModelValue()
	data := ClaudeViewData{
		Enabled:      claudeACPEnabled(cfg),
		SelectedID:   strings.TrimSpace(selectedID),
		CurrentModel: currentModel,
		ModelOptions: claudeModelOptions(currentModel),
	}
	if cwd, err := claudeACPCwd(cfg); err == nil {
		data.Cwd = cwd
	}
	if !data.Enabled {
		data.Error = "Claude ACP is disabled in config.yaml."
		return data
	}

	if data.SelectedID != "" {
		if active := m.activeTurn(data.SelectedID); active != nil {
			data.Available = true
			data.Sessions = m.cachedSessions()
			data.Conversation = active.view()
			if data.Conversation.CurrentModel != "" {
				data.CurrentModel = data.Conversation.CurrentModel
				data.ModelOptions = claudeModelOptions(data.CurrentModel)
			}
			return data
		}
	}

	sessions, err := m.listSessions(ctx, cfg)
	if err != nil {
		data.Error = err.Error()
	} else {
		data.Available = true
		data.Sessions = sessions
	}

	if data.SelectedID == "" {
		return data
	}

	conversation, err := m.loadConversation(ctx, cfg, data.SelectedID)
	if err != nil {
		data.Conversation = ClaudeConversationView{
			SessionID: data.SelectedID,
			Error:     err.Error(),
		}
		return data
	}
	data.Conversation = conversation
	if conversation.CurrentModel != "" {
		data.CurrentModel = conversation.CurrentModel
		data.ModelOptions = claudeModelOptions(data.CurrentModel)
		m.setCurrentModel(conversation.CurrentModel)
	}
	return data
}

func (m *claudeManager) activeTurn(sessionID string) *claudeTurnState {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.active[sessionID]
}

func (m *claudeManager) cachedSessions() []ClaudeSessionInfo {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return append([]ClaudeSessionInfo(nil), m.sessions...)
}

func (m *claudeManager) listSessions(ctx context.Context, cfg *Config) ([]ClaudeSessionInfo, error) {
	m.mu.RLock()
	if time.Since(m.sessionsAt) < 10*time.Second {
		sessions := append([]ClaudeSessionInfo(nil), m.sessions...)
		err := m.sessionsErr
		m.mu.RUnlock()
		return sessions, err
	}
	m.mu.RUnlock()

	if sessions, err := listLocalClaudeSessions(cfg); err == nil && len(sessions) > 0 {
		m.cacheSessions(sessions, nil)
		return sessions, nil
	}

	opCtx, cancel := context.WithTimeout(ctx, 20*time.Second)
	defer cancel()

	p, err := startACPProcess(opCtx, cfg, nil, nil)
	if err != nil {
		m.cacheSessions(nil, err)
		return nil, err
	}
	defer p.close()

	initResult, err := p.initialize(opCtx)
	if err != nil {
		m.cacheSessions(nil, err)
		return nil, err
	}
	if initResult.AgentCapabilities.SessionCapabilities == nil || initResult.AgentCapabilities.SessionCapabilities["list"] == nil {
		err := fmt.Errorf("Claude ACP agent does not support session/list")
		m.cacheSessions(nil, err)
		return nil, err
	}

	cwd, err := claudeACPCwd(cfg)
	if err != nil {
		m.cacheSessions(nil, err)
		return nil, err
	}
	var result acpSessionListResult
	if err := p.sendRequest(opCtx, "session/list", map[string]any{"cwd": cwd}, &result); err != nil {
		m.cacheSessions(nil, err)
		return nil, err
	}

	for i := range result.Sessions {
		if isModelTitle(result.Sessions[i].Title) {
			result.Sessions[i].Title = "New conversation"
		}
	}
	sort.Slice(result.Sessions, func(i, j int) bool {
		return result.Sessions[i].UpdatedAt > result.Sessions[j].UpdatedAt
	})
	if len(result.Sessions) > 20 {
		result.Sessions = result.Sessions[:20]
	}
	m.cacheSessions(result.Sessions, nil)
	return result.Sessions, nil
}

func (m *claudeManager) cacheSessions(sessions []ClaudeSessionInfo, err error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.sessions = append([]ClaudeSessionInfo(nil), sessions...)
	m.sessionsErr = err
	m.sessionsAt = time.Now()
}

func loadLocalClaudeConversation(cfg *Config, sessionID string) (ClaudeConversationView, error) {
	sessionID = strings.TrimSpace(sessionID)
	if sessionID == "" {
		return ClaudeConversationView{}, fmt.Errorf("missing session id")
	}
	path, err := localClaudeSessionPath(cfg, sessionID)
	if err != nil {
		return ClaudeConversationView{}, err
	}

	file, err := os.Open(path)
	if err != nil {
		return ClaudeConversationView{}, err
	}
	defer file.Close()

	state := newClaudeTurnState(sessionID)
	state.Running = false
	scanner := bufio.NewScanner(file)
	scanner.Buffer(make([]byte, 0, 64*1024), 10*1024*1024)
	for scanner.Scan() {
		var entry claudeTranscriptEntry
		if err := json.Unmarshal(scanner.Bytes(), &entry); err != nil {
			continue
		}
		if entry.Message != nil {
			role := strings.TrimSpace(entry.Message.Role)
			if role == "" {
				role = strings.TrimSpace(entry.Type)
			}
			if role == "user" || role == "assistant" {
				if model := strings.TrimSpace(entry.Message.Model); model != "" {
					state.mu.Lock()
					state.CurrentModel = model
					state.mu.Unlock()
				}
				state.appendMessage(role, claudeTranscriptContentText(entry.Message.Content))
			}
		}
		if entry.Type == "system" && strings.TrimSpace(entry.Content) != "" {
			text, model := normalizeClaudeMessageText(entry.Content)
			if model != "" {
				state.mu.Lock()
				state.CurrentModel = model
				state.mu.Unlock()
			}
			if text != "" {
				state.appendMessage("assistant", text)
			}
		}
	}
	if err := scanner.Err(); err != nil {
		return ClaudeConversationView{}, err
	}

	conversation := state.view()
	if len(conversation.Messages) == 0 && conversation.CurrentModel == "" {
		return ClaudeConversationView{}, fmt.Errorf("local Claude transcript has no visible messages")
	}
	return conversation, nil
}

func listLocalClaudeSessions(cfg *Config) ([]ClaudeSessionInfo, error) {
	projectDir, cwd, err := localClaudeProjectDir(cfg)
	if err != nil {
		return nil, err
	}
	entries, err := os.ReadDir(projectDir)
	if err != nil {
		return nil, err
	}
	sessions := make([]ClaudeSessionInfo, 0, len(entries))
	for _, entry := range entries {
		if entry.IsDir() || filepath.Ext(entry.Name()) != ".jsonl" {
			continue
		}
		info, err := entry.Info()
		if err != nil {
			continue
		}
		sessionID := strings.TrimSuffix(entry.Name(), ".jsonl")
		path := filepath.Join(projectDir, entry.Name())
		title := firstLocalClaudeSessionTitle(path)
		if title == "" || isModelTitle(title) {
			title = sessionID
		}
		sessions = append(sessions, ClaudeSessionInfo{
			SessionID: sessionID,
			Cwd:       cwd,
			Title:     title,
			UpdatedAt: info.ModTime().Format(time.RFC3339),
		})
	}
	sort.Slice(sessions, func(i, j int) bool {
		return sessions[i].UpdatedAt > sessions[j].UpdatedAt
	})
	if len(sessions) > 20 {
		sessions = sessions[:20]
	}
	return sessions, nil
}

func firstLocalClaudeSessionTitle(path string) string {
	file, err := os.Open(path)
	if err != nil {
		return ""
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	scanner.Buffer(make([]byte, 0, 64*1024), 1024*1024)
	for scanner.Scan() {
		var entry claudeTranscriptEntry
		if err := json.Unmarshal(scanner.Bytes(), &entry); err != nil || entry.Message == nil {
			continue
		}
		role := strings.TrimSpace(entry.Message.Role)
		if role == "" {
			role = strings.TrimSpace(entry.Type)
		}
		if role != "user" {
			continue
		}
		text, _ := normalizeClaudeMessageText(claudeTranscriptContentText(entry.Message.Content))
		if text != "" {
			return truncateText(text, 64)
		}
	}
	return ""
}

func localClaudeSessionPath(cfg *Config, sessionID string) (string, error) {
	projectDir, _, err := localClaudeProjectDir(cfg)
	if err != nil {
		return "", err
	}
	path := filepath.Join(projectDir, sessionID+".jsonl")
	if _, err := os.Stat(path); err == nil {
		return path, nil
	}
	return "", fmt.Errorf("local Claude transcript not found")
}

func localClaudeProjectDir(cfg *Config) (string, string, error) {
	cwd, err := claudeACPCwd(cfg)
	if err != nil {
		return "", "", err
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return "", "", err
	}
	projectDir := strings.ReplaceAll(cwd, string(os.PathSeparator), "-")
	return filepath.Join(home, ".claude", "projects", projectDir), cwd, nil
}

func claudeTranscriptContentText(raw json.RawMessage) string {
	if len(raw) == 0 || string(raw) == "null" {
		return ""
	}
	var text string
	if err := json.Unmarshal(raw, &text); err == nil {
		return text
	}
	var blocks []struct {
		Type string `json:"type"`
		Text string `json:"text"`
	}
	if err := json.Unmarshal(raw, &blocks); err == nil {
		parts := make([]string, 0, len(blocks))
		for _, block := range blocks {
			if block.Type == "text" && strings.TrimSpace(block.Text) != "" {
				parts = append(parts, block.Text)
			}
		}
		return strings.Join(parts, "\n")
	}
	return ""
}

func isModelTitle(title string) bool {
	t := strings.TrimSpace(strings.ToLower(title))
	if t == "" || t == "model" || t == "/model" {
		return true
	}
	if strings.HasPrefix(t, "/model ") || strings.HasPrefix(t, "model ") {
		return true
	}
	if strings.HasPrefix(t, "set model to") {
		return true
	}
	return false
}

func (m *claudeManager) rememberSession(session ClaudeSessionInfo) {
	if strings.TrimSpace(session.SessionID) == "" {
		return
	}
	if strings.TrimSpace(session.Title) == "" || isModelTitle(session.Title) {
		session.Title = "New conversation"
	}
	if strings.TrimSpace(session.UpdatedAt) == "" {
		session.UpdatedAt = time.Now().Format(time.RFC3339)
	}

	m.mu.Lock()
	defer m.mu.Unlock()
	next := []ClaudeSessionInfo{session}
	for _, existing := range m.sessions {
		if existing.SessionID != session.SessionID {
			next = append(next, existing)
		}
	}
	if len(next) > 20 {
		next = next[:20]
	}
	m.sessions = next
	m.sessionsErr = nil
	m.sessionsAt = time.Now()
}

func (m *claudeManager) loadConversation(ctx context.Context, cfg *Config, sessionID string) (ClaudeConversationView, error) {
	m.mu.RLock()
	if cached, ok := m.history[sessionID]; ok && time.Since(m.historyFetched[sessionID]) < 30*time.Second {
		m.mu.RUnlock()
		return cached, nil
	}
	m.mu.RUnlock()

	if conversation, err := loadLocalClaudeConversation(cfg, sessionID); err == nil {
		m.mu.Lock()
		m.history[sessionID] = conversation
		m.historyFetched[sessionID] = time.Now()
		m.mu.Unlock()
		return conversation, nil
	}

	state := newClaudeTurnState(sessionID)
	state.Running = false

	opCtx, cancel := context.WithTimeout(ctx, 30*time.Second)
	defer cancel()

	p, err := startACPProcess(opCtx, cfg, state.applyACPUpdate, nil)
	if err != nil {
		return ClaudeConversationView{}, err
	}
	defer p.close()

	initResult, err := p.initialize(opCtx)
	if err != nil {
		return ClaudeConversationView{}, err
	}
	if !initResult.AgentCapabilities.LoadSession {
		return ClaudeConversationView{}, fmt.Errorf("Claude ACP agent does not support session/load")
	}

	cwd, err := claudeACPCwd(cfg)
	if err != nil {
		return ClaudeConversationView{}, err
	}
	if err := p.sendRequest(opCtx, "session/load", map[string]any{
		"sessionId":  sessionID,
		"cwd":        cwd,
		"mcpServers": []any{},
	}, nil); err != nil {
		return ClaudeConversationView{}, err
	}

	conversation := state.view()
	m.mu.Lock()
	m.history[sessionID] = conversation
	m.historyFetched[sessionID] = time.Now()
	m.mu.Unlock()
	return conversation, nil
}

func (m *claudeManager) beginPrompt(cfg *Config, sessionID string, prompt string) (string, error) {
	prompt = strings.TrimSpace(prompt)
	if prompt == "" {
		return "", fmt.Errorf("prompt is empty")
	}
	if !claudeACPEnabled(cfg) {
		return "", fmt.Errorf("Claude ACP is disabled")
	}

	ctx := context.Background()
	var state *claudeTurnState
	p, err := startACPProcess(ctx, cfg, func(params json.RawMessage) {
		if state != nil {
			state.applyACPUpdate(params)
		}
	}, func(id json.RawMessage, params json.RawMessage) any {
		if state == nil {
			return map[string]any{"outcome": map[string]string{"outcome": "cancelled"}}
		}
		return state.waitForPermission(id, params)
	})
	if err != nil {
		return "", err
	}

	initCtx, cancel := context.WithTimeout(ctx, 30*time.Second)
	defer cancel()
	initResult, err := p.initialize(initCtx)
	if err != nil {
		p.close()
		return "", err
	}

	cwd, err := claudeACPCwd(cfg)
	if err != nil {
		p.close()
		return "", err
	}
	sessionID = strings.TrimSpace(sessionID)
	isNewSession := sessionID == ""
	if sessionID == "" {
		var newResult acpSessionNewResult
		if err := p.sendRequest(initCtx, "session/new", map[string]any{
			"cwd":        cwd,
			"mcpServers": []any{},
		}, &newResult); err != nil {
			p.close()
			return "", err
		}
		sessionID = strings.TrimSpace(newResult.SessionID)
	}
	if sessionID == "" {
		p.close()
		return "", fmt.Errorf("Claude ACP returned an empty session id")
	}

	state = newClaudeTurnState(sessionID)
	state.Title = truncateText(prompt, 64)
	state.CurrentModel = m.currentModelValue()
	state.appendMessage("user", prompt)
	m.mu.Lock()
	m.active[sessionID] = state
	delete(m.history, sessionID)
	delete(m.historyFetched, sessionID)
	m.mu.Unlock()
	m.rememberSession(ClaudeSessionInfo{
		SessionID: sessionID,
		Cwd:       cwd,
		Title:     state.Title,
		UpdatedAt: time.Now().Format(time.RFC3339),
	})

	go func() {
		defer p.close()
		defer func() {
			completed := state.view()
			m.mu.Lock()
			delete(m.active, sessionID)
			if len(completed.Messages) > 0 || completed.Error != "" {
				m.history[sessionID] = completed
				m.historyFetched[sessionID] = time.Now().Add(-25 * time.Second)
			} else {
				delete(m.history, sessionID)
				delete(m.historyFetched, sessionID)
			}
			m.sessionsAt = time.Now()
			m.mu.Unlock()
		}()

		runCtx := context.Background()
		if initResult.AgentCapabilities.LoadSession && strings.TrimSpace(sessionID) != "" && !isNewSession {
			cwd, err := claudeACPCwd(cfg)
			if err == nil {
				_ = p.sendRequest(runCtx, "session/load", map[string]any{
					"sessionId":  sessionID,
					"cwd":        cwd,
					"mcpServers": []any{},
				}, nil)
			}
		}
		if model := strings.TrimSpace(m.currentModelValue()); model != "" && model != "default" {
			state.mu.Lock()
			state.MuteMessages = true
			state.mu.Unlock()
			var modelResult acpPromptResult
			err := p.sendRequest(runCtx, "session/prompt", map[string]any{
				"sessionId": sessionID,
				"prompt": []map[string]string{
					{"type": "text", "text": "/model " + model},
				},
			}, &modelResult)
			state.mu.Lock()
			state.MuteMessages = false
			state.mu.Unlock()
			if err != nil {
				state.finish("", err)
				return
			}
		}
		var promptResult acpPromptResult
		err := p.sendRequest(runCtx, "session/prompt", map[string]any{
			"sessionId": sessionID,
			"prompt": []map[string]string{
				{"type": "text", "text": prompt},
			},
		}, &promptResult)
		if err != nil {
			state.finish("", err)
			return
		}
		state.finish(promptResult.StopReason, nil)
	}()

	return sessionID, nil
}

func (m *claudeManager) selectPermission(sessionID string, requestID string, optionID string) error {
	active := m.activeTurn(strings.TrimSpace(sessionID))
	if active == nil {
		return fmt.Errorf("no active Claude turn for session")
	}
	return active.selectPermission(strings.TrimSpace(requestID), strings.TrimSpace(optionID))
}

func (s *claudeTurnState) applyACPUpdate(params json.RawMessage) {
	var payload struct {
		SessionID string          `json:"sessionId"`
		Update    json.RawMessage `json:"update"`
	}
	if err := json.Unmarshal(params, &payload); err != nil || len(payload.Update) == 0 {
		return
	}
	var update struct {
		SessionUpdate string          `json:"sessionUpdate"`
		Content       json.RawMessage `json:"content"`
		ToolCallID    string          `json:"toolCallId"`
		Title         string          `json:"title"`
		Kind          string          `json:"kind"`
		Status        string          `json:"status"`
	}
	if err := json.Unmarshal(payload.Update, &update); err != nil {
		return
	}

	switch update.SessionUpdate {
	case "user_message_chunk":
		s.appendMessage("user", acpContentText(update.Content))
	case "agent_message_chunk":
		s.appendMessage("assistant", acpContentText(update.Content))
	case "tool_call", "tool_call_update":
		s.updateTool(update.ToolCallID, update.Title, update.Kind, update.Status)
	case "session_info_update":
		if strings.TrimSpace(update.Title) != "" {
			s.mu.Lock()
			if !s.MuteMessages {
				s.Title = strings.TrimSpace(update.Title)
			}
			s.mu.Unlock()
		}
	}
}

func (s *claudeTurnState) appendMessage(role string, text string) {
	s.mu.RLock()
	muted := s.MuteMessages
	s.mu.RUnlock()
	text, model := normalizeClaudeMessageText(text)
	if muted {
		if model != "" {
			s.mu.Lock()
			s.CurrentModel = model
			s.mu.Unlock()
		}
		return
	}
	if text == "" {
		if model != "" {
			s.mu.Lock()
			s.CurrentModel = model
			s.mu.Unlock()
		}
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if model != "" {
		s.CurrentModel = model
	}
	if len(s.Messages) > 0 && s.Messages[len(s.Messages)-1].Role == role {
		if role == "user" && s.Messages[len(s.Messages)-1].Text == text {
			return
		}
		if s.Messages[len(s.Messages)-1].Text == "" {
			s.Messages[len(s.Messages)-1].Text = text
		} else {
			s.Messages[len(s.Messages)-1].Text += "\n" + text
		}
		return
	}
	msg := ClaudeMessageView{Role: role, Text: text}
	if role == "assistant" {
		msg.Model = s.CurrentModel
	}
	s.Messages = append(s.Messages, msg)
}

func normalizeClaudeMessageText(text string) (string, string) {
	text = strings.TrimSpace(text)
	if text == "" {
		return "", ""
	}
	model := extractClaudeModel(text)
	cleaned := text
	for _, pattern := range claudeHiddenMessagePatterns {
		cleaned = pattern.ReplaceAllString(cleaned, "")
	}
	cleaned = claudeLocalCommandStdoutPattern.ReplaceAllStringFunc(cleaned, func(match string) string {
		if claudeModelStdoutPattern.MatchString(match) {
			return ""
		}
		parts := claudeLocalCommandStdoutPattern.FindStringSubmatch(match)
		if len(parts) > 1 {
			return strings.TrimSpace(parts[1])
		}
		return match
	})
	cleaned = claudeCommandMessagePattern.ReplaceAllStringFunc(cleaned, func(match string) string {
		if claudeModelCommandMessagePattern.MatchString(match) {
			return ""
		}
		parts := claudeCommandMessagePattern.FindStringSubmatch(match)
		if len(parts) > 1 {
			return strings.TrimSpace(parts[1])
		}
		return match
	})
	cleaned = strings.TrimSpace(cleaned)
	if model == "" {
		if match := claudePlainModelPattern.FindStringSubmatch(cleaned); len(match) > 1 {
			model = strings.TrimSpace(match[1])
			cleaned = ""
		}
	}
	if strings.HasPrefix(cleaned, "/model ") || cleaned == "/model" {
		cleaned = ""
	}
	lower := strings.ToLower(cleaned)
	if strings.Contains(lower, "/model isn't available") {
		cleaned = ""
	}
	if strings.HasPrefix(lower, "set model to ") || strings.HasPrefix(lower, "model set to ") || strings.HasPrefix(lower, "model: ") {
		cleaned = ""
	}
	if cleaned == "model" {
		cleaned = ""
	}
	return cleaned, model
}

func extractClaudeModel(text string) string {
	if match := claudeModelStdoutPattern.FindStringSubmatch(text); len(match) > 1 {
		return strings.TrimSpace(match[1])
	}
	if match := claudeModelCommandMessagePattern.FindStringSubmatch(text); len(match) > 1 {
		return strings.TrimSpace(match[1])
	}
	if match := claudePlainModelPattern.FindStringSubmatch(text); len(match) > 1 {
		return strings.TrimSpace(match[1])
	}
	return ""
}

func renderBasicMarkdown(text string) template.HTML {
	text = strings.TrimSpace(text)
	if text == "" {
		return ""
	}

	// Extract code blocks first to protect them from other transformations
	type codeBlock struct {
		lang string
		code string
	}
	var blocks []codeBlock
	text = mdCodeBlockPattern.ReplaceAllStringFunc(text, func(match string) string {
		parts := mdCodeBlockPattern.FindStringSubmatch(match)
		idx := len(blocks)
		blocks = append(blocks, codeBlock{lang: parts[1], code: parts[2]})
		return fmt.Sprintf("\uFFFCCODEBLOCK%d\uFFFC", idx)
	})

	// Extract inline code to protect from other transformations
	var inlines []string
	text = mdInlineCodePattern.ReplaceAllStringFunc(text, func(match string) string {
		parts := mdInlineCodePattern.FindStringSubmatch(match)
		idx := len(inlines)
		inlines = append(inlines, parts[1])
		return fmt.Sprintf("\uFFFCINLINE%d\uFFFC", idx)
	})

	// Escape HTML in the remaining text
	text = template.HTMLEscapeString(text)

	// Process line-based elements
	lines := strings.Split(text, "\n")
	var out []string
	inList := ""
	for _, line := range lines {
		trimmed := strings.TrimSpace(line)

		// Close open list if line doesn't continue it
		isUL := strings.HasPrefix(trimmed, "- ") || strings.HasPrefix(trimmed, "* ")
		isOL := len(trimmed) > 2 && trimmed[0] >= '0' && trimmed[0] <= '9' && strings.Contains(trimmed[:min(5, len(trimmed))], ". ")
		if inList == "ul" && !isUL {
			out = append(out, "</ul>")
			inList = ""
		}
		if inList == "ol" && !isOL {
			out = append(out, "</ol>")
			inList = ""
		}

		switch {
		case trimmed == "---" || trimmed == "***" || trimmed == "___":
			out = append(out, "<hr>")
		case strings.HasPrefix(trimmed, "### "):
			out = append(out, "<h4>"+trimmed[4:]+"</h4>")
		case strings.HasPrefix(trimmed, "## "):
			out = append(out, "<h3>"+trimmed[3:]+"</h3>")
		case strings.HasPrefix(trimmed, "# "):
			out = append(out, "<h2>"+trimmed[2:]+"</h2>")
		case isUL:
			if inList != "ul" {
				out = append(out, "<ul>")
				inList = "ul"
			}
			content := trimmed[2:]
			out = append(out, "<li>"+content+"</li>")
		case isOL:
			if inList != "ol" {
				out = append(out, "<ol>")
				inList = "ol"
			}
			dot := strings.Index(trimmed, ". ")
			content := trimmed[dot+2:]
			out = append(out, "<li>"+content+"</li>")
		default:
			out = append(out, line)
		}
	}
	if inList == "ul" {
		out = append(out, "</ul>")
	}
	if inList == "ol" {
		out = append(out, "</ol>")
	}
	text = strings.Join(out, "\n")

	// Inline formatting
	text = mdBoldPattern.ReplaceAllString(text, "<strong>$1</strong>")
	text = mdItalicPattern.ReplaceAllStringFunc(text, func(match string) string {
		// Preserve leading/trailing non-* characters
		start := 0
		end := len(match)
		if match[0] != '*' {
			start = 1
		}
		if match[end-1] != '*' {
			end -= 1
		}
		inner := match[start+1 : end-1]
		return match[:start] + "<em>" + inner + "</em>" + match[end:]
	})
	text = mdLinkPattern.ReplaceAllString(text, `<a href="$2">$1</a>`)

	// Restore inline code
	for i, code := range inlines {
		escaped := template.HTMLEscapeString(code)
		text = strings.Replace(text, fmt.Sprintf("\uFFFCINLINE%d\uFFFC", i), "<code>"+escaped+"</code>", 1)
	}

	// Restore code blocks
	for i, block := range blocks {
		escaped := template.HTMLEscapeString(strings.TrimRight(block.code, "\n"))
		text = strings.Replace(text, fmt.Sprintf("\uFFFCCODEBLOCK%d\uFFFC", i), "<pre><code>"+escaped+"</code></pre>", 1)
	}

	return template.HTML(text)
}

func (s *claudeTurnState) updateTool(id string, title string, kind string, status string) {
	id = strings.TrimSpace(id)
	if id == "" {
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	tool, exists := s.Tools[id]
	if !exists {
		tool = ClaudeToolView{ID: id}
		s.ToolOrder = append(s.ToolOrder, id)
	}
	if title = strings.TrimSpace(title); title != "" {
		tool.Title = title
	}
	if kind = strings.TrimSpace(kind); kind != "" {
		tool.Kind = kind
	}
	if status = strings.TrimSpace(status); status != "" {
		tool.Status = status
	}
	s.Tools[id] = tool
}

func (s *claudeTurnState) waitForPermission(id json.RawMessage, params json.RawMessage) any {
	requestID := string(id)
	view := ClaudePermissionView{
		ID:        requestID,
		SessionID: s.SessionID,
		Title:     "Permission requested",
	}
	var payload struct {
		SessionID string `json:"sessionId"`
		ToolCall  struct {
			ToolCallID string `json:"toolCallId"`
			Title      string `json:"title"`
			Kind       string `json:"kind"`
		} `json:"toolCall"`
		Options []struct {
			OptionID string `json:"optionId"`
			Name     string `json:"name"`
			Kind     string `json:"kind"`
		} `json:"options"`
	}
	if err := json.Unmarshal(params, &payload); err == nil {
		view.SessionID = payload.SessionID
		if title := strings.TrimSpace(payload.ToolCall.Title); title != "" {
			view.Title = title
		} else if payload.ToolCall.ToolCallID != "" {
			view.Title = payload.ToolCall.ToolCallID
		}
		for _, option := range payload.Options {
			name := strings.TrimSpace(option.Name)
			if name == "" {
				name = option.OptionID
			}
			view.Options = append(view.Options, ClaudePermissionOptionView{
				ID:   option.OptionID,
				Name: name,
				Kind: option.Kind,
			})
		}
	}

	if len(view.Options) == 0 {
		view.Options = []ClaudePermissionOptionView{
			{ID: "reject-once", Name: "Reject", Kind: "reject_once"},
		}
	}

	permission := &claudePermissionState{
		View:   view,
		choice: make(chan string, 1),
	}
	s.mu.Lock()
	s.Permissions[requestID] = permission
	s.mu.Unlock()

	optionID := <-permission.choice

	s.mu.Lock()
	delete(s.Permissions, requestID)
	s.mu.Unlock()

	if optionID == "" {
		return map[string]any{"outcome": map[string]string{"outcome": "cancelled"}}
	}
	return map[string]any{"outcome": map[string]string{"outcome": "selected", "optionId": optionID}}
}

func (s *claudeTurnState) selectPermission(requestID string, optionID string) error {
	if requestID == "" || optionID == "" {
		return fmt.Errorf("missing permission request or option")
	}
	s.mu.RLock()
	permission := s.Permissions[requestID]
	s.mu.RUnlock()
	if permission == nil {
		return fmt.Errorf("permission request is no longer pending")
	}
	permission.choice <- optionID
	return nil
}

func (s *claudeTurnState) finish(stopReason string, err error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.Running = false
	s.StopReason = strings.TrimSpace(stopReason)
	if err != nil {
		s.Error = err.Error()
	}
}

func (s *claudeTurnState) view() ClaudeConversationView {
	s.mu.RLock()
	defer s.mu.RUnlock()

	messages := append([]ClaudeMessageView(nil), s.Messages...)
	if s.Running {
		if len(messages) > 0 && messages[len(messages)-1].Role == "assistant" {
			messages[len(messages)-1].Loading = true
		} else {
			messages = append(messages, ClaudeMessageView{
				Role:    "assistant",
				Text:    "",
				Loading: true,
			})
		}
	}
	for i := range messages {
		if messages[i].Text != "" {
			messages[i].HTML = renderBasicMarkdown(messages[i].Text)
		}
	}

	tools := make([]ClaudeToolView, 0, len(s.Tools))
	for _, id := range s.ToolOrder {
		if tool, ok := s.Tools[id]; ok {
			tools = append(tools, tool)
		}
	}

	permissions := make([]ClaudePermissionView, 0, len(s.Permissions))
	for _, permission := range s.Permissions {
		permissions = append(permissions, permission.View)
	}
	sort.Slice(permissions, func(i, j int) bool {
		return permissions[i].ID < permissions[j].ID
	})

	return ClaudeConversationView{
		SessionID:    s.SessionID,
		Title:        s.Title,
		CurrentModel: s.CurrentModel,
		Messages:     messages,
		Tools:        tools,
		Permissions:  permissions,
		Running:      s.Running,
		StopReason:   s.StopReason,
		Error:        s.Error,
	}
}

func acpContentText(raw json.RawMessage) string {
	if len(raw) == 0 || string(raw) == "null" {
		return ""
	}
	var block struct {
		Type string `json:"type"`
		Text string `json:"text"`
	}
	if err := json.Unmarshal(raw, &block); err == nil {
		if strings.TrimSpace(block.Text) != "" {
			return block.Text
		}
	}
	var blocks []json.RawMessage
	if err := json.Unmarshal(raw, &blocks); err == nil {
		parts := make([]string, 0, len(blocks))
		for _, item := range blocks {
			if text := acpContentText(item); text != "" {
				parts = append(parts, text)
			}
		}
		return strings.Join(parts, "\n")
	}
	return ""
}

func claudePageHandler(cfg *Config, cache *dashboardCache, manager *claudeManager, tmpl *template.Template) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		data := cache.getOrRefresh(cfg)
		data.Tab = "claude"
		data.Claude = manager.viewData(r.Context(), cfg, r.URL.Query().Get("session_id"))
		if err := tmpl.Execute(w, data); err != nil {
			log.Printf("Claude Template Execute Error: %v", err)
		}
	}
}

func claudeFragmentHandler(cfg *Config, manager *claudeManager, tmpl *template.Template) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		data := manager.viewData(r.Context(), cfg, r.URL.Query().Get("session_id"))
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		if err := tmpl.ExecuteTemplate(w, "claude-content", data); err != nil {
			log.Printf("Claude Fragment Execute Error: %v", err)
		}
	}
}

func claudeSendHandler(cfg *Config, manager *claudeManager) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
			return
		}
		sessionID := strings.TrimSpace(r.FormValue("session_id"))
		prompt := strings.TrimSpace(r.FormValue("prompt"))
		if isLocalClaudeCommand(prompt, "resume") {
			if wantsJSON(r) {
				w.Header().Set("Content-Type", "application/json")
				_ = json.NewEncoder(w).Encode(map[string]string{
					"session_id": sessionID,
					"command":    "resume",
				})
				return
			}
			http.Redirect(w, r, "/claude?history=1", http.StatusSeeOther)
			return
		}
		nextSessionID, err := manager.beginPrompt(cfg, sessionID, prompt)
		if err != nil {
			log.Printf("Claude ACP Send Error: %v", err)
			if wantsJSON(r) {
				w.Header().Set("Content-Type", "application/json")
				w.WriteHeader(http.StatusBadRequest)
				_ = json.NewEncoder(w).Encode(map[string]string{"error": err.Error()})
				return
			}
			http.Redirect(w, r, "/claude", http.StatusSeeOther)
			return
		}
		if wantsJSON(r) {
			w.Header().Set("Content-Type", "application/json")
			_ = json.NewEncoder(w).Encode(map[string]string{"session_id": nextSessionID})
			return
		}
		http.Redirect(w, r, "/claude?session_id="+url.QueryEscape(nextSessionID), http.StatusSeeOther)
	}
}

func isLocalClaudeCommand(prompt string, command string) bool {
	prompt = strings.TrimSpace(prompt)
	command = strings.TrimPrefix(strings.TrimSpace(command), "/")
	if prompt == "" || command == "" || !strings.HasPrefix(prompt, "/") {
		return false
	}
	name := strings.TrimPrefix(strings.Fields(prompt)[0], "/")
	return strings.EqualFold(name, command)
}

func claudeModelHandler(manager *claudeManager) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
			return
		}
		model := strings.TrimSpace(r.FormValue("model"))
		if model == "" {
			model = "default"
		}
		manager.setCurrentModel(model)
		if wantsJSON(r) {
			w.Header().Set("Content-Type", "application/json")
			_ = json.NewEncoder(w).Encode(map[string]string{"current_model": model})
			return
		}
		sessionID := strings.TrimSpace(r.FormValue("session_id"))
		if sessionID != "" {
			http.Redirect(w, r, "/claude?session_id="+url.QueryEscape(sessionID), http.StatusSeeOther)
			return
		}
		http.Redirect(w, r, "/claude", http.StatusSeeOther)
	}
}

func wantsJSON(r *http.Request) bool {
	return strings.Contains(r.Header.Get("Accept"), "application/json") ||
		strings.EqualFold(r.Header.Get("X-Requested-With"), "XMLHttpRequest")
}

func claudePermissionHandler(manager *claudeManager) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost {
			http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
			return
		}
		sessionID := strings.TrimSpace(r.FormValue("session_id"))
		requestID := strings.TrimSpace(r.FormValue("request_id"))
		optionID := strings.TrimSpace(r.FormValue("option_id"))
		if err := manager.selectPermission(sessionID, requestID, optionID); err != nil {
			log.Printf("Claude ACP Permission Error: %v", err)
		}
		http.Redirect(w, r, "/claude?session_id="+url.QueryEscape(sessionID), http.StatusSeeOther)
	}
}
