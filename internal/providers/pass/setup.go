package main

import (
	"bufio"
	"crypto/hmac"
	"crypto/sha1"
	"encoding/base32"
	"encoding/binary"
	"fmt"
	"log/slog"
	"net"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"

	_ "embed"

	"github.com/abenz1267/elephant/v2/internal/util"
	"github.com/abenz1267/elephant/v2/pkg/common"
	"github.com/abenz1267/elephant/v2/pkg/pb/pb"
)

var (
	Name       = "pass"
	NamePretty = "Pass (password-store)"
	config     *Config

	// sessions keyed by connection remote address
	sessionsMu sync.Mutex
	sessions   = map[string]*sessionState{}
)

//go:embed README.md
var readme string

const (
	// actions
	ActionOpen    = "open"     // drill down into store or entry
	ActionPaste   = "paste"    // paste a field
	ActionOTP     = "otp"      // generate otp and paste
	ActionAuto    = "autotype" // username<TAB>password
	ActionBack    = "back"     // go back to previous menu
	CommandToken  = "%CONTENT%"
	PasswordLabel = "password"
)

type Config struct {
	common.Config `koanf:",squash"`

	Command string      `koanf:"command" desc:"default command to paste content into focused window. supports %CONTENT%." default:"wtype %CONTENT%"`
	Delay   int         `koanf:"delay" desc:"delay in ms before executing command to avoid potential focus issues" default:"100"`
	Stores  []PassStore `koanf:"pass" desc:"configured password stores" default:""`
}

type PassStore struct {
	Keywords []string `koanf:"keywords" desc:"searchable keywords for this store" default:""`
	Name     string   `koanf:"name" desc:"display name for this store" default:""`
	Path     string   `koanf:"path" desc:"filesystem path to the password store (password-store style)" default:""`
	Key      string   `koanf:"key" desc:"default key id or email used to encrypt / identify store (optional)" default:""`
}

type parsedEntry struct {
	EntryPath string            // relative path used as display (flattened)
	FilePath  string            // actual .gpg file path
	Fields    []string          // keys order (first is "password")
	Values    map[string]string // key -> value
	Score     int32
	Fuzzyinfo *pb.QueryResponse_Item_FuzzyInfo
}

type sessionState struct {
	Mode         string // "", "stores", "entries", "fields"
	StoreIndex   int
	Entries      []parsedEntry
	SelectedEntry int  // index in Entries; used when Mode == "fields"
	FieldsCached  bool // true if fields parsed and stored in Entries[SelectedEntry]
	// timestamp to expire session if needed (not enforced here)
}

func Setup() {
	config = &Config{
		Config: common.Config{
			Icon:     "key",
			MinScore: 50,
		},
		Command: "wtype %CONTENT%",
		Delay:   100,
		Stores:  []PassStore{},
	}

	common.LoadConfig(Name, config)
}

func Available() bool {
	return true
}

func PrintDoc() {
	fmt.Println(readme)
	fmt.Println()
	util.PrintConfig(Config{}, Name)
}

func Icon() string {
	return config.Icon
}

func State(provider string) *pb.ProviderStateResponse {
	// stateless provider for now; actions handled on Activate
	return &pb.ProviderStateResponse{}
}

// -------------------- Query flow --------------------

func Query(conn net.Conn, query string, single bool, exact bool, _ uint8) []*pb.QueryResponse_Item {
	start := time.Now()

	key := connKey(conn)
	s := getSession(key)

	entries := []*pb.QueryResponse_Item{}

	switch s.Mode {
	case "", "stores":
		// list configured stores
		for idx, st := range config.Stores {
			e := &pb.QueryResponse_Item{
				Identifier: fmt.Sprintf("store:%d", idx),
				Text:       st.Name,
				Actions:    []string{ActionOpen},
				Icon:       Icon(),
				Provider:   Name,
				Score:      int32(100000 - idx),
				Type:       0,
			}

			if query != "" {
				score, positions, startPos, found := calcStoreScore(query, st, exact)
				if found {
					e.Score = score
					e.Fuzzyinfo = &pb.QueryResponse_Item_FuzzyInfo{
						Start:     startPos,
						Field:     "text",
						Positions: positions,
					}
				}
			}

			if query == "" || e.Score > config.MinScore {
				entries = append(entries, e)
			}
		}
	case "entries":
		// list entries in selected store (searchable)
		if s.StoreIndex < 0 || s.StoreIndex >= len(config.Stores) {
			// invalid store -> reset
			s.Mode = "stores"
			return Query(conn, query, single, exact, 0)
		}

		// Build index if empty
		if len(s.Entries) == 0 {
			buildEntriesForStore(&s.Entries, config.Stores[s.StoreIndex].Path)
		}
		// Use the entries in s.Entries (already flattened)
		for idx := range s.Entries {
			e := &pb.QueryResponse_Item{
				Identifier: fmt.Sprintf("entry:%d", idx),
				Text:       s.Entries[idx].EntryPath,
				Actions:    []string{ActionOpen},
				Icon:       Icon(),
				Provider:   Name,
				Score:      int32(100000 - idx),
				Type:       0,
			}

			if query != "" {
				score, positions, startPos, found := calcEntryScore(query, s.Entries[idx], exact)
				if found {
					e.Score = score
					e.Fuzzyinfo = &pb.QueryResponse_Item_FuzzyInfo{
						Start:     startPos,
						Field:     "text",
						Positions: positions,
					}
				}
			}

			if query == "" || e.Score > config.MinScore {
				entries = append(entries, e)
			}
		}
	case "fields":
		// list parsed fields for the selected entry (values are not shown)
		// selected entry must be valid
		if s.SelectedEntry < 0 || s.SelectedEntry >= len(s.Entries) {
			s.Mode = "entries"
			return Query(conn, query, single, exact, 0)
		}

		pe := &s.Entries[s.SelectedEntry]
		// ensure parsed
		if !peIsParsed(pe) {
			// should not happen: the Activate for entry should have parsed; but fallback: parse now
			if err := decryptAndParseFile(pe); err != nil {
				slog.Error(Name, "decrypt_parse_error", err)
				return entries
			}
		}

		// Always provide a "Back" item as first action
		back := &pb.QueryResponse_Item{
			Identifier: "back:0",
			Text:       "← Back",
			Actions:    []string{ActionBack},
			Icon:       "arrow-left",
			Provider:   Name,
			Score:      9999999,
		}
		entries = append(entries, back)

		// password field should be listed as first item named 'password', with ActionPaste and ActionAuto if username exists
		for fidx, keyname := range pe.Fields {
			actions := []string{ActionPaste}
			fieldKind := keyKind(pe.Values[keyname])

			if fieldKind == "otp_uri" {
				actions = []string{ActionOTP}
			} else if keyname == PasswordLabel {
				// autotype if username available
				if _, ok := pe.Values["username"]; ok {
					actions = append(actions, ActionAuto)
				}
			}

			item := &pb.QueryResponse_Item{
				Identifier: fmt.Sprintf("field:%d", fidx),
				Text:       keyname,
				Actions:    actions,
				Icon:       Icon(),
				Provider:   Name,
				Score:      int32(100000 - fidx),
				Type:       0,
			}

			entries = append(entries, item)
		}
	default:
		// unknown -> reset
		s.Mode = "stores"
		return Query(conn, query, single, exact, 0)
	}

	slog.Info(Name, "queryresult", len(entries), "time", time.Since(start))
	return entries
}

// -------------------- Activate flow --------------------

func Activate(single bool, identifier, action string, query string, args string, format uint8, conn net.Conn) {
	// small delay to avoid focus race when typing
	time.Sleep(time.Duration(config.Delay) * time.Millisecond)

	key := connKey(conn)
	s := getSession(key)

	// Parse identifier prefixes: store:<i>, entry:<i>, field:<i>, back:0
	switch {
	case strings.HasPrefix(identifier, "store:"):
		// store selected -> open the store (ActionOpen expected)
		iStr := strings.TrimPrefix(identifier, "store:")
		i, _ := strconv.Atoi(iStr)
		if i < 0 || i >= len(config.Stores) {
			slog.Error(Name, "activate", fmt.Errorf("invalid store index %d", i))
			return
		}
		s.Mode = "entries"
		s.StoreIndex = i
		// clear previous entries to force re-index
		s.Entries = []parsedEntry{}
		s.SelectedEntry = -1
		return
	case strings.HasPrefix(identifier, "entry:"):
		// entry selected -> decrypt file and parse fields, then switch to fields mode
		iStr := strings.TrimPrefix(identifier, "entry:")
		i, _ := strconv.Atoi(iStr)
		if s.Mode != "entries" {
			// nothing to do
			return
		}
		if i < 0 {
			return
		}
		// ensure entries are built
		if len(s.Entries) == 0 {
			buildEntriesForStore(&s.Entries, config.Stores[s.StoreIndex].Path)
		}
		if i >= len(s.Entries) {
			return
		}
		// decrypt selected file and parse
		pe := &s.Entries[i]
		if err := decryptAndParseFile(pe); err != nil {
			slog.Error(Name, "decrypt", err)
			return
		}
		s.SelectedEntry = i
		s.Mode = "fields"
		return
	case strings.HasPrefix(identifier, "back:"):
		// go back to entries list
		if s.Mode == "fields" {
			s.Mode = "entries"
			s.SelectedEntry = -1
		} else {
			s.Mode = "stores"
		}
		return
	case strings.HasPrefix(identifier, "field:"):
		// user chose an action for a field, e.g. paste, otp, autotype
		fStr := strings.TrimPrefix(identifier, "field:")
		fidx, _ := strconv.Atoi(fStr)

		if s.Mode != "fields" {
			return
		}
		if s.SelectedEntry < 0 || s.SelectedEntry >= len(s.Entries) {
			return
		}
		pe := &s.Entries[s.SelectedEntry]
		if fidx < 0 || fidx >= len(pe.Fields) {
			return
		}

		keyname := pe.Fields[fidx]
		val := pe.Values[keyname]

		switch action {
		case ActionPaste:
			runPasteCommand(val)
		case ActionOTP:
			otpCode, err := generateOTPFromValue(val)
			if err != nil {
				slog.Error(Name, "otp_error", err)
				return
			}
			runPasteCommand(otpCode)
		case ActionAuto:
			// autotype username<TAB>password
			username, okU := pe.Values["username"]
			password, okP := pe.Values[PasswordLabel]
			if !okU || !okP {
				// nothing to do
				return
			}
			autotype := fmt.Sprintf("%s\t%s", username, password)
			runPasteCommand(autotype)
		default:
			// treat unknown action as paste
			runPasteCommand(val)
		}
		// After performing action, close or go back to stores (Elephant/Walker usually closes menu when action runs)
		// We'll reset session to stores to be safe:
		s.Mode = "stores"
		s.SelectedEntry = -1
		s.Entries = []parsedEntry{}
		return
	default:
		// unknown identifier
		return
	}
}

// -------------------- Helpers --------------------

// connKey returns a stable string key for the connection to store session state
func connKey(conn net.Conn) string {
	if conn == nil {
		return "local"
	}
	if addr := conn.RemoteAddr(); addr != nil {
		return addr.String()
	}
	return "local"
}

func getSession(key string) *sessionState {
	sessionsMu.Lock()
	defer sessionsMu.Unlock()
	if ss, ok := sessions[key]; ok {
		return ss
	}
	ss := &sessionState{
		Mode:         "stores",
		StoreIndex:   -1,
		Entries:      []parsedEntry{},
		SelectedEntry: -1,
	}
	sessions[key] = ss
	return ss
}

// buildEntriesForStore populates the given slice pointer with flattened pass entries found under rootPath.
// Each file with .gpg extension is a pass entry.
func buildEntriesForStore(dst *[]parsedEntry, rootPath string) {
	*dst = []parsedEntry{}

	rootPath = filepath.Clean(rootPath)

	err := filepath.WalkDir(rootPath, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			// ignore permission errors but log
			slog.Debug(Name, "walk_error", err, "path", path)
			return nil
		}
		if d.IsDir() {
			return nil
		}
		// typically pass uses .gpg extension
		if strings.HasSuffix(d.Name(), ".gpg") {
			rel, err := filepath.Rel(rootPath, path)
			if err != nil {
				rel = d.Name()
			}
			// remove .gpg
			rel = strings.TrimSuffix(rel, ".gpg")
			// flatten path separators to spaces to help fuzzy search
			entryPath := strings.ReplaceAll(rel, string(filepath.Separator), " ")
			pe := parsedEntry{
				EntryPath: entryPath,
				FilePath:  path,
				Fields:    []string{},
				Values:    map[string]string{},
			}
			*dst = append(*dst, pe)
		}
		return nil
	})
	if err != nil {
		slog.Error(Name, "walkdir", err)
	}
}

// decryptAndParseFile uses gpg CLI to decrypt the file and parse its contents into the parsedEntry struct
func decryptAndParseFile(pe *parsedEntry) error {
	// use gpg CLI to decrypt; this will use user's keyring / gpg-agent
	cmd := exec.Command("gpg", "--quiet", "--batch", "--yes", "--decrypt", pe.FilePath)
	out, err := cmd.Output()
	if err != nil {
		return fmt.Errorf("gpg decrypt failed: %w", err)
	}

	// parse content
	reader := bufio.NewReader(strings.NewReader(string(out)))
	lines := []string{}
	for {
		line, err := reader.ReadString('\n')
		if err != nil {
			if line != "" {
				lines = append(lines, strings.TrimRight(line, "\r\n"))
			}
			break
		}
		lines = append(lines, strings.TrimRight(line, "\r\n"))
	}

	if len(lines) == 0 {
		return fmt.Errorf("empty decrypted content for %s", pe.FilePath)
	}

	// first line = password
	pe.Fields = []string{}
	pe.Values = map[string]string{}

	pe.Fields = append(pe.Fields, PasswordLabel)
	pe.Values[PasswordLabel] = lines[0]

	// parse subsequent key: value or key:value
	for _, l := range lines[1:] {
		l = strings.TrimSpace(l)
		if l == "" {
			continue
		}
		// first try key: value
		if parts := strings.SplitN(l, ":", 2); len(parts) == 2 {
			key := strings.TrimSpace(parts[0])
			val := strings.TrimSpace(parts[1])
			if key == "" {
				continue
			}
			// normalize key to lowercase
			key = strings.ToLower(key)
			pe.Fields = append(pe.Fields, key)
			pe.Values[key] = val
			continue
		}
		// ignore other lines
	}

	return nil
}

func peIsParsed(pe *parsedEntry) bool {
	return len(pe.Fields) > 0 && len(pe.Values) > 0
}

// runPasteCommand replaces %CONTENT% in config.Command and executes it
func runPasteCommand(content string) {
	toRun := strings.ReplaceAll(config.Command, CommandToken, escapeForCommand(content))
	cmd := exec.Command("sh", "-c", toRun)
	if err := cmd.Start(); err != nil {
		slog.Error(Name, "run_command", err)
	} else {
		go func() {
			cmd.Wait()
		}()
	}
}

// naive escaping for content substitution -- users should configure wtype or a safer mechanism if needed
func escapeForCommand(s string) string {
	// wrap with single quotes and escape any single quotes
	escaped := strings.ReplaceAll(s, "'", `'\''`)
	return fmt.Sprintf("'%s'", escaped)
}

// determine key kind: otp_uri or plain
func keyKind(val string) string {
	if strings.HasPrefix(strings.ToLower(val), "otpauth://") {
		return "otp_uri"
	}
	return "plain"
}

// generateOTPFromValue accepts either a full otpauth:// URI or a secret directly (base32)
func generateOTPFromValue(val string) (string, error) {
	if strings.HasPrefix(strings.ToLower(val), "otpauth://") {
		// parse otpauth URI
		u, err := url.Parse(val)
		if err != nil {
			return "", err
		}
		// query params include secret, digits, period, algorithm
		q := u.Query()
		secret := q.Get("secret")
		algorithm := q.Get("algorithm")
		digitsStr := q.Get("digits")
		periodStr := q.Get("period")

		digits := 6
		if digitsStr != "" {
			if d, err := strconv.Atoi(digitsStr); err == nil {
				digits = d
			}
		}
		period := 30
		if periodStr != "" {
			if p, err := strconv.Atoi(periodStr); err == nil {
				period = p
			}
		}
		alg := strings.ToUpper(algorithm)
		if alg == "" {
			alg = "SHA1"
		}
		// only SHA1 implemented for now (as per defaults). Other algorithms would require branching.
		return totpCode(secret, digits, period)
	} else {
		// treat as secret (base32)
		return totpCode(val, 6, 30)
	}
}

// totpCode performs RFC6238 TOTP generation with SHA1
func totpCode(base32secret string, digits int, period int) (string, error) {
	// normalize secret (base32) -- allow without padding and in lower case
	normalized := strings.ToUpper(strings.ReplaceAll(base32secret, " ", ""))
	// add padding if necessary
	if m := len(normalized) % 8; m != 0 {
		normalized += strings.Repeat("=", 8-m)
	}
	secretBytes, err := base32.StdEncoding.DecodeString(normalized)
	if err != nil {
		// try raw base32 without padding
		raw := base32.NewEncoding("ABCDEFGHIJKLMNOPQRSTUVWXYZ234567").WithPadding(base32.NoPadding)
		secretBytes, err = raw.DecodeString(normalized)
		if err != nil {
			return "", fmt.Errorf("base32 decode failed: %w", err)
		}
	}

	// time counter
	counter := uint64(time.Now().Unix() / int64(period))
	var b [8]byte
	binary.BigEndian.PutUint64(b[:], counter)

	h := hmac.New(sha1.New, secretBytes)
	h.Write(b[:])
	hash := h.Sum(nil)
	offset := hash[len(hash)-1] & 0x0f
	truncated := binary.BigEndian.Uint32(hash[offset : offset+4])
	truncated &= 0x7fffffff
	mod := uint32(1)
	for i := 0; i < digits; i++ {
		mod *= 10
	}
	code := truncated % mod
	return fmt.Sprintf("%0*d", digits, code), nil
}

// calcScore helpers (use common.FuzzyScore)
func calcStoreScore(q string, s PassStore, exact bool) (int32, []int32, int32, bool) {
	var scoreRes int32
	var posRes []int32
	var startRes int32

	toSearch := []string{s.Name}
	toSearch = append(toSearch, s.Keywords...)
	toSearch = append(toSearch, s.Path)

	for _, v := range toSearch {
		score, pos, start := common.FuzzyScore(q, v, exact)
		if score > scoreRes {
			scoreRes = score
			posRes = pos
			startRes = start
		}
	}

	if scoreRes == 0 {
		return 0, nil, 0, false
	}
	scoreRes = max(scoreRes-startRes, 10)
	return scoreRes, posRes, startRes, true
}

func calcEntryScore(q string, e parsedEntry, exact bool) (int32, []int32, int32, bool) {
	// search on EntryPath
	score, pos, start := common.FuzzyScore(q, e.EntryPath, exact)
	if score == 0 {
		return 0, nil, 0, false
	}
	score = max(score-start, 10)
	return score, pos, start, true
}

func max(a, b int32) int32 {
	if a > b {
		return a
	}
	return b
}

// entriesRef is a convenience to get pointer reference for buildEntriesForStore when using session
func (s *sessionState) entriesRef(store PassStore) []parsedEntry {
	return s.Entries
}

