// Copyright 2011 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package terminal

import (
	"bytes"
	"fmt"
	"io"
	"io/ioutil"
	"os"
	"path/filepath"
	"strings"
	"sync"
)

// EscapeCodes contains escape sequences that can be written to the terminal in
// order to achieve different styles of text.
type EscapeCodes struct {
	// Foreground colors
	Black, Red, Green, Yellow, Blue, Magenta, Cyan, White EscapeCode

	// Reset all attributes
	Reset EscapeCode
}

type EscapeCode []byte

var vt100EscapeCodes = EscapeCodes{
	Black:   EscapeCode{keyEscape, '[', '3', '0', 'm'},
	Red:     EscapeCode{keyEscape, '[', '3', '1', 'm'},
	Green:   EscapeCode{keyEscape, '[', '3', '2', 'm'},
	Yellow:  EscapeCode{keyEscape, '[', '3', '3', 'm'},
	Blue:    EscapeCode{keyEscape, '[', '3', '4', 'm'},
	Magenta: EscapeCode{keyEscape, '[', '3', '5', 'm'},
	Cyan:    EscapeCode{keyEscape, '[', '3', '6', 'm'},
	White:   EscapeCode{keyEscape, '[', '3', '7', 'm'},

	Reset: EscapeCode{keyEscape, '[', '0', 'm'},
}

// Terminal contains the state for running a VT100 terminal that is capable of
// reading lines of input.
type Terminal struct {
	// AutoCompleteCallback, if non-null, is called for each keypress
	// with the full input line and the current position of the cursor.
	// If it returns a nil newLine, the key press is processed normally.
	// Otherwise it returns a replacement line and the new cursor position.
	AutoCompleteCallback func(line []byte, pos, key int) (newLine []byte, newPos int)

	// Escape contains a pointer to the escape codes for this terminal.
	// It's always a valid pointer, although the escape codes themselves
	// may be empty if the terminal doesn't support them.
	Escape *EscapeCodes

	// By default, Terminal aims to emulate tab completion of file
	// paths. Setting DisableFileTablCompletion will prevent this.
	DisableFileTabCompletion bool

	// By default, Terminal aims to emulate tab completion of
	// executable files in the current $PATH. Setting
	// DisableExeTabCompletion will prevent this.
	DisableExeTabCompletion bool

	// By default, Terminal aims to emulate command history by
	// keeping a buffer of entered lines and handling the up
	// and down keys accordingly. Setting DisableHistory will
	// prevent this.
	DisableHistory bool

	// for resetting the terminal
	fds   [2]uintptr
	reset [2]*State

	// command history
	history        [][]byte
	currentHistory [][]byte
	currentIndex   int

	// tab completion
	cwd      string
	midTab   bool
	tabEnds  [][]byte
	tabToken []byte

	// lock protects the terminal and the state in this object from
	// concurrent processing of a key press and a Write() call.
	lock sync.Mutex

	c      io.ReadWriter
	prompt string

	// line is the current line being entered.
	line []byte
	// pos is the logical position of the cursor in line
	pos int
	// echo is true if local echo is enabled
	echo bool

	// cursorX contains the current X value of the cursor where the left
	// edge is 0. cursorY contains the row number where the first row of
	// the current line is 0.
	cursorX, cursorY int
	// maxLine is the greatest value of cursorY so far.
	maxLine int

	termWidth, termHeight int

	// outBuf contains the terminal data to be sent.
	outBuf []byte
	// remainder contains the remainder of any partial key sequences after
	// a read. It aliases into inBuf.
	remainder []byte
	inBuf     [256]byte
}

// NewTerminal runs a VT100 terminal on the given input and output.
// prompt is a string that is written at the start of each input line (i.e.
// "> ").
func NewTerminal(input, output *os.File, prompt string) (*Terminal, error) {
	var old [2]*State
	var err error
	if IsTerminal(int(input.Fd())) {
		old[0], err = MakeRaw(int(input.Fd()))
		if err != nil {
			return nil, err
		}
	}
	if IsTerminal(int(output.Fd())) {
		old[1], err = MakeRaw(int(output.Fd()))
		if err != nil {
			return nil, err
		}
	}
	width, height, err := GetSize(int(output.Fd()))
	if err != nil {
		return nil, err
	}
	cwd, err := os.Getwd()
	if err != nil {
		return nil, err
	}
	return &Terminal{
		Escape:     &vt100EscapeCodes,
		fds:        [2]uintptr{input.Fd(), output.Fd()},
		reset:      old,
		history:    make([][]byte, 0, 1),
		cwd:        cwd,
		c:          ReadWriter{input, output},
		prompt:     prompt,
		termWidth:  width,
		termHeight: height,
		echo:       true,
	}, nil
}

func (t *Terminal) Reset() error {
	if t.reset[0] != nil {
		if err := Restore(int(t.fds[0]), t.reset[0]); err != nil {
			return err
		}
	}
	if t.reset[1] != nil {
		if err := Restore(int(t.fds[1]), t.reset[1]); err != nil {
			return err
		}
	}
	return nil
}

const (
	keyCtrlD     = 4
	keyEnter     = '\r'
	keyEscape    = 27
	keyBackspace = 127
	keyUnknown   = 256 + iota
	keyUp
	keyDown
	keyLeft
	keyRight
	keyAltLeft
	keyAltRight
)

// bytesToKey tries to parse a key sequence from b. If successful, it returns
// the key and the remainder of the input. Otherwise it returns -1.
func bytesToKey(b []byte) (int, []byte) {
	if len(b) == 0 {
		return -1, nil
	}

	if b[0] != keyEscape {
		return int(b[0]), b[1:]
	}

	if len(b) >= 3 && b[0] == keyEscape && b[1] == '[' {
		switch b[2] {
		case 'A':
			return keyUp, b[3:]
		case 'B':
			return keyDown, b[3:]
		case 'C':
			return keyRight, b[3:]
		case 'D':
			return keyLeft, b[3:]
		}
	}

	if len(b) >= 6 && b[0] == keyEscape && b[1] == '[' && b[2] == '1' && b[3] == ';' && b[4] == '3' {
		switch b[5] {
		case 'C':
			return keyAltRight, b[6:]
		case 'D':
			return keyAltLeft, b[6:]
		}
	}

	// If we get here then we have a key that we don't recognise, or a
	// partial sequence. It's not clear how one should find the end of a
	// sequence without knowing them all, but it seems that [a-zA-Z] only
	// appears at the end of a sequence.
	for i, c := range b[0:] {
		if c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' {
			return keyUnknown, b[i+1:]
		}
	}

	return -1, b
}

// queue appends data to the end of t.outBuf
func (t *Terminal) queue(data []byte) {
	t.outBuf = append(t.outBuf, data...)
}

var eraseUnderCursor = []byte{' ', keyEscape, '[', 'D'}
var space = []byte{' '}

func isPrintable(key int) bool {
	return key >= 32 && key < 127
}

// moveCursorToPos appends data to t.outBuf which will move the cursor to the
// given, logical position in the text.
func (t *Terminal) moveCursorToPos(pos int) {
	if !t.echo {
		return
	}

	x := len(t.prompt) + pos
	y := x / t.termWidth
	x = x % t.termWidth

	up := 0
	if y < t.cursorY {
		up = t.cursorY - y
	}

	down := 0
	if y > t.cursorY {
		down = y - t.cursorY
	}

	left := 0
	if x < t.cursorX {
		left = t.cursorX - x
	}

	right := 0
	if x > t.cursorX {
		right = x - t.cursorX
	}

	t.cursorX = x
	t.cursorY = y
	t.move(up, down, left, right)
}

func (t *Terminal) move(up, down, left, right int) {
	movement := make([]byte, 3*(up+down+left+right))
	m := movement
	for i := 0; i < up; i++ {
		m[0] = keyEscape
		m[1] = '['
		m[2] = 'A'
		m = m[3:]
	}
	for i := 0; i < down; i++ {
		m[0] = keyEscape
		m[1] = '['
		m[2] = 'B'
		m = m[3:]
	}
	for i := 0; i < left; i++ {
		m[0] = keyEscape
		m[1] = '['
		m[2] = 'D'
		m = m[3:]
	}
	for i := 0; i < right; i++ {
		m[0] = keyEscape
		m[1] = '['
		m[2] = 'C'
		m = m[3:]
	}

	t.queue(movement)
}

func (t *Terminal) clearLineToRight() {
	op := []byte{keyEscape, '[', 'K'}
	t.queue(op)
}

func (t *Terminal) ClearLine() {
	op := []byte{keyEscape, '[', '2', 'K'}
	t.Write(op)
}

const maxLineLength = 4096

// handleKey processes the given key and, optionally, returns a line of text
// that the user has entered.
func (t *Terminal) handleKey(key int) (line string, ok bool) {
	switch key {
	case keyBackspace:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		if t.pos == 0 {
			return
		}
		t.pos--
		t.moveCursorToPos(t.pos)

		copy(t.line[t.pos:], t.line[1+t.pos:])
		t.line = t.line[:len(t.line)-1]
		if t.echo {
			t.writeLine(t.line[t.pos:])
		}
		t.queue(eraseUnderCursor)
		t.moveCursorToPos(t.pos)
	case keyAltLeft:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		// move left by a word.
		if t.pos == 0 {
			return
		}
		t.pos--
		for t.pos > 0 {
			if t.line[t.pos] != ' ' {
				break
			}
			t.pos--
		}
		for t.pos > 0 {
			if t.line[t.pos] == ' ' {
				t.pos++
				break
			}
			t.pos--
		}
		t.moveCursorToPos(t.pos)
	case keyAltRight:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		// move right by a word.
		for t.pos < len(t.line) {
			if t.line[t.pos] == ' ' {
				break
			}
			t.pos++
		}
		for t.pos < len(t.line) {
			if t.line[t.pos] != ' ' {
				break
			}
			t.pos++
		}
		t.moveCursorToPos(t.pos)
	case keyLeft:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		if t.pos == 0 {
			return
		}
		t.pos--
		t.moveCursorToPos(t.pos)
	case keyRight:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		if t.pos == len(t.line) {
			return
		}
		t.pos++
		t.moveCursorToPos(t.pos)
	case keyUp:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		if t.DisableHistory {
			t.handleAutoComplete(key)
			return
		}
		if !t.echo {
			return
		}
		if t.currentHistory != nil {
			if t.currentIndex == 0 {
				return
			}
			t.currentHistory[t.currentIndex] = t.line
			t.currentIndex--
			newLine := t.currentHistory[t.currentIndex]
			t.moveCursorToPos(0)
			t.writeLine(newLine)
			for i := len(newLine); i < len(t.line); i++ {
				t.writeLine(space)
			}
			t.pos = len(newLine)
			t.moveCursorToPos(t.pos)
			t.line = newLine
			return
		}
		t.currentHistory = make([][]byte, len(t.history)+1)
		for i := range t.history {
			t.currentHistory[i] = make([]byte, len(t.history[i]))
			for j := range t.currentHistory[i] {
				t.currentHistory[i][j] = t.history[i][j]
			}
		}
		t.currentHistory[len(t.history)] = []byte{}
		t.currentIndex = len(t.history) - 1
		newLine := t.currentHistory[t.currentIndex]
		t.moveCursorToPos(0)
		t.writeLine(newLine)
		for i := len(newLine); i < len(t.line); i++ {
			t.writeLine(space)
		}
		t.pos = len(newLine)
		t.moveCursorToPos(t.pos)
		t.line = newLine
		return
	case keyDown:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		if t.DisableHistory {
			t.handleAutoComplete(key)
			return
		}
		if !t.echo || t.currentHistory == nil || t.currentIndex == len(t.currentHistory)-1 {
			return
		}
		t.currentHistory[t.currentIndex] = t.line
		t.currentIndex++
		newLine := t.currentHistory[t.currentIndex]
		t.moveCursorToPos(0)
		t.writeLine(newLine)
		for i := len(newLine); i < len(t.line); i++ {
			t.writeLine(space)
		}
		t.pos = len(newLine)
		t.moveCursorToPos(t.pos)
		t.line = newLine
		return
	case keyEnter:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		t.moveCursorToPos(len(t.line))
		t.queue([]byte("\r\n"))
		line = string(t.line)
		ok = true
		t.line = t.line[:0]
		t.pos = 0
		t.cursorX = 0
		t.cursorY = 0
		t.maxLine = 0
		t.currentIndex = 0
		t.currentHistory = nil
	case '\t':
		if t.DisableExeTabCompletion && t.DisableFileTabCompletion {
			if t.midTab {
				t.midTab = false
				t.tabEnds = nil
				t.tabToken = nil
			}
			t.handleAutoComplete(key)
			return
		}
		if t.midTab {
			buf := new(bytes.Buffer)
			buf.WriteString("\r\n")
			for _, end := range t.tabEnds {
				buf.Write(t.tabToken)
				buf.Write(end)
				buf.WriteString("\r\n")
			}
			buf.WriteString(t.prompt)
			buf.Write(t.line)
			t.queue(buf.Bytes())
			return
		}
		// find the last full word.
		if t.pos == 0 {
			return
		}
		i := t.pos - 1
		for i > 0 {
			if t.line[i] == ' ' {
				break
			}
			i--
		}
		if i == t.pos {
			return
		}
		token := t.line[i:t.pos]
		if token[0] == ' ' {
			token = token[1:]
		}
		// try local files first.
		if !t.DisableFileTabCompletion {
			ends := t.findFiles(token)
			switch len(ends) {
			case 0:
			case 1:
				if len(t.line)+len(ends[0]) == maxLineLength {
					return
				}
				newLine := make([]byte, 0, len(t.line)+len(ends[0]))
				newLine = append(newLine, t.line[:t.pos]...)
				newLine = append(newLine, ends[0]...)
				newLine = append(newLine, t.line[t.pos:]...)
				t.line = newLine
				if t.echo {
					t.writeLine(t.line[t.pos:])
				}
				t.pos += len(ends[0])
				t.moveCursorToPos(t.pos)
				return
			default:
				prefix := longestCommonPrefix(ends)
				if prefix > 0 {
					newLine := make([]byte, 0, len(t.line)+prefix)
					newLine = append(newLine, t.line[:t.pos]...)
					newLine = append(newLine, ends[0][:prefix]...)
					newLine = append(newLine, t.line[t.pos:]...)
					t.line = newLine
					if t.echo {
						t.writeLine(t.line[t.pos:])
					}
					t.pos += prefix
					t.moveCursorToPos(t.pos)
				}
				t.midTab = true
				t.tabEnds = ends
				t.tabToken = token
				return
			}
		}
		// then try path executables.
		if !t.DisableExeTabCompletion {
			ends := t.findExes(token)
			switch len(ends) {
			case 0:
			case 1:
				if len(t.line)+len(ends[0]) == maxLineLength {
					return
				}
				newLine := make([]byte, 0, len(t.line)+len(ends[0]))
				newLine = append(newLine, t.line[:t.pos]...)
				newLine = append(newLine, ends[0]...)
				newLine = append(newLine, t.line[t.pos:]...)
				t.line = newLine
				if t.echo {
					t.writeLine(t.line[t.pos:])
				}
				t.pos += len(ends[0])
				t.moveCursorToPos(t.pos)
			default:
				prefix := longestCommonPrefix(ends)
				if prefix > 0 {
					newLine := make([]byte, 0, len(t.line)+prefix)
					newLine = append(newLine, t.line[:t.pos]...)
					newLine = append(newLine, ends[0][:prefix]...)
					newLine = append(newLine, t.line[t.pos:]...)
					t.line = newLine
					if t.echo {
						t.writeLine(t.line[t.pos:])
					}
					t.pos += prefix
					t.moveCursorToPos(t.pos)
				}
				t.midTab = true
				t.tabEnds = ends
				t.tabToken = token
			}
		}
		return

	default:
		if t.midTab {
			t.midTab = false
			t.tabEnds = nil
			t.tabToken = nil
		}
		if t.handleAutoComplete(key) {
			return
		}
		if !isPrintable(key) {
			return
		}
		if len(t.line) == maxLineLength {
			return
		}
		if len(t.line) == cap(t.line) {
			newLine := make([]byte, len(t.line), 2*(1+len(t.line)))
			copy(newLine, t.line)
			t.line = newLine
		}
		t.line = t.line[:len(t.line)+1]
		copy(t.line[t.pos+1:], t.line[t.pos:])
		t.line[t.pos] = byte(key)
		if t.echo {
			t.writeLine(t.line[t.pos:])
		}
		t.pos++
		t.moveCursorToPos(t.pos)
	}
	return
}

func (t *Terminal) handleAutoComplete(key int) bool {
	if t.AutoCompleteCallback != nil {
		t.lock.Unlock()
		newLine, newPos := t.AutoCompleteCallback(t.line, t.pos, key)
		t.lock.Lock()

		if newLine != nil {
			if t.echo {
				t.moveCursorToPos(0)
				t.writeLine(newLine)
				for i := len(newLine); i < len(t.line); i++ {
					t.writeLine(space)
				}
				t.moveCursorToPos(newPos)
			}
			t.line = newLine
			t.pos = newPos
			return true
		}
	}
	return false
}

func (t *Terminal) findFiles(token []byte) [][]byte {
	out := make([][]byte, 0, 1)
	start := filepath.Join(t.cwd, string(token))
	dir := filepath.Dir(start)
	name := filepath.Base(start)
	files, err := ioutil.ReadDir(dir)
	if err != nil {
		return out
	}
	for _, file := range files {
		if strings.HasPrefix(file.Name(), name) {
			out = append(out, []byte(file.Name()[len(name):]))
		}
	}
	return out
}

func (t *Terminal) findExes(token []byte) [][]byte {
	out := make([][]byte, 0, 1)
	name := filepath.Base(string(token))
	path := os.Getenv("PATH")
	if len(path) == 0 {
		return out
	}
	pathdirs := filepath.SplitList(path)
	for _, dir := range pathdirs {
		files, err := ioutil.ReadDir(dir)
		if err != nil {
			continue
		}
		for _, file := range files {
			if file.Mode().Perm()&001 == 0 { // make sure executable
				continue
			}
			if strings.HasPrefix(file.Name(), name) {
				end := []byte(file.Name()[len(name):])
				dup := false
				for _, other := range out {
					if bytes.Equal(end, other) {
						dup = true
						break
					}
				}
				if !dup {
					out = append(out, end)
				}
			}
		}
	}
	return out
}

func longestCommonPrefix(lines [][]byte) int {
	switch len(lines) {
	case 0:
		return 0
	case 1:
		return len(lines[0])
	}
	prefix := lines[0]
	length := len(prefix)
	for i := 1; i < len(lines); i++ {
		line := lines[i]
		for j := range prefix {
			if line[j] != prefix[j] {
				length = j
				if length <= 0 {
					return 0
				}
				prefix = prefix[:length]
				break
			}
		}
	}
	return length
}

func (t *Terminal) writeLine(line []byte) {
	for len(line) != 0 {
		remainingOnLine := t.termWidth - t.cursorX
		todo := len(line)
		if todo > remainingOnLine {
			todo = remainingOnLine
		}
		t.queue(line[:todo])
		t.cursorX += todo
		line = line[todo:]

		if t.cursorX == t.termWidth {
			t.cursorX = 0
			t.cursorY++
			if t.cursorY > t.maxLine {
				t.maxLine = t.cursorY
			}
		}
	}
}

func (t *Terminal) Write(buf []byte) (n int, err error) {
	t.lock.Lock()
	defer t.lock.Unlock()

	if t.cursorX == 0 && t.cursorY == 0 {
		// This is the easy case: there's nothing on the screen that we
		// have to move out of the way.
		return t.c.Write(buf)
	}

	// We have a prompt and possibly user input on the screen. We
	// have to clear it first.
	t.move(0 /* up */, 0 /* down */, t.cursorX /* left */, 0 /* right */)
	t.cursorX = 0
	t.clearLineToRight()

	for t.cursorY > 0 {
		t.move(1 /* up */, 0, 0, 0)
		t.cursorY--
		t.clearLineToRight()
	}

	if _, err = t.c.Write(t.outBuf); err != nil {
		return
	}
	t.outBuf = t.outBuf[:0]

	if n, err = t.c.Write(buf); err != nil {
		return
	}

	t.queue([]byte(t.prompt))
	chars := len(t.prompt)
	if t.echo {
		t.queue(t.line)
		chars += len(t.line)
	}
	t.cursorX = chars % t.termWidth
	t.cursorY = chars / t.termWidth
	t.moveCursorToPos(t.pos)

	if _, err = t.c.Write(t.outBuf); err != nil {
		return
	}
	t.outBuf = t.outBuf[:0]
	return
}

// Print formats using the default formats for its operands
// and writes to the terminal's output. Spaces are added
// between operands when neither is a string. It returns the
// number of bytes written and any write error encountered.
func (t *Terminal) Print(a ...interface{}) (int, error) {
	return fmt.Fprint(t, a...)
}

// Printf formats according to a format specifier and writes
// to the terminal's output. It returns the number of bytes
// written and any write error encountered.
func (t *Terminal) Printf(format string, a ...interface{}) (int, error) {
	return fmt.Fprintf(t, format, a...)
}

// Println formats using the default formats for its operands
// and writes to the terminal's output. Spaces are always
// added between operands and a newline is appended. It returns
// the number of bytes written and any write error encountered.
func (t *Terminal) Println(a ...interface{}) (int, error) {
	return fmt.Fprintln(t, a...)
}

// SetColour sets the terminal output to the given colour, if
// this is supported by the terminal.
func (t *Terminal) SetColour(colour EscapeCode) error {
	_, err := t.Write([]byte(colour))
	return err
}

// ResetColour uses the Reset EscapeCode to reset the output
// colour, if this is supported by the terminal.
func (t *Terminal) ResetColour() error {
	_, err := t.Write([]byte(t.Escape.Reset))
	return err
}

// ReadPassword temporarily changes the prompt and reads a password, without
// echo, from the terminal.
func (t *Terminal) ReadPassword(prompt string) (line string, err error) {
	t.lock.Lock()
	defer t.lock.Unlock()

	oldPrompt := t.prompt
	t.prompt = prompt
	t.echo = false

	line, err = t.readLine()

	t.prompt = oldPrompt
	t.echo = true

	return
}

// ReadLine returns a line of input from the terminal.
func (t *Terminal) ReadLine() (line string, err error) {
	t.lock.Lock()
	defer t.lock.Unlock()

	line, err = t.readLine()
	if err != nil {
		return "", err
	}
	t.history = append(t.history, []byte(line))
	return line, nil
}

func (t *Terminal) readLine() (line string, err error) {
	// t.lock must be held at this point

	if t.cursorX == 0 && t.cursorY == 0 {
		t.writeLine([]byte(t.prompt))
		t.c.Write(t.outBuf)
		t.outBuf = t.outBuf[:0]
	}

	for {
		rest := t.remainder
		lineOk := false
		for !lineOk {
			var key int
			key, rest = bytesToKey(rest)
			if key < 0 {
				break
			}
			if key == keyCtrlD {
				return "", io.EOF
			}
			line, lineOk = t.handleKey(key)
		}
		if len(rest) > 0 {
			n := copy(t.inBuf[:], rest)
			t.remainder = t.inBuf[:n]
		} else {
			t.remainder = nil
		}
		t.c.Write(t.outBuf)
		t.outBuf = t.outBuf[:0]
		if lineOk {
			return
		}

		// t.remainder is a slice at the beginning of t.inBuf
		// containing a partial key sequence
		readBuf := t.inBuf[len(t.remainder):]
		var n int

		t.lock.Unlock()
		n, err = t.c.Read(readBuf)
		t.lock.Lock()

		if err != nil {
			return
		}

		t.remainder = t.inBuf[:n+len(t.remainder)]
	}
	panic("unreachable")
}

// SetPrompt sets the prompt to be used when reading subsequent lines.
func (t *Terminal) SetPrompt(prompt string) {
	t.lock.Lock()
	defer t.lock.Unlock()

	t.prompt = prompt
}

func (t *Terminal) GetSize() (width, height int) {
	t.lock.Lock()
	defer t.lock.Unlock()

	return t.termWidth, t.termHeight
}

func (t *Terminal) SetSize(width, height int) {
	t.lock.Lock()
	defer t.lock.Unlock()

	t.termWidth, t.termHeight = width, height
}
