// Copyright 2023 The Scanner Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package scanner provides some common scanner stuff.
package scanner // modernc.org/scanner

import (
	"fmt"
	"go/token"
	"strings"

	mtoken "github.com/opentoys/sqlite/token"
)

var (
	_ error = ErrWithPosition{}
	_ error = ErrList{}
)

// ErrWithPosition augments an error with optional position information.
type ErrWithPosition struct {
	Pos token.Position
	Err error
}

// Error implements error.
func (e ErrWithPosition) Error() string {
	switch {
	case e.Pos.IsValid():
		return fmt.Sprintf("%v: %v", e.Pos, e.Err)
	default:
		return fmt.Sprintf("%v", e.Err)
	}
}

// ErrList is a list of errors.
type ErrList []ErrWithPosition

// Err returns e if len(e) != 0 or nil.
func (e ErrList) Err() (r error) {
	if len(e) == 0 {
		return nil
	}

	return e
}

// Error implements error.
func (e ErrList) Error() string {
	w := 0
	prev := ErrWithPosition{Pos: token.Position{Offset: -1}}
	for _, v := range e {
		if v.Pos.Line == 0 || v.Pos.Offset != prev.Pos.Offset || v.Err.Error() != prev.Err.Error() {
			e[w] = v
			w++
			prev = v
		}
	}

	var a []string
	for _, v := range e[:w] {
		a = append(a, fmt.Sprint(v))
	}
	return strings.Join(a, "\n")
}

// AddErr adds an error message associated with an optional position.
func (e *ErrList) AddErr(pos token.Position, msg string, args ...interface{}) {
	switch {
	case len(args) == 0:
		*e = append(*e, ErrWithPosition{pos, fmt.Errorf("%s", msg)})
	default:
		*e = append(*e, ErrWithPosition{pos, fmt.Errorf(msg, args...)})
	}
}

type tok struct { // 12 bytes
	ch  rune
	sep int32
	src int32
}

// source represents a single source file, editor text buffer etc.
type source struct {
	buf        []byte
	file       *mtoken.File
	name       string
	sepPatches map[int32]string
	srcPatches map[int32]string
	toks       []tok

	off int
}

// 'buf' becomes owned by the result and must not be modified afterwards.
func newSource(name string, buf []byte) *source {
	file := mtoken.NewFile(name, len(buf))
	return &source{
		buf:  buf,
		file: file,
		name: name,
	}
}

// ScanSep is a function used by Scanner to determine the length in bytes of
// any separator preceding a token or EOF.
//
// If the buf contains "if foo()" and the current offset is 2, calling
//
//	ScanSep()
//
// may return
//
//	1
//
// to indicate the separator is " ".
//
// Scanner increments its own kept buffer offset by the returned length, the
// ScanSep function is assumed to do the same.
type ScanSep func() int

// ScanSrc is a function used by Scanner to determine the length in bytes of a token.
//
// If the buf contains "if foo()" and the current offset is 3, calling
//
//	ScanSrc()
//
// may return
//
//	(3, IDENT)
//
// to indicate the token is "foo" and its semantic value is IDENT.
//
// Once ScanSrc returns zero for the token length an EOF is assumed.
//
// Scanner increments its own kept buffer offset by the returned length, the
// ScanSrc function is assumed to do the same.
type ScanSrc func() (int, rune)

// Scanner represents the data structures and methods common to some/many
// lexical scanners.
type Scanner struct {
	*source
	errs    ErrList
	scanSep ScanSep
	scanSrc ScanSrc

	errBudget int

	isClosed bool
}

// NewScanner returns a newly created Scanner. The 'name' argument is used to
// report positions. 'buf' becomes owned by the scanner and should not be
// mutated by the caller afterwards.
func NewScanner(name string, buf []byte, scanSep ScanSep, scanSrc ScanSrc) *Scanner {
	r := &Scanner{
		errBudget: 10,
		scanSep:   scanSep,
		scanSrc:   scanSrc,
		source:    newSource(name, buf),
	}
	return r
}

// AddErr registers an error.
func (s *Scanner) AddErr(pos token.Position, msg string, args ...interface{}) {
	switch {
	case s.errBudget > 0:
		s.errs.AddErr(pos, msg, args...)
	case s.errBudget == 0:
		s.errs.AddErr(token.Position{}, "too many errors")
	}
	s.errBudget--
}

// Position returns the position determined by offset.
func (s *Scanner) Position(offset int) (r token.Position) {
	return token.Position(s.file.PositionFor(mtoken.Pos(offset+s.file.Base()), true))
}

// Err reports any errors from reported by AddErr()
func (s *Scanner) Err() error { return s.errs.Err() }

// AddLine adds the line offset for a new line.  The line offset must be larger
// than the offset for the previous line and smaller than the scanner buffer
// size; otherwise the line offset is ignored.
func (s *Scanner) AddLine(offset int) { s.file.AddLine(offset + s.file.Base()) }

// AddLineColumnInfo adds alternative file, line, and column number information
// for a given scanner buffer offset. The offset must be larger than the offset
// for the previously added alternative line info and smaller than the scanner
// buffer size; otherwise the information is ignored.
//
// AddLineColumnInfo is typically used to register alternative position
// information for line directives such as //line filename:line:column.
func (s *Scanner) AddLineColumnInfo(offset int, filename string, line, column int) {
	s.file.AddLineColumnInfo(offset, filename, line, column)
}

// Scan returns the next token.
func (s *Scanner) Scan() Token {
	var t tok
	x := int32(len(s.toks))
	switch {
	case !s.isClosed:
		off := s.off
		sep := s.scanSep()
		s.off += sep
		src, ch := s.scanSrc()
		t = tok{ch: ch, sep: int32(off), src: int32(s.off)}
		s.off += src
		s.toks = append(s.toks, t)
		if src == 0 {
			s.isClosed = true
		}
	default:
		x--
		t = s.toks[x]
	}
	return Token{
		Ch:     t.ch,
		index:  x,
		source: s.source,
	}
}

// Token represents a lexeme, its position and semantic value.
type Token struct { // 16 bytes on 64 bit arch
	// Ch represents the semantic value of the token as determined by the Scan
	// function.
	Ch     rune
	index  int32
	source *source
}

// Position reports the position of t.
func (t Token) Position() (r token.Position) {
	s := t.source
	if s == nil {
		return r
	}

	return token.Position(s.file.PositionFor(mtoken.Pos(s.toks[t.index].src+int32(s.file.Base())), true))
}

// Prev returns the token preceding t or a zero value if no such token exists.
func (t Token) Prev() (r Token) {
	s := t.source
	if s == nil {
		return r
	}

	if index := t.index - 1; index >= 0 {
		return Token{source: s, Ch: s.toks[index].ch, index: index}
	}

	return r
}

// Next returns the token following t or a zero value if no such token exists.
func (t Token) Next() (r Token) {
	s := t.source
	if s == nil {
		return r
	}

	if index := t.index + 1; index < int32(len(t.source.toks)) {
		return Token{source: s, Ch: s.toks[index].ch, index: index}
	}

	return r
}

// Sep returns the separator preceding t.
func (t Token) Sep() string {
	s := t.source
	if s == nil {
		return ""
	}

	if p, ok := s.sepPatches[t.index]; ok {
		return p
	}

	return string(s.buf[s.toks[t.index].sep:s.toks[t.index].src])
}

// SetSep sets t's separator.
func (t Token) SetSep(s string) {
	src := t.source
	if src == nil {
		return
	}

	if src.sepPatches == nil {
		src.sepPatches = map[int32]string{}
	}
	src.sepPatches[t.index] = s
}

// Src returns t's source form, without its preceding separator.
func (t Token) Src() string {
	s := t.source
	if s == nil {
		return ""
	}

	if p, ok := s.srcPatches[t.index]; ok {
		return p
	}

	tok := s.toks[t.index]
	if int(tok.src) >= len(s.buf) {
		return ""
	}

	if int(t.index+1) < len(s.toks) {
		return string(s.buf[tok.src:s.toks[t.index+1].sep])
	}

	return string(s.buf[tok.src:s.off])
}

// SetSrc sets t's source form.
func (t Token) SetSrc(s string) {
	src := t.source
	if src == nil {
		return
	}

	if src.srcPatches == nil {
		src.srcPatches = map[int32]string{}
	}
	src.srcPatches[t.index] = s
}

// IsValid reports whether t is a valid token. Zero values of Token report
// false.
func (t Token) IsValid() bool { return t.source != nil }

// String implements fmt.Stringer.
func (t Token) String() string {
	return fmt.Sprintf("%v: %q %q %#U", t.Position(), t.Sep(), t.Src(), t.Ch)
}
