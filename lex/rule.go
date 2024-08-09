// Copyright (c) 2014 The lex Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package lex // import "modernc.org/lex"

import (
	"bytes"
	"errors"
	"fmt"
	"go/token"
	"regexp"
	"strconv"
	"unicode"
	"unicode/utf8"
)

var (
	nameFirst = &unicode.RangeTable{R16: []unicode.Range16{{'A', 'Z', 1}, {'_', '_', 1}, {'a', 'z', 1}}}
	nameNext  = &unicode.RangeTable{R16: []unicode.Range16{{'-', '-', 1}, {'0', '9', 1}, {'A', 'Z', 1}, {'_', '_', 1}, {'a', 'z', 1}}}
)

func cased(vars *vars, r rune) string {
	switch {
	case vars.caseless:
		switch {
		case r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z':
			return fmt.Sprintf("(%c|%c)", r, r^' ')
		default:
			return fmt.Sprintf("%c", r)
		}
	default:
		return fmt.Sprintf("%c", r)
	}
}

func parsePattern(vars *vars, pos token.Position, src string, stack map[string]bool) (pattern, re, action string, bol, eol bool) {
	p := &pat{src: src, re: bytes.NewBuffer(nil), stack: stack}

	defer func() {
		if e := recover(); e != nil {
			pos.Column += p.pos
			logErr(vars, fmt.Sprintf(`%s - "%s^%s" - %s`, pos, src[:p.pos], src[p.pos:], e.(error)))
		}
	}()

	p.parseExpr(vars, 0)
	pattern, re = src[:p.pos], p.re.String()
	bol, eol = p.bol, p.eol
	switch b := p.current(vars); b {
	case 0:
		return
	case ' ', '\t':
		p.move(vars)
		action = src[p.pos:]
		return
	}
	panic(errors.New("syntax error"))
}

type pat struct {
	src      string
	pos      int
	delta    int
	re       *bytes.Buffer
	stack    map[string]bool
	bol, eol bool
}

func (p *pat) current(vars *vars) (y rune) {
	if i := p.pos; i < len(p.src) {
		if !vars.bits32 {
			return rune(p.src[i])
		}

		y, p.delta = utf8.DecodeRuneInString(p.src[i:])
		return
	}

	return 0
}

func (p *pat) eof(vars *vars, whiteIsEof bool) bool {
	b := p.current(vars)
	return b == 0 || whiteIsEof && (b == ' ' || b == '\t')
}

func (p *pat) move(vars *vars) {
	if p.pos < len(p.src) {
		if !vars.bits32 {
			p.pos++
		} else {
			p.pos += p.delta
		}
	}
}

func (p *pat) accept(vars *vars, b rune) bool {
	if b == p.current(vars) {
		p.move(vars)
		return true
	}

	return false
}

func (p *pat) parseExpr(vars *vars, nest int) {
	ok := false
	for !p.eof(vars, true) {
		p.parseAlt(vars, nest)
		ok = true
		if !p.accept(vars, '|') {
			break
		}

		p.re.WriteRune('|')
	}
	if ok {
		return
	}

	panic(errors.New(`expected "alernative"`))
}

func (p *pat) parseAlt(vars *vars, nest int) {
	ok := false
	for p.current(vars) != 0 {
		if !p.parseTerm(vars, nest) {
			break
		}

		ok = true
	}
	if ok {
		return
	}

	panic(errors.New(`expected "term"`))
}

func (p *pat) parseTerm(vars *vars, nest int) (ok bool) {
	ok = true
	switch b := p.current(vars); b {
	default:
		p.re.WriteString(cased(vars, b))
		p.move(vars)
	case '$':
		p.move(vars)
		if p.pos != len(p.src) && p.current(vars) != ' ' && p.current(vars) != '\t' { // not an assertion
			p.re.WriteString(`\$`)
		} else {
			p.re.WriteString(`(\n|\x00)`)
			p.eol = true
		}
	case '^':
		p.move(vars)
		if p.pos != 1 { // not an assertion
			p.re.WriteString(`\^`)
		} else {
			p.bol = true
		}
	case '/':
		panic(errors.New("trailing context not supported"))
	case '.':
		p.move(vars)
		if !vars.bits32 {
			p.re.WriteString("[\x01-\x09\x0b-\u00ff]")
		} else {
			p.re.WriteString("[\x01-\x09\x0b-\U0010ffff]")
		}
	case '+', '*', '?':
		panic(fmt.Errorf("unexpected metachar %q", string(b)))
	case '\\':
		switch b := p.mustParseChar(vars, false); b {
		default:
			p.re.WriteString(regexp.QuoteMeta(string(b)))
		case 0:
			p.re.WriteString("\\x00")
		}
	case 0, '|', ' ', '\t':
		return false
	case ')':
		if nest == 0 {
			panic(errors.New(`unexpected ")"`))
		}
		return false
	case '(':
		p.re.WriteRune(b)
		p.move(vars)
		p.parseExpr(vars, nest+1)
		p.expect(vars, ')')
		p.re.WriteRune(')')
	case '[':
		p.re.WriteRune(b)
		p.move(vars)
		if p.accept(vars, '^') {
			p.re.WriteString("^\\x00-\\x00")
		}
	loop:
		for {
			a := p.mustParseChar(vars, false)
			p.re.WriteString(regexp.QuoteMeta(string(a)))
			switch p.current(vars) {
			case '\\':
				switch c := p.mustParseChar(vars, false); c {
				case '-':
					p.re.WriteString(`\-`)
				default:
					p.re.WriteString(regexp.QuoteMeta(string(c)))
				}
			default:
				if p.accept(vars, '-') {
					p.re.WriteRune('-')
					if p.current(vars) == ']' {
						p.move(vars)
						break loop
					}

					b := p.mustParseChar(vars, false)
					if b < a {
						panic(fmt.Errorf(`invalid range bounds ordering in bracket expression "%s-%s"`, string(a), string(b)))
					}
					p.re.WriteString(regexp.QuoteMeta(string(b)))
				}
			}
			if p.accept(vars, ']') {
				break
			}
		}
		p.re.WriteRune(']')
	case '{':
		p.move(vars)
		if !unicode.Is(nameFirst, p.current(vars)) {
			p.re.WriteRune('{')
			break
		}

		name := ""
		for {
			b := p.current(vars)
			if !unicode.Is(nameNext, b) {
				break
			}
			p.move(vars)
			name += string(b)
		}
		p.expect(vars, '}')
		if _, ok := vars.defs[name]; !ok {
			panic(fmt.Errorf("%q undefined", name))
		}

		if re, ok := vars.defRE[name]; ok {
			p.re.WriteString(re)
			break
		}

		if p.stack[name] {
			panic(fmt.Errorf("recursive definition %q", name))
		}

		p.stack[name] = true
		//TODO support assertions in definitions also?
		_, re, _, _, _ := parsePattern(vars, vars.defPos[name], vars.defs[name], p.stack)
		re = "(" + re + ")"
		vars.defRE[name] = re
		p.re.WriteString(re)
	case '"':
		p.move(vars)
		lit := ""
	outer:
		for {
			switch b := p.current(vars); b {
			default:
				lit += cased(vars, b)
				p.move(vars)
			case 0, '\n', '\r':
				panic(fmt.Errorf("unterminated quoted pattern"))
			case '\\':
				p.move(vars)
				if p.current(vars) == '"' {
					p.move(vars)
					lit += "\""
				} else {
					lit += "\\"
				}
			case '"':
				p.move(vars)
				break outer
			}
		}
		lit = "(" + regexp.QuoteMeta(lit) + ")"
		p.re.WriteString(lit)
	}

	// postfix ops
	switch b := p.current(vars); b {
	case '+', '*', '?':
		p.re.WriteRune(b)
		p.move(vars)
	}

	return
}

func (p *pat) mustParseChar(vars *vars, whiteIsEof bool) (b rune) {
	if p.eof(vars, whiteIsEof) {
		panic(fmt.Errorf("unexpected regexp end"))
	}

	b = p.parseChar(vars)
	p.move(vars)
	return
}

func (p *pat) parseChar(vars *vars) (b rune) {
	if b = p.current(vars); b != '\\' {
		return
	}

	p.move(vars)
	switch b = p.current(vars); b {
	default:
		return
	case 'a':
		return '\a'
	case 'b':
		return '\b'
	case 'f':
		return '\f'
	case 'n':
		return '\n'
	case 'r':
		return '\r'
	case 't':
		return '\t'
	case 'v':
		return '\v'
	case 'x':
		s := ""
		for i := 0; i < 2; i++ {
			if p.eof(vars, true) {
				panic(errors.New("unexpected regexp end"))
			}
			p.move(vars)
			s += string(p.current(vars))
		}
		n, err := strconv.ParseUint(s, 16, 64)
		if err != nil {
			panic(err)
		}

		return rune(n)
	case 'u':
		s := ""
		for i := 0; i < 4; i++ {
			if p.eof(vars, true) {
				panic(errors.New("unexpected regexp end"))
			}
			p.move(vars)
			s += string(p.current(vars))
		}
		n, err := strconv.ParseUint(s, 16, 64)
		if err != nil {
			panic(err)
		}

		return rune(n)
	case 'U':
		s := ""
		for i := 0; i < 8; i++ {
			if p.eof(vars, true) {
				panic(errors.New("unexpected regexp end"))
			}
			p.move(vars)
			s += string(p.current(vars))
		}
		n, err := strconv.ParseUint(s, 16, 64)
		if err != nil {
			panic(err)
		}

		return rune(n)
	case '0', '1', '2', '3', '4', '5', '6', '7':
		s := ""
		for b = p.current(vars); (len(s) < 3 || vars.bits32 && len(s) < 7) && b >= '0' && b <= '7'; b = p.current(vars) {
			s += string(b)
			p.move(vars)
		}
		n, err := strconv.ParseUint(s, 8, 64)
		if err != nil {
			panic(err)
		}

		if !vars.bits32 && n > 255 {
			panic(fmt.Errorf("octal literal %s out of byte range", s))
		}

		p.pos--
		return rune(n)
	}
}

func (p *pat) expect(vars *vars, b rune) {
	if !p.accept(vars, b) {
		panic(fmt.Errorf("expected %q, got %q", string(b), string(p.current(vars))))
	}
}

func moreAction(vars *vars, s string) {
	n := len(vars.rules) - 1
	vars.rules[n].action += "\n" + s
}

func addStartSet(vars *vars, s string) bool {
	if _, ok := vars.defStarts[s]; ok {
		return false
	}

	vars.iStarts[s] = len(vars.iStarts)
	vars.defStarts[s], vars.unrefStarts[s] = true, true
	return true
}
