// Copyright (c) 2014 The fileutil Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !arm && !arm64
// +build !arm,!arm64

package fileutil // import "github.com/opentoys/sqlite/fileutil"

import (
	"io"
	"os"
)

const hasPunchHole = false

// PunchHole deallocates space inside a file in the byte range starting at
// offset and continuing for len bytes. Similar to FreeBSD, this is
// unimplemented.
func PunchHole(f *os.File, off, len int64) error {
	return nil
}

// Unimplemented on NetBSD.
func Fadvise(f *os.File, off, len int64, advice FadviseAdvice) error {
	return nil
}

// IsEOF reports whether err is an EOF condition.
func IsEOF(err error) bool { return err == io.EOF }
