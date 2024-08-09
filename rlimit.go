// Copyright 2021 The Sqlite Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build freebsd
// +build freebsd

package sqlite // import "github.com/opentoys/sqlite"

import (
	"github.com/opentoys/sqlite/pkg/unix"
)

func setMaxOpenFiles(n int64) error {
	var rLimit unix.Rlimit
	rLimit.Max = n
	rLimit.Cur = n
	return unix.Setrlimit(unix.RLIMIT_NOFILE, &rLimit)
}
