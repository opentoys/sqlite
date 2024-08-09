//go:build !riscv64 && !loong64
// +build !riscv64,!loong64

package mathutil

import (
	"math/big"
)

func (f *float) sqr() {
	f.n = new(big.Int).Mul(f.n, f.n) // github.com/remyoudompheng/bigfft.Mul
	f.fracBits *= 2
	f.normalize()
}
