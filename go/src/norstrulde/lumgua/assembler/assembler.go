package assembler

import (
	. "norstrulde/lumgua/machine"
)

type Prog interface {
	size() int
	flatten([]asm) []asm
}

type block struct {
	progs []Prog
}

type asm interface {
	Prog
	asmVariant()
}

type Label struct {
	// Pointer identity is all that matters. The struct MUST NOT be empty.
	bool
}

type asmInstr struct {
	instr Instr
	label *Label // May be nil.
}

func (*Label) asmVariant() {}
func (*asmInstr) asmVariant() {}

func (*Label) size() int {
	return 1
}

func (*asmInstr) size() int {
	return 1
}

func (b *block) size() int {
	s := 0
	for _, sub := range b.progs {
		s += sub.size()
	}
	return s
}

func (label *Label) flatten(code []asm) []asm {
	return append(code, label)
}

func (instr *asmInstr) flatten(code []asm) []asm {
	return append(code, instr)
}

func (b *block) flatten(code []asm) []asm {
	for _, prog := range b.progs {
		code = prog.flatten(code)
	}
	return code
}

func (asm *asmInstr) link(labels map[*Label]int) Instr {
	pc := labels[asm.label]
	switch InstrOp(asm.instr) {
	case OpFrame:
		return NewFrameInstr(pc)
	case OpFjump:
		return NewFjumpInstr(pc)
	case OpJump:
		return NewJumpInstr(pc)
	}
	return asm.instr
}

func Assemble(prog Prog) []Instr {
	asmCode := make([]asm, 0, prog.size())
	asmCode = prog.flatten(asmCode)
	labels := make(map[*Label]int)
	i := 0
	for _, asm := range asmCode {
		switch asm := asm.(type) {
		case *Label:
			labels[asm] = i
		case *asmInstr:
			i++
		}
	}
	code := make([]Instr, i)
	i = 0
	for _, asm := range asmCode {
		switch asm := asm.(type) {
		case *asmInstr:
			code[i] = asm.link(labels)
			i++
		}
	}
	return code
}

func GenBlock(progs ...Prog) Prog {
	return &block{progs}
}

func GenConst(x Value) Prog {
	return &asmInstr{NewConstInstr(x), nil}
}

func GenJump(label *Label) Prog {
	return &asmInstr{NewJumpInstr(-1), label}
}

func GenPush() Prog {
	return &asmInstr{NewPushInstr(), nil}
}

func GenFjump(label *Label) Prog {
	return &asmInstr{NewFjumpInstr(-1), label}
}

func GenClose(temp *Template) Prog {
	return &asmInstr{NewCloseInstr(temp), nil}
}

func GenFrame(label *Label) Prog {
	return &asmInstr{NewFrameInstr(-1), label}
}

func GenApply(nargs int) Prog {
	return &asmInstr{NewApplyInstr(nargs), nil}
}

func GenShift() Prog {
	return &asmInstr{NewShiftInstr(), nil}
}

func GenReturn() Prog {
	return &asmInstr{NewReturnInstr(), nil}
}

func GenLocal(n int) Prog {
	return &asmInstr{NewLocalInstr(n), nil}
}

func GenFree(n int) Prog {
	return &asmInstr{NewFreeInstr(n), nil}
}

func GenGlobal(n int) Prog {
	return &asmInstr{NewGlobalInstr(n), nil}
}

func NewLabel() *Label {
	return new(Label)
}
