package assembler

import (
	. "norstrulde/lumgua/machine"
)

type Asm interface {
	asmVariant()
}

type AsmLabel struct {
	// Pointer identity is all that matters.
}

type AsmInstr struct {
	instr Instr
	label *AsmLabel // May be nil.
}

func (asm *AsmLabel) asmVariant() {}
func (asm *AsmInstr) asmVariant() {}

func (asm *AsmInstr) link(labels map[*AsmLabel]int) Instr {
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

func Assemble(asmCode []Asm) []Instr {
	labels := make(map[*AsmLabel]int)
	i := 0
	for _, asm := range asmCode {
		switch asm := asm.(type) {
		case *AsmLabel:
			labels[asm] = i
		case *AsmInstr:
			i++
		}
	}
	code := make([]Instr, i)
	i = 0
	for _, asm := range asmCode {
		switch asm := asm.(type) {
		case *AsmInstr:
			code[i] = asm.link(labels)
			i++
		}
	}
	return code
}

func NewLabel() *AsmLabel {
	return new(AsmLabel)
}

func NewPushAsm() Asm {
	return &AsmInstr{NewPushInstr(), nil}
}

func NewReturnAsm() Asm {
	return &AsmInstr{NewReturnInstr(), nil}
}

func NewGlobalAsm(n int) Asm {
	return &AsmInstr{NewGlobalInstr(n), nil}
}

func NewConstAsm(x Value) Asm {
	return &AsmInstr{NewConstInstr(x), nil}
}

func NewFrameAsm(label *AsmLabel) Asm {
	return &AsmInstr{NewFrameInstr(-1), label}
}

func NewShiftAsm() Asm {
	return &AsmInstr{NewShiftInstr(), nil}
}

func NewApplyAsm(nargs int) Asm {
	return &AsmInstr{NewApplyInstr(nargs), nil}
}

func NewJumpAsm(label *AsmLabel) Asm {
	return &AsmInstr{NewJumpInstr(-1), label}
}

func NewFjumpAsm(label *AsmLabel) Asm {
	return &AsmInstr{NewFjumpInstr(-1), label}
}

func NewCloseAsm(temp *Template) Asm {
	return &AsmInstr{NewCloseInstr(temp), nil}
}

func NewLocalAsm(i int) Asm {
	return &AsmInstr{NewLocalInstr(i), nil}
}

func NewFreeAsm(i int) Asm {
	return &AsmInstr{NewFreeInstr(i), nil}
}
