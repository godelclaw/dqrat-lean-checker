-- Core types: Literal, Var, CRef
-- MiniSAT encoding: x = var*2 + (1 if positive, 0 if negative)

abbrev Var := Nat  -- 1-indexed internal variable

structure Literal where
  x : Nat
  deriving Ord, Repr, DecidableEq

def mkLit (v : Var) (pos : Bool) : Literal :=
  ⟨v * 2 + if pos then 1 else 0⟩

def Literal.var (l : Literal) : Var := l.x / 2
def Literal.isPos (l : Literal) : Bool := l.x % 2 == 1
def Literal.negate (l : Literal) : Literal := ⟨l.x ^^^ 1⟩

abbrev CRef := Nat
def CRef_Undef : CRef := 0
