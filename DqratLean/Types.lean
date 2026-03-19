-- Core types: Literal, Var, CRef
-- MiniSAT encoding: x = var*2 + (1 if positive, 0 if negative)

abbrev Var := Nat  -- 1-indexed internal variable

structure Literal where
  x : Nat
  deriving BEq, Repr

instance : Ord Literal where
  compare a b := compare a.x b.x

def mkLit (v : Var) (pos : Bool) : Literal :=
  ⟨v * 2 + if pos then 1 else 0⟩

def Literal.var (l : Literal) : Var := l.x / 2
def Literal.isPos (l : Literal) : Bool := l.x % 2 == 1
def Literal.negate (l : Literal) : Literal := ⟨l.x ^^^ 1⟩

abbrev CRef := Nat
def CRef_Undef : CRef := 0

-- Safe array set: returns a unchanged if index is out of bounds
def arraySafeSet (a : Array α) (i : Nat) (v : α) : Array α :=
  if i < a.size then a.set! i v else a

-- Grow array to at least n elements, padding with dflt
def arrayGrowTo (a : Array α) (n : Nat) (dflt : α) : Array α :=
  if a.size >= n then a
  else a ++ (List.replicate (n - a.size) dflt).toArray
