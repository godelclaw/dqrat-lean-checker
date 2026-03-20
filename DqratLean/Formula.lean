import DqratLean.Types

-- DQBF state: variables, quantifier types, dependency sets
structure DQBF where
  maxVar        : Var := 0
  -- external → internal: unsorted pairs, linear search
  internalName  : Array (Nat × Var) := #[]
  -- internal → external (index = internal var, 0 is dummy)
  externalName  : Array Nat := #[0]
  -- is this variable existential? (index = internal var, 0 is dummy false)
  isExistential : Array Bool := #[false]
  -- all universal / existential internal vars (in insertion order)
  univars       : Array Var := #[]
  exivars       : Array Var := #[]
  -- depset[v] = sorted array of universal vars that existential v depends on
  -- index = internal var (0 is dummy empty)
  depset        : Array (Array Var) := #[#[]]

namespace DQBF

def lookupInternal (f : DQBF) (ext : Nat) : Option Var :=
  f.internalName.findSome? fun (e, i) => if e = ext then some i else none

def externalVarExists (f : DQBF) (ext : Nat) : Bool :=
  f.internalName.any fun (e, _) => e = ext

def isVarExistential (f : DQBF) (v : Var) : Bool :=
  f.isExistential.getD v false

-- is v outer of exivar?
-- v is existential: depset[v] ⊆ depset[exivar]
-- v is universal:   v ∈ depset[exivar]
def isVarOuterOfExivar (f : DQBF) (v : Var) (exivar : Var) : Bool :=
  let depExi := f.depset.getD exivar #[]
  if f.isVarExistential v then
    (f.depset.getD v #[]).all (fun u => depExi.contains u)
  else
    depExi.contains v

-- is v outer of univar?
-- kernel = intersection of depsets of all existentials depending on univar
-- v is universal:   v ∈ kernel
-- v is existential: depset[v] ⊆ kernel \ {univar}
def isVarOuterOfUnivar (f : DQBF) (v : Var) (univar : Var) : Bool :=
  let innerDepsets := f.exivars.filterMap fun x =>
    let deps := f.depset.getD x #[]
    if deps.contains univar then some deps else none
  if innerDepsets.isEmpty then
    true
  else
    let first := innerDepsets.getD 0 #[]
    let kernel := first.filter fun u =>
      innerDepsets.all (fun ds => ds.contains u)
    if f.isVarExistential v then
      let depV := f.depset.getD v #[]
      depV.all fun u => u != univar && kernel.contains u
    else
      kernel.contains v

-- Force-delete dependency (no validity check; caller must verify)
def forceDelDep (f : DQBF) (of_ on_ : Var) : DQBF :=
  let deps := (f.depset.getD of_ #[]).filter (· ≠ on_)
  { f with depset := f.depset.setIfInBounds of_ deps }

-- Externalize a literal for error messages
def externalizeLit (f : DQBF) (l : Literal) : Int :=
  let ext := (f.externalName.getD l.var 0 : Nat)
  if l.isPos then Int.ofNat ext else -(Int.ofNat ext)

end DQBF
