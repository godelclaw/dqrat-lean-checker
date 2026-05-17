import Init.Data.Array.Lemmas
import DqratLean.Types

namespace DqratLean.Watched

/--
Shared array lemmas for the watched-runtime refinement proofs.

The runtime cache transitions in `WatchedState.lean` all follow the same
`rightpad` + `setIfInBounds` pattern, so keeping these facts in one file makes
the later cache proofs shorter and more stable.
-/
theorem lit_eq_of_x_eq {l₁ l₂ : Literal} (h : l₁.x = l₂.x) : l₁ = l₂ := by
  cases l₁
  cases l₂
  cases h
  rfl

theorem arraySetIfInBounds_getD_eq
    {α : Type} (a : Array α) (i : Nat) (v fallback : α) (h : i < a.size) :
    (a.setIfInBounds i v).getD i fallback = v := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD, dif_pos (hsize ▸ h)]
  simp [Array.getElem_setIfInBounds h]

theorem arraySetIfInBounds_getD_ne
    {α : Type} (a : Array α) (i j : Nat) (v fallback : α) (hij : i ≠ j) :
    (a.setIfInBounds i v).getD j fallback = a.getD j fallback := by
  have hsize : (a.setIfInBounds i v).size = a.size := Array.size_setIfInBounds
  simp only [Array.getD]
  rcases Nat.lt_or_ge j a.size with hjlt | hjge
  · rw [dif_pos (hsize ▸ hjlt), dif_pos hjlt]
    exact Array.getElem_setIfInBounds_ne hjlt hij
  · have hjlt' : ¬ j < a.size := Nat.not_lt.mpr hjge
    rw [dif_neg (hsize ▸ hjlt'), dif_neg hjlt']

theorem getD_rightpad_eq_of_lt
    {α : Type} (a : Array α) (n : Nat) (x fallback : α) {i : Nat}
    (hi : i < a.size) :
    (a.rightpad n x).getD i fallback = a.getD i fallback := by
  have hlt : i < (a ++ Array.replicate (n - a.size) x).size := by
    exact Nat.lt_of_lt_of_le hi (by simp)
  rw [Array.getD, Array.getD, Array.rightpad, dif_pos hlt, dif_pos hi]
  simpa using
    (Array.getElem_append_left' (xs := a) (i := i) hi (Array.replicate (n - a.size) x)).symm

theorem getD_rightpad_eq
    {α : Type} (a : Array α) (n : Nat) (x : α) (i : Nat) :
    (a.rightpad n x).getD i x = a.getD i x := by
  by_cases hi : i < a.size
  · exact getD_rightpad_eq_of_lt a n x x hi
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.rightpad,
      Array.getElem?_append]
    simp [hi]
    cases hopt : (Array.replicate (n - a.size) x)[i - a.size]? with
    | none =>
        simp
    | some val =>
        have ⟨hidx, hEq⟩ :=
          Array.getElem_of_getElem?
            (xs := Array.replicate (n - a.size) x) (i := i - a.size) (a := val) hopt
        have hval : x = val := by
          rw [← hEq]
          simp
        simp [hval]

theorem mem_getD_imp_lt_size
    {α : Type} {a : Array (Array α)} {i : Nat} {x : α}
    (hmem : x ∈ a.getD i #[]) :
    i < a.size := by
  by_cases hi : i < a.size
  · exact hi
  · simp [Array.getD, hi] at hmem

end DqratLean.Watched
