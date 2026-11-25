import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11021_aux

open PEqualNP.CircuitLowerBounds

/-- The function the step posts, spelled the way the statement spells it. -/
def f_L_meta_11021 : (Fin 9 → Bool) → Bool :=
  fun x => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8

/-- A gate list of length zero leaves the inputs alone: there is nothing to compute with. -/
theorem wires_nil (C : Circuit) (h : C.gates = []) (x : List Bool) : C.wires x = x := by
  simp [Circuit.wires, h]

/-- Reading a wire of the input vector: `ofFn` and `getD` agree, which is the only list plumbing needed. -/
theorem getD_ofFn {α : Type} : ∀ (v : Fin 9 → α) (j : ℕ) (d : α), j < 9 → (List.ofFn v).getD j d = v ⟨j, ‹_›⟩ := by
  intro v j d h
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

/-- An input that is true on one vertex satisfies no edge, so the function is false there. -/
theorem f_L_meta_11021_single (k : Fin 9) : f_L_meta_11021 (fun i => decide (i = k)) = false := by
  have key : ∀ a b : Fin 9, a ≠ b → (decide (a = k) && decide (b = k)) = false := by
    intro a b hab
    by_cases ha : a = k
    · have hb : b ≠ k := by rw [← ha]; exact hab
      simp [ha, hb]
    · simp [ha]
  simp [f_L_meta_11021, key]

end PEqualNP.Outside.L_meta_11021_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_11021_aux

theorem PEqualNP.Outside.L_meta_11021 : (¬ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) t)) := by
  intro h
  obtain ⟨C, -, hsize, hev⟩ := h 0
  have hgates : C.gates = [] := by
    have : C.gates.length = 0 := Nat.le_zero.mp (by simpa [Circuit.size] using hsize)
    exact List.length_eq_zero_iff.mp this
  have hw : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (List.ofFn x).getD C.output false := by
    intro x
    simp [Circuit.eval, wires_nil C hgates]
  by_cases hk : C.output < 9
  · let x : Fin 9 → Bool := fun i => decide (i = ⟨C.output, hk⟩)
    have h1 : C.eval (List.ofFn x) = true := by
      rw [hw x, getD_ofFn x C.output false hk]
      simp [x]
    have h2 : f_L_meta_11021 x = false := f_L_meta_11021_single ⟨C.output, hk⟩
    have := hev x
    rw [h1, show f_L_meta_11021 x = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) x from rfl, h2] at this
    exact Bool.noConfusion this
  · let x : Fin 9 → Bool := fun _ => true
    have h1 : C.eval (List.ofFn x) = false := by
      rw [hw x, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hk]
    have := hev x
    rw [h1, show f_L_meta_11021 x = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8) x from rfl] at this
    simp [x, f_L_meta_11021] at this
