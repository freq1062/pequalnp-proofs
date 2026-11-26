import Mathlib
import PEqualNP.Defs

/-!
# `L-meta-7097`: a monotone 44-gate circuit for the difference-set fit

The step asks for `x1 : Fin 4` and a monotone circuit `x2` of size at most 62 over 27 inputs, true on
the 52 two-hot vectors of the difference set `{0,1,3,9}` and false on 624 assignments. The witness below
has 44 gates: five inputs are already safe terms on their own, eight groups are `i && (p1 || p2 || p3 ||
p4)`, and twelve ORs join the thirteen terms.
-/

namespace PEqualNP.Outside
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem L_meta_7097 :
  ∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         have x8 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))];         have x9 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x9 : ℕ × ℕ) (x10 x11 : Fin (13 : ℕ)) (x12 : Bool) =>           have x13 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x13 x14 : ℕ) (x15 : Fin (13 : ℕ)) => if x12 = Bool.true then x14.testBit ↑(-(x10 * x15 + x11)) else x13.testBit ↑(x10 * x15 + x11);           Fin.append (x13 x9.1 x9.2) (x13 x9.2 x9.1);         (∀ (x10 x11 : Fin (13 : ℕ)), x4 x10 x11 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) ∧ ∀ x10 ∈ x8, ∀ x12 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x14 : Fin (13 : ℕ)) (x15 : Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 (x9 x10 x12 x14 x15)) = Bool.false := by
  refine ⟨⟨1, by decide⟩, ⟨[{ op := GateOp.or, inputs := [13, 17] },
    { op := GateOp.or, inputs := [27, 23] },
    { op := GateOp.or, inputs := [28, 25] },
    { op := GateOp.and, inputs := [0, 29] },
    { op := GateOp.or, inputs := [13, 14] },
    { op := GateOp.or, inputs := [31, 18] },
    { op := GateOp.or, inputs := [32, 24] },
    { op := GateOp.and, inputs := [1, 33] },
    { op := GateOp.or, inputs := [14, 15] },
    { op := GateOp.or, inputs := [35, 19] },
    { op := GateOp.or, inputs := [36, 25] },
    { op := GateOp.and, inputs := [2, 37] },
    { op := GateOp.or, inputs := [13, 15] },
    { op := GateOp.or, inputs := [39, 16] },
    { op := GateOp.or, inputs := [40, 20] },
    { op := GateOp.and, inputs := [3, 41] },
    { op := GateOp.or, inputs := [14, 16] },
    { op := GateOp.or, inputs := [43, 17] },
    { op := GateOp.or, inputs := [44, 21] },
    { op := GateOp.and, inputs := [4, 45] },
    { op := GateOp.or, inputs := [15, 17] },
    { op := GateOp.or, inputs := [47, 18] },
    { op := GateOp.or, inputs := [48, 22] },
    { op := GateOp.and, inputs := [5, 49] },
    { op := GateOp.or, inputs := [16, 18] },
    { op := GateOp.or, inputs := [51, 19] },
    { op := GateOp.or, inputs := [52, 23] },
    { op := GateOp.and, inputs := [6, 53] },
    { op := GateOp.or, inputs := [17, 19] },
    { op := GateOp.or, inputs := [55, 20] },
    { op := GateOp.or, inputs := [56, 24] },
    { op := GateOp.and, inputs := [7, 57] },
    { op := GateOp.or, inputs := [8, 9] },
    { op := GateOp.or, inputs := [59, 10] },
    { op := GateOp.or, inputs := [60, 11] },
    { op := GateOp.or, inputs := [61, 12] },
    { op := GateOp.or, inputs := [62, 30] },
    { op := GateOp.or, inputs := [63, 34] },
    { op := GateOp.or, inputs := [64, 38] },
    { op := GateOp.or, inputs := [65, 42] },
    { op := GateOp.or, inputs := [66, 46] },
    { op := GateOp.or, inputs := [67, 50] },
    { op := GateOp.or, inputs := [68, 54] },
    { op := GateOp.or, inputs := [69, 58] }], 70⟩, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide

end PEqualNP.Outside
