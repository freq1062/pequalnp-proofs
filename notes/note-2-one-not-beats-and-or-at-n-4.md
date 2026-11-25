# A one-NOT circuit is strictly cheaper than the best AND/OR circuit already at n=4

Measured, reproducible, and it constrains how a `cut`/`refute` step about NOT elimination can be
proved. `programs/x4_witness.py` (asserted, prints its own sha256) computes, for every monotone
function on 4 inputs, the exact AND/OR gate count and the exact count with at most one NOT gate.

* 26 of the 168 monotone functions on 4 inputs are strictly cheaper with one NOT.
* Smallest: `f = 0b1010101010101000` costs 5 AND/OR gates and 3 gates with one NOT.
* The complements of these 26 are **not** monotone, so the saving is a NOT gate in the middle of
  the circuit, not a cheap monotone complement. Any proof that reasons "the NOT's argument is
  monotone, so replace its output by false" is unsound: that step needs the reading function to be
  monotone on the region the NOT is false on, and here it is not.

At n=3 all 20 monotone functions tie, so n=4 is the first witness and the phenomenon is not exotic.

## Calibration warning for anyone searching for circuits

`programs/one_not_beam.py` (beam over 128-bit truth tables) reports no one-NOT circuit for the
`L-meta-11746` target at 8, 9 or 10 gates. That is NOT a lower bound: the same search fails to find
the target's KNOWN 13-gate AND/OR circuit, which `programs/shrink_circuit.py --n 7 --edges
0-3,1-3,0-4,2-4,0-5,1-5,3-5,1-6,2-6,4-6` prints as `gates=13 wrong=0/128` after simulating all 128
points. Before trusting any search result about these targets, make the search reproduce that 13.
