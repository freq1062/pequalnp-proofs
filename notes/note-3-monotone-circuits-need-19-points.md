# An AND/OR circuit only has to be checked on 19 points, not 128

`programs/sat_11764.py` constrains the output wire on every one of the `2^n` inputs, which is why the
circuit-size search costs about a million clauses at ten gates and settles nothing there. For a
circuit with no NOT gate that is a factor of six wasted work.

An AND/OR circuit is monotone, and a monotone `g` equals the monotone target `f` exactly when `g` is
true on every minterm of `f` and false on every maximal point where `f` is false:

* every true point of `f` dominates one of its minterms, so `f x = true` follows from `g` on minterms;
* every false point of `f` is dominated by a maximal false point, so `f x = false` follows too.

For the Petersen edge function that is 10 minterms (the edges) plus 9 maximal independent sets, and
`--mono-witness` uses exactly those. The 9 are eight pairs plus the single {5,6}, so any assumption
about their shape is wrong: what matters is maximality, checked by brute force over all 128 points.
An earlier version of this note said 8, because the maximality test compared subset sizes instead of
testing `a & m = a`.

The mode refuses to run with `--nots 1`, because a NOT gate destroys monotonicity and the argument
with it. Whenever a `cut`/`refute` step about AND/OR size is out of reach, this is the knob to turn
before giving up on the encoding.
