# The known 18-gate circuit is optimal among star circuits, so 17 needs a different shape

For the 10-vertex, 13-edge graph of `L-meta-9820`, every circuit the fleet has for this function is
"OR of stars": pick vertices `v`, form `x_v AND (OR of some neighbours)`, OR the results.

Counting that shape exactly: a star with `d` neighbours costs `d` gates (`d-1` ORs plus one AND),
and joining `k` stars costs `k-1` ORs, so the total is `sum(d_i) + k - 1`.

* The star centres must touch every edge, so they form a vertex cover. Brute force over all 1024
  vertex sets gives minimum vertex cover **6**, e.g. `{1,3,4,5,6,7}`.
* A cover of size `k` covers 13 edges, so `sum(d_i) >= 13`, giving `13 + k - 1 >= 18` gates.

Hence **no star circuit has 17 gates**, and the desk's known 18 is optimal in that family. Getting to
17 therefore requires an intermediate that is not a star, and the natural candidates are ruled out by
the same structure: any two centres of this graph share at most one neighbour (the graph has girth
5), so two stars cannot share a common `OR` subterm of size 2 or more, which is the only sharing that
would save a gate.

That is a proof obligation for whoever finds 17: the circuit must nest one star inside another's
input, not just OR independently built stars.

The count is not just an estimate from one cover. `programs/star_search.py` orients every edge towards
the centre that covers it and enumerates all `2^13 = 8192` orientations, which is exactly the star
family: it reports an optimum of **18 gates**, attained by centres `{2,3,4,5,6,7}` — a six-element
vertex cover, different from the `{1,3,4,5,6,7}` found by the earlier brute force, and every other
six-cover costs the same. A five-element cover would give 17, and none exists.

Allowing the nesting note-4 asks for does not help either. `programs/double_star_search.py` adds the
double star `O AND (x_v OR x_w)` with `O = OR of S`, which costs `|S| + 1` and covers the `2|S|`
edges between `{v,w}` and `S`, so it needs `S` inside the common neighbourhood of `v` and `w`. A DP
over the 2^13 edge subsets, taking the cheapest OR-combination of stars and double stars, still
reports **18** gates for this graph, because no two vertices share two common neighbours.

The family is not vacuous: on the five-edge test graph the same DP returns **5** gates, against 6 for
stars alone, so double stars are a genuine saving when the common neighbourhood is large enough. The
target graph simply does not offer one.

Refuting 17 by SAT is out of reach for a reason worth recording: the graph's automorphism group has
order **2** (computed over all `10!` permutations), so symmetry breaking buys a single bit, and the
encoding must still pin the circuit on 1024 input points. With one NOT allowed, the monotone
18-point reduction is unavailable. So the desk step can only be settled constructively, or by a
structural bound like the ones above.
