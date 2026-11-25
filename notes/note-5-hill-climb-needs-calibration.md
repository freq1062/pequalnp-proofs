# A hill climb that finds nothing is not evidence

While asking whether one NOT gate ever beats the best star circuit on *edge* functions, I got
"0 of 983 graphs beat the star optimum with one NOT". That number is worthless, and the calibration
run is what shows it: the same climber, given the star optimum itself as its budget, reached distance
0 on **1 of 26** five-vertex graphs, and on the three-edge path it never got below distance 2 even
though `f = x0x1 OR x2(x1 OR x3)` is a four-gate circuit in the family.

The arithmetic of that circuit is worth stating, because it is the formula every star count uses: an
orientation that assigns each edge to the centre covering it gives `fewer_centres` stars, and the cost
is `edges + centres - 1`. Three edges with centres `{1,2}` is `3 + 2 - 1 = 4`, matching the hand-built
circuit. A star that covers an already-covered edge is pure waste: covering the path's middle edge
twice costs `4 + 2 - 1 = 5`.

So: before reporting "no circuit at size k", check that the search finds a *known* circuit at size k.
Mine does not, and until it does, absence of a hit says nothing about the circuits that exist.
