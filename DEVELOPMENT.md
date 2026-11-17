# Development status

The `v3` structural rewrite is prepared for upstream review after a clean
project build, axiom audit, and sandboxed Comparator check.
`README.md` has been rewritten for v3 with sun123zxy's explicit authorization.
`AGENTS.md` remains unchanged.

The target is the public paper
[arXiv:2611.06944v1](https://arxiv.org/abs/2611.06944v1), submitted
2026-11-02 at 06:23:21 UTC: independent order `n`, meld count `m`, and copy
bound, with a structural, non-enumerative proof of the classification.
The correspondence was checked against the public PDF, HTML, and TeX source,
not just the local manuscript. Versioned URLs and downloaded source hashes are
in [`ComparatorChallenges/paper.json`](ComparatorChallenges/paper.json).
The default library target is `Ninegates`. The previous API, finite
enumeration and old Comparator reduction challenge have been removed from this
branch; the complete previous implementation is archived on `v2` at
`e45fd512ebb2cd0bac7d69690f3163647bdc3bc8`.

## Model

`Mahjong.VirtualHand n` is an integer vector on `Fin (3*n)`; `Nonnegative`
specifies actual hands. Subtraction is integer subtraction. The paper rank of
index `i` is `i.val+1`, including in the rank sum and congruence classes.
`Winning m`, `IsFullWait m`, and `IsLiveFullWait cap m` keep all three parameters
independent. Explicit size conditions exclude vacuous zero-rank full waits.

`Hand/Defs` and `Hand/Basic` contain the elementary patterns and linear
statistics. `Meldable/Defs` and `Meldable/Basic` introduce integer placements,
nonnegative placements, and the necessary congruence conditions. `Wait` starts
the draw-pair relation and its connection to full-sidedness and liveness.

`Meldable/Coordinates` hides the finite sums behind the coordinate equation,
using zero extension to integer indices. Its injectivity argument works over
any cancellative additive monoid, so it proves uniqueness both over the
integers and over residues. `Sequence` proves uniqueness of sequence placements;
`Canonical` constructs and proves uniqueness of canonical virtual placements,
preserves nonnegativity when present, and reduces meldability of a known
canonical placement to nonnegativity of its triplet coefficients.

`Hand/Classes` groups the ranks into blocks of three. `Meldable/Recovery`
proves the sequence recurrence, its closed form, and the two endpoint formulas.
It constructs a sequence placement exactly when all three integer class sizes
are equal; nonnegative recovered coefficients characterize actual sequential
meldability. `Meldable/Virtual` balances congruent class sizes using integer
triplets, proving that virtual meldability is equivalent to both size and rank
sum vanishing modulo three, and hence to a unique canonical virtual placement.

`Meldable/Scan` computes the canonical sequence coefficients and integer triplet
quotients. It proves the triplet-greedy recurrence, identifies the computed
placement with the unique canonical placement, and establishes the full scan
criterion: both right-end sequence values vanish and every triplet quotient is
nonnegative. Prefix congruence is equivalent to equality of the canonical
sequence prefixes. `ClosedForm` proves the weighted-prefix formula modulo three.

`Meldable/Reverse` transports placements, canonicalization, and both sequence
and general meldability under reversal. `Moving` gives the local sequence
replacement and the exact canonical borrow/carry update. It proves all four
rows of the rightward tile-moving table and that any successful long rightward
move permits the first step. The proof uses equality of the first three
triplet quotients, obtained from exact prefix agreement. `Interval` iterates
these steps and reverses them for leftward moves, proving the interval property
inside each congruence class. Its endpoint version also works when the original
hand is not meldable.

`SequentialMoving` writes the telescoping long-range sequence update explicitly
on integer indices. Uniqueness then gives the required-sequence criteria in
both directions: starts `i,i+3,...,j-3` for a rightward move, and
`j+1,j+4,...,i-2` for a leftward move. These are structural proofs for arbitrary
order, with no enumeration of hands.

Both movement directions expose their exact replacement sequence vectors.
The leftward vector subtracts the signed rightward update from target to
source, so the two placement formulas directly match the two rows of
Proposition 3.8. Nonnegativity of each vector is exactly its required-sequence
condition; uniqueness then proves both directions of the criterion.

`Meldable/Triplets` proves that adding integer triplets preserves the canonical
sequence part and translates the canonical triplet coefficients. A triplet can
be removed exactly when its canonical coefficient is positive. `Preserve`
proves that a successful step from a rank with no canonical triplet preserves
all existing triplets.

`Wait/Graph` introduces the fixed class, the class involution, incoming
intervals, and two-pair decompositions. It proves the equivalence between a
bidirectional edge on distinct ranks and a two-pair decomposition. `Classes`
proves that, for size one modulo three, each nonfixed class size plus one is
congruent to the fixed class size. `Consecutive` proves that two consecutive
edges yield a mutual edge at an intermediate rank in the same class as the
outer vertices. It follows the moving tile by well-founded induction while
preserving the middle vertex's triplet; a self-loop is allowed as the witness.
`TwoPair` derives the full-wait two-pair theorem for independent `n,m`: every
used pair in a nonfixed class participates in a two-pair decomposition, and
such a decomposition always exists. The pairs lie in different nonfixed
classes and the actual remainder has `m-1` melds.

`Hand/Cut` gives linear restrictions to the ranks strictly before and after a
cut, keeping the original rank space. `Meldable/Split` proves that a zero tile
count in an actual placement forces all crossing sequence coefficients and the
triplet at the cut to vanish. Restricting the placement then proves that a
hand missing that rank is meldable exactly when both sides are meldable. No
canonical-placement assumption is needed.

`Wait/Missing` proves the side-size residues and the opposite-side rule when
there are waiting tiles on both sides of a missing rank. Every draw on a given
side has the same congruence class. It also proves that a pair receiving draws
from both sides requires at least three copies in the original hand.
`Positive` derives positivity at every interior rank of a full-sided wait,
including order one: the only exceptional cut would be the middle of three
ranks, but the middle draw then has no available pair.

`Hand/Interior` gives the indicator hand with one copy of every interior rank
and zero at both boundaries. Its class sizes are `n` in class two and `n-1` in
each boundary class. The excess above this hand is nonnegative in a full wait.
Class-size monotonicity and bounds on one or two terms turn small class totals
into constraints on individual multiplicities. `Neighbours` constructs a rank
of either other congruence class within two steps on each side when there is
room.

`Wait/Bounds` proves that the fixed class contains at least `n` tiles and each
nonfixed class at least `n+1`. If a class of size at most `n` supplies a pair,
it must be a boundary class with a unique interior rank of multiplicity two.
For a nonfixed class, full-sidedness forces draws from both sides to use that
rank, contradicting the three-copy requirement. Summing the three class bounds
proves `IsFullWait.meldCount_gt_order`: every full-sided wait satisfies `m>n`.
The proof uses no bound on tile multiplicities.

`Meldable/Statistics` proves that each sequence contributes one tile to every
class, and that a placement's class size equals its sequence count plus three
times its triplet count in that class. In an actual meldable hand, a class
larger than another class must supply a removable triplet. This conclusion
retains an actual meldable remainder, not just a large original multiplicity.

`Wait/ClassSizes` proves the exact sizes at `m=n+1` and `n>=2`: the fixed class
has `n` tiles and every other class has `n+2`. Congruence and the lower bounds
first reduce the sizes to two possibilities, including the order-one exception.
In the unwanted case, every nonfixed draw requires triplets in both its own
class and the fixed class. If the fixed class is not class two, a draw of
multiplicity one in class two cannot supply the required triplet. If it is
class two, all fixed-class triplets are forced to a single original rank.
Removing that triplet leaves a missing rank while preserving waiting on both
other classes, contradicting the cut constraints. The assumption `n>=2` is
used explicitly and the proof does not enumerate hands.

`Wait/Pillars` proves that the fixed class has at most one original rank of
multiplicity two, while each nonfixed class has a unique rank of multiplicity
at least two; that rank has three or four copies. Removing the two forced
triplets from fixed-class winning remainders and splitting at a hypothetical
extra pair excludes any second candidate. `PillarPlacements` strengthens this
to every actual winning placement of a fixed-class draw: its sequence count is
`n-1` and its entire triplet vector consists of one triplet at each pillar.

`PillarPair` packages the two pillars and determines all edges from either
nonfixed class. The only two-pair decompositions are the pillar pair and its
exchange. `PillarRemainder` proves that removing the two pairs leaves a sequential
hand of size `3n`. Moving a tile from either pillar to any rank in its own class
preserves sequential meldability. These are the structural inputs for the
eight-family argument below.

`Meldable/Required` indexes each pillar's required starts by `Fin (n-1)` and
proves that the row is injective and has exactly `n-1` entries. Moving to both
ends of the class forces every entry to occur. Generic nonnegative-weight
bounds control row unions and their overlap; equality forces the entire
sequence vector to be the indicator of the required set.

`RequiredTwo` and `Wait/Required` settle the fixed-class-two counting step:
the two rows exhaust all possible common middle starts, so the paper pillar
ranks are `p in {1,4}`, `q in {3n-3,3n}`, and every sequence coefficient is
fixed by their union. `RequiredOne` and `Wait/RequiredOne` settle the
fixed-class-one step: a sequence outside both rows forces them to coincide,
so `p=3`, `q=3n-1`, and the remainder is the periodic row plus a sequence
starting at paper rank one or two. The proof explicitly handles the hypothetical
pillar at rank two using the missing-rank split.

`Hand/Reverse` proves size and rank-sum reversal identities, and `Wait/Reverse`
transports full and live waits with fixed class sent to `1-s`.

`Hand/Segment` describes intervals of single tiles and their sizes.
`Meldable/Segment` partitions any interval of length divisible by three into
sequences, including the two pieces obtained by removing an appropriate tile.
`RequiredCoordinates` gives arithmetic row membership and proves its converse:
containing the row suffices for all moves in that class. `RequiredPatterns`
identifies the two forced coefficient templates with their hand vectors.

`Standard/Defs` defines the paper's eight named families with interval vectors;
`Standard/Basic` proves their coordinate patterns and reflection identities.
The description of `E` includes the overlapping end patterns at order two.
`Standard/Necessity` proves every full-sided `(n,n+1)` wait for `n>=2` belongs
to these families, using the row argument and reflection for fixed class zero.

`Wait/Construction` turns the two rows and fixed-class winning decompositions
into full-sidedness. `Standard/WaitTwo` and `Standard/WaitOne` verify all the
family constructions with sequences and triplets. For `D`, the bottom
fixed-class draw pairs at paper rank four; all its other fixed-class draws
self-pair. The interval lemma verifies the remaining tiles in each case.

`Classification.isFullWait_iff_eightFamily` is the resulting non-enumerative
eight-family equivalence. `liveFullWait_unique` and `isLiveFullWait_iff_eq_A`
derive live uniqueness under copy bound four: every other family has a
coordinate of multiplicity four, while every coordinate of `A` is at most three.
These declarations are in the `Mahjong.VirtualHand` namespace.

`Standard/One` handles order one separately. Each class contains one rank, so
the two class-size alternatives give precisely the six displayed hands.
Their eighteen explicit draw-pair decompositions are verified by kernel
evaluation of the proved meldability criterion; no hands are searched to
establish necessity. All six are live. `Standard/Valid` also proves that every
full-sided `(n,n+1)` wait, including order one, respects the four-copy bound.

`Meldable/Coverage` bounds the tile contribution of canonical sequences by the
paper's threshold `(2,4,6,...,6,4,2)`, with `(2,4,2)` at order one.
`Wait/Abundance` proves every congruence-permitted draw-pair edge above this
threshold, and hence full-sidedness whenever the hand has the required size.
The proof uses the canonical virtual placement: each triplet coefficient has
three times its value at least `-2`, so integrality forces nonnegativity.
At order one this threshold can be improved to `(2,2,2)`:
`drawPair_orderOne_of_two` and `isFullWait_orderOne_of_two` prove the stronger
statement using nonnegative virtual meldability. The paper's stated threshold
remains sufficient.

`Wait/OrderOne` gives the exact criterion at arbitrary meld count: the hand
has size `3m+1`, its fixed rank has at least one tile, and its other two ranks
have at least two each. The class-dependent threshold has size five and rank
sum congruent to minus its specified class. Adding the threshold for the
negative fixed class, or subtracting the threshold for the fixed class, are
inverse translations on integer hands. This gives an explicit bijection from
nonnegative triples of sum `3m-4` to full order-one waits for `m>=2`.
`Numerical/OrderOne` applies stars and bars to prove the exact count
`choose(3m-2,2)`; the count is zero for `m<=1`. These counts have no copy bound.

The order-one abundance and minimality proofs reuse this shared threshold
criterion. The virtual draw congruence criterion now lives in `Wait/Classes`,
independently of abundance, and the size residue is packaged once in
`Wait/Basic` for use by the abundance, minimality, and reversal arguments.

`Wait/Add` preserves all draw-pair edges and full-sidedness under adding an
arbitrary actual meldable hand. `Minimal/Defs` defines minimal full waits by
excluding every nonzero meldable removal leaving a full wait of any meld count.
`Minimal/Basic` proves that every full wait with `m=n+1` is automatically minimal.
The eight-family classification therefore also classifies minimal waits at
that meld count.

`Meldable/OrderOne` proves that nonnegativity and the congruence conditions
suffice for meldability at order one. `Minimal/One` uses the class bounds to
place one of the six smallest full waits below any order-one full wait, with
the same fixed class. Their difference is nonnegative and virtually meldable,
hence actually meldable. Thus every minimal order-one full wait has `m=2` and
is one of the six classified hands.

`Meldable/Large` proves that seven tiles at one rank of a meldable hand force
a removable triplet. `Minimal/Upper` applies this uniformly to all winning
remainders when an original rank has at least nine copies. Removing that
triplet preserves full-sidedness, so every minimal full wait has multiplicities
at most eight and satisfies `m<8n`.
`Minimal/Maximum` defines `maxMinimalMeldCount n` and proves the maximum is
attained at every positive order, with `M(1)=2`.

`Minimal/Double/Full` constructs the paper's `(3,2,...,2)` family at meld count
`2n`, including live full-sidedness. Fixed-class draws move a tile within the
sequential hand of all twos; the other two classes use two doubled intervals
and two triplets. `Double/Rigidity` proves that the first draw must self-pair
and that a draw at the middle of a three-rank block forbids that block's
sequence in every actual winning placement.

`Double/Minimal` applies these constraints to an arbitrary meldable removal.
The first draw forces the removed hand to contain only block sequences, with
no triplets; the corresponding middle draws force every such coefficient to
vanish. Thus the family is minimal. `maxMinimalMeldCount_bounds` and
`exists_maximal_minimal_meldCount` now give the full paper bound `2n<=M(n)<8n`,
including attainment and maximality. The alternating constructions below
strengthen the lower bound.

`Meldable/RemoveSequence` gives an exact removal criterion: either the canonical
sequence coefficient is positive, or all three covered ranks supply a canonical
triplet. In the second case, replacing those three triplets by two sequences
provides the remaining hand. `Meldable/Elementary` proves that every nonzero
meldable hand has an elementary meld that can be removed. `Minimal/Criterion`
therefore reduces minimality to excluding individual triplet and sequence
removals, while retaining the paper's definition for arbitrary meldable removals.

`Minimal/Alternating` starts the two stronger even/odd families. Their common
coordinate definition, sizes, and the forced location of later draws' pairs
are formalized: any draw at zero-based index at least four must pair among the
first three ranks. `Alternating/Class` proves their fixed classes are two and
zero. `Alternating/Full` proves full-sidedness for all parameters, with meld
counts `9a+6` and `9a+10`. The boundary-sensitive abundance estimate covers all
but the short exceptional prefix, whose fixed states are checked in the kernel
and transferred across orders using `Meldable/Prefix`.

`Alternating/Scan` proves a closed formula for every legal canonical sequence
coefficient after any draw and pair removal. It combines the base sequence
recurrence with two single-tile impulses. The formula is valid for arbitrary
orders and indices; it does not rely on checking finitely many family members.
`Alternating/Critical` now proves the critical-draw obstructions in the
alternating middle: the selected draw forces a zero triplet coefficient, or a
zero sequence coefficient together with a zero covered triplet coefficient.
These identities hold at arbitrary order. `Alternating/Boundary` transports
fixed prefix certificates through the common `PrefixModel`; `Exceptional`
handles the two early draws whose pairs need not lie among the first three
ranks. `Alternating/Minimal` excludes every elementary removal and therefore
every nonzero meldable removal. It proves minimality of both families and
`9*n/2-3 <= M(n)`. Together with the double family the bound is
`max(2*n,9*n/2-3) <= M(n) < 8*n` at every positive order.

The example `(0,2,2,4,2,3)` is verified by six explicit meld placements as a
full-sided `(2,4)`-wait. It is live for copy bound five and not live for four.
This checks parameters beyond the old fixed relation `m=n+1`.
The negative-sequence example checks that `-1 = 2 + 3*(-1)` is used in virtual
canonicalization; it is not converted to a natural-number coefficient.
Two right-boundary examples have zero recovered coefficients at every legal
sequence start, but endpoint states `(1,0)` and `(0,1)`. Both are rejected;
checking only the admissible start coefficients would miss these failures.
Their computed triplet quotients are all zero. Conversely, the nonnegative hand
with tiles at paper ranks `1,3,5` satisfies the size/rank-sum congruences but has
a negative triplet quotient, so it is virtually meldable and not actually
meldable. These examples check each part of the scan criterion separately.

`MovingExamples` checks the overlapping borrow/carry case, where only the
source triplet is needed, and a failed borrow despite source-tile availability.
It also separates success of the first sequential step from failure of a longer
move with a later required sequence absent.

`GraphExamples` verifies two different two-pair decompositions of the larger
example. It also checks the paper's full-sided `(3,7)`-wait
`(2,2,2,3,3,2,4,1,3)`: its fixed class is zero and the incoming neighbours of
paper rank nine are exactly ranks three and six. Thus a used pair in the fixed
class need not have a self-loop.

`SplitExamples` checks that splitting cannot be extended to virtual placements:
`e_1-e_4` has a virtual sequence placement and is zero at rank two, but its left
piece has size one and is not even virtually meldable. The order-one hand
`(2,0,2)` has outgoing edges for the two boundary draws and none for the middle
draw, checking the special case in the interior-positivity argument.

`BoundsExamples` verifies the order-one full wait `(2,3,2)` with fixed class two
and class sizes `(2,2,3)`. It attains the two nonfixed-class lower bounds and
checks the order-one exception that the later `m=n+1` classification must retain.

## Paper alignment

The challenge and solution each list all 43 numbered public v1 items in paper
order: Theorem 1.1, 27 propositions, nine definitions, three examples, two open
problems, and Conjecture 6.9. All propositions and the theorem are formalized;
Examples 4.5 and 6.5 are formalized. Definitions identify the relevant model
objects rather than being counted as new paper theorems. Example 6.6 is deferred,
and the problems and conjecture remain explicitly open. The selected statements,
including the five remarks and eleven additional results, give 120 Comparator targets.

`Standard/Graph` was added during this audit: it proves Example 4.5's exact
draw-pair relation for `A_n` and its fixed class two for every positive order,
including order one. The correspondence also exposes the literal sequence
recurrence uniqueness, all three parts of Proposition 5.10, and the existential
full-wait conclusion of Proposition 6.2.

| Part of the public v1 paper | Current status |
| --- | --- |
| Virtual hands, independent parameters, elementary tile patterns | Implemented |
| Class-size partition and rank-sum congruence | Proved as sums over `ZMod 3` |
| Equal-class residue criterion from the two linear congruences | Proved |
| Virtual and nonnegative meld placements | Implemented |
| Virtual meldability iff class residues agree iff size and rank sum vanish modulo three | Proved |
| Draw-pair congruence and pair availability | Proved |
| Virtual sequence placement uniqueness | Proved |
| Sequence recurrence, closed form, boundary formulas, and existence criterion | Proved |
| Nonnegative sequence-placement criterion | Proved |
| Virtual canonicalization and unique canonical placements | Proved |
| Meldability of a known canonical placement iff triplet coefficients are nonnegative | Proved |
| Canonical sequence part under coordinatewise congruence | Global and prefix versions proved |
| Canonical scan, weighted closed form, boundary formulas, and full criterion | Proved |
| Sequential tile moving, four-case general moving, interval property | Proved |
| Fixed/interchanging classes and class-size congruence | Proved |
| Exact draw-pair graph and fixed class of `A_n` (Example 4.5) | Proved |
| Incoming intervals, bidirectional edges, consecutive edges, two-pair theorem | Proved |
| Missing-rank split, waits across a missing rank, interior positivity | Proved |
| Incoming edges from both sides force three copies | Proved |
| Class-size lower bounds and `m>n` | Proved |
| Classwise sequence/triplet statistics and removable triplets | Proved |
| Exact class sizes at `m=n+1` for `n>=2` | Proved |
| Two pillars and all fixed-draw winning placements at `m=n+1` | Proved |
| Unique two-pair decomposition and sequential remainder/moves | Proved |
| Required sequence rows and exact fixed-class-two/one templates | Proved |
| Full-wait reversal and fixed-class transformation | Proved |
| Named eight-family classification and six order-one hands | Proved |
| Live uniqueness as a corollary of the new classification | Proved |
| Four-copy validity of every full-sided `(n,n+1)` wait | Proved |
| Abundance and preservation under adding melds | Proved |
| Minimality at `m=n+1` and all order-one minimal waits | Proved |
| Eight-copy bound for minimal waits and `m<8n` | Proved |
| Existence of the maximum `M(n)` and `M(1)=2` | Proved |
| Minimal `(3,2,...,2)` family and lower bound `2n<=M(n)` | Proved |
| Full-sidedness of the stronger even/odd constructions | Proved |
| Minimality of the stronger constructions and improved lower bound | Proved |
| Distinct families and exact standard cardinalities 0/8/6, live 1/6 | Proved |
| Nonminimal `(n,n+2)` characterization, Taiwanese nonminimal count 122 | Proved |
| Taiwanese total/live/minimal counts 149/11/27 (Example 6.6) | Deferred |

`Standard/Distinct` proves the eight named families are pairwise distinct at
every order at least two. Their two endpoints and second coordinate distinguish
all but `D` and `E`; the fourth coordinate separates that last pair. The six
explicit order-one vectors are distinct as well. `Cardinality` constructs
bijections from `Fin 8` and `Fin 6` to the full-wait subtypes, giving the exact
counts for full and minimal waits. It also proves live cardinalities one and
six, zero cardinalities for `m<=n`, and six minimal order-one waits across all
meld counts. These are consequences of the structural classification, not an
enumeration of candidate hands.

`Minimal/Next` characterizes all nonminimal full-sided `(n,n+2)` waits at
`n>=2`: each is one of the eight standard hands plus one triplet or sequence.
This follows from elementary removal and the structural classification at
`m=n+1`. `Numerical/Taiwanese` proves there are exactly 122 such hands at
`n=3`, by kernel evaluation of the finite set of 128 standard-hand/meld
combinations with duplicates removed. The paper's total/live/minimal Taiwanese
counts 149/11/27 remain unformalized; independent discovery computations are
not used as Lean proofs.

`Minimal/LiveNext` sharpens this for live draws under copy bound four. A
nonnegative elementary meld added to a standard family can only preserve
liveness if the standard family was live already, so that family must be `A_n`.
Adding a triplet to `A_n` violates liveness, while adding a sequence is live
exactly when the sequence avoids both boundary ranks. Thus for every `n>=2`,
the live nonminimal `(n,n+2)` waits are precisely `A_n + sequence r` with
zero-based start `1 <= r <= 3*n-4`. The sequence starts give an explicit
bijection, proving the exact count `3*n-4` without enumerating candidate hands.
At `n=3` this gives exactly five live nonminimal Taiwanese waits; it does not
establish the deferred total of eleven live Taiwanese waits.

Consequently, any live `(n,n+2)` wait missing either boundary rank is minimal
in the original arbitrary-removal sense. The class-bound sharpness witness
from the remark after Proposition 5.6 is therefore minimal and live at every
`n>=2`. These are additional consequences of the formalized theory, not new
numbered results attributed to arXiv v1. Three additional Comparator targets
certify the classification, count, and minimal/live witness.

### Remaining paper statements

The numbered results have one unfinished example: **Example 6.6**, the
Taiwanese `149/11/27` counts. At sun123zxy's request, expensive computation is
parked. A direct 100-case kernel-check prototype reached the 4 GB memory limit
and a 30-second timeout; the full 24,310-candidate batch was not started.
This is a limitation of that prototype, not a claim that an improved kernel
certificate would necessarily be expensive. The structural proof of the
nonminimal count 122 is complete.

All five unnumbered remarks are now formalized, with their proof targets next
to the corresponding paper proposition in both Comparator files:

| Remark after | Formalized statements |
| --- | --- |
| 4.11 | The two explicit decompositions and all six specified winning pairs of `(0,2,2,4,2,3)`; the fixed-class vertex with incoming interval `{3,6}` and no self-loop in the nine-rank example |
| 5.6 | `A_n` attains the fixed-class lower bound at every positive order; `(2,3,2)` attains both interchanging bounds at order one; `(0,3,3,3,1^(3n-5),3)` is full for all `n>=2`, with all three asserted edge families, fixed class two, and class-one size `n+1`; reversal attains the class-zero bound |
| 5.8 | The order-one counterexample to the `n>=2` class-size conclusion |
| 5.9 | `D_n` has fixed class one and multiplicity two at paper rank four |
| 5.10 | A difference is virtually meldable exactly when fixed classes agree, and the partition `{A,B,B',E}`, `{C,D}`, `{C',D'}` into fixed classes two, one, and zero |

`Wait/Sharpness` proves the general family by explicit sequence intervals and
triplets. The useful interval identity is in `Meldable/Segment`: moving the
first tile rightward to a congruent rank splits the remaining vector into two
sequence intervals, including a target at the interval's right endpoint.
`Hand/Reverse` supplies the class-size reflection formula. No candidate hands
are enumerated. `Standard/Classes` packages the eight fixed classes and the
attainment example. The difference criterion in `Wait/Classes` actually holds
for any two full-sided waits on the same ranks, even with different meld counts.

These statements and the numbered-result inventory account for the paper's
five explicit remarks. They do not turn open problems or numerical discovery
computations into proved results.

**Problems 6.1 and 6.4** ask for general classifications and counts beyond the
proved regimes; they are open questions in the paper, not missing proofs of
claimed results. The arbitrary-meld-count case at order one has the explicit
criterion and count above. `Minimal/Next` settles the nonminimal part at `m=n+2`.

The exact general `M(n)` formula remains a conjecture in the paper. It is not
assumed as an axiom or used to prove any part of this development. Existing
computer-assisted upper-bound experiments are separate from this structural
formalization.

## Verification

Use the pinned Lean 4.35.0 and dependencies:

```sh
lake build --wfail Ninegates
lake env lean -j2 -M4096 -DwarningAsError=true Audit.lean > axioms.log
python3 scripts/check_axioms.py Audit.lean axioms.log
python3 scripts/check_paper_coverage.py
lake build --wfail ComparatorChallenges.Solution
lake comparator --config=ComparatorChallenges/config.json
```

The audit covers the foundational results and the complete explicit example.
Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are no
placeholder proofs or uses of `native_decide` in the library. `Audit.lean`
and `scripts/check_axioms.py` provide the local standard-axiom audit. The new
`ComparatorChallenges` target checks 120 statements against a model importing
only shared foundational project definitions. Derived model objects have their
own namespace and definitions; only the solution imports the library and proves
the required bridges. Run Comparator with its sandbox enabled. Its intentional
challenge holes are outside the default library. The correspondence check
enforces the independently pinned public order, source version, equal full source
signatures, target inventory, all five ordered remark blocks, and explicit
exclusions. Named arguments such as `(n := n)` remain part of the signature;
only the outer declaration assignment ends it. It is an inventory check; kernel
verification and mathematical review of the statements remain separate
requirements.
`README.md` introduces the current API; this file records its detailed status.

The Comparator readability cleanup was checked against commit
`1078e6b275b0136f496353920b428112e54897ff`: all 121 challenge theorem types
(including the deferred goal) are definitionally unchanged, as is the open
conjecture's proposition. Lean accepted 122 equality checks using `rfl`; a
control substituting a different proposition was rejected. The model,
configuration, and proof bodies are unchanged. This preservation check does not
certify the deferred goal or conjecture. The strict solution build and normal
sandboxed Comparator were rerun for the cleaned statements. Seventeen temporary
inventory mutations were rejected, including a changed tile-movement conclusion
after a named argument that the previous signature splitter missed.


The 16 November 2026 stability review rebuilt the project from tracked sources
in a detached checkout of `7b6149793573a8a60c4c916aa06da9268e172e6a`, with an
empty project build directory and the pinned dependency cache. Both `Ninegates`
and `ComparatorChallenges.Solution` passed `--wfail` (3,252 jobs). All 109
library modules are reachable from the root import, and the strict audit passed
for 606 declarations. The normal sandboxed Comparator passed all 120 targets in
the regular checkout, whose tracked sources matched the detached checkout.
The deferred Example 6.6 and the open questions retain their explicit status.


The hosted `Lean Action CI` workflow is manual (`workflow_dispatch`) and runs
only checkout plus `lean-action` with `--wfail`. Dispatch it at a work milestone.
Docgen is disabled in this workflow. The axiom audit, paper correspondence and
sandboxed Comparator commands above remain local validation checks.
