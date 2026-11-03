# C3.2.15: bounded sparse-compactness audit

This is a design checkpoint, NOT a HOL theorem or a claim that either frozen
obligation is proved. No production definitions are proposed by this report.

## 1. Abstract compactness (mathematical argument only)

Let A = 256 word, z = 0w, supp(a) = {i | a i <> z}, and
S_N(a) = FINITE(supp(a)) /\ CARD(supp(a)) <= N.
Suppose Q(k,a) is nested in k, depends only on coordinates below B(k), and
for every k there is a_k with S_N(a_k) /\ Q(k,a_k).
Then there is a with S_N(a) /\ (!k. Q(k,a)).

Proof: choose a_k. For every finite prefix length d, retain prefixes occurring
for arbitrarily large k. The empty prefix qualifies. Every qualifying prefix
has a qualifying one-letter extension, since A is finite and a finite union
of bounded index sets is bounded. Choose such extensions recursively. They
define a stream a. For fixed k, its prefix of length B(k) occurs among a_j
with j >= k; nesting and prefix-dependence give Q(k,a). If a had N+1 distinct
nonzero positions, take d larger than all of them. A qualifying d-prefix
would force an a_j to have N+1 nonzero positions, contradiction. Hence supp(a)
has cardinality at most N and is finite. Note that no bound on the *largest*
support index was needed. Ones escaping to infinity may disappear in a.

Checked library interface: pred_setScript.sml:8171-8174 exports KoenigsLemma:
  (!x. FINITE {y | R x y}) ==>
  !x. ~FINITE {y | RTC R x y} ==>
       ?f. f 0 = x /\ !n. R (f n) (f (SUC n)).
One can instantiate R by qualifying one-letter list extension. Finite word
alphabet, unbounded prefix lengths, RTC membership, and extraction of the
stream still need HOL proofs. No compactness library has been implemented.
This is not the previously forbidden compactness of arbitrary injections:
branching here is finite because 256-bit words form a finite alphabet.

## 2. Exact candidate constraints and interpretation

Fix D,C,C',vs', xs=vs'.vs_gas_readings, N=LENGTH xs. Fix the nongas fields to
those of vs'. For S_N(a), let L(a) be any finite list representing a with zero
padding (the dftSparseOracle extraction boundary), and put
  I(a) = vs' with vs_gas_readings := L(a).
The final gas_variant is immediate for I(a). Representatives may differ by
trailing zeros; observable results must be shown independent of that choice.
Raw state equality is NOT representative-independent: residual oracle lists
can have different lengths. Compare gas-insensitive observations instead.

The exact terminal constraint is
  T_k(a) <=> !f. f <= k /\ terminates(run_context f C (I(a))) ==>
    ?g. dead_result_rel D (run_context f C (I(a)))
                         (run_context g C' vs').
This has the SOURCE-to-target direction in o1PassContractScript.sml:239-244.
The target fuel g is existential, not required to equal f. Replacing this
by target-to-source termination or by equivalence would change the task.
The relation ignores remaining gas lists (ibid.:119-134), but compares all
the indicated terminal observables; arbitrary D does not justify dropping
observable equalities. terminates is the imported passSimulation predicate.

For memory, define on paper RR_k(v,C,fn,i,s): a raw_reachable derivation of
height at most k whose next/block rule fuel parameters are at most k.
All other premises are unchanged. Every raw_reachable derivation has some
such k. Raw rules are in contextRawReachableScript.sml:26-56; entry and callee
expose post-PHI instruction states, including inside a nonreturning call.

A sufficient gas-insensitive observation relation is
  Obs(fn,i,s; fn',i',s') <=> fn'=dft_fn fn /\ i'=i /\
    inst_mem_ranges i s = inst_mem_ranges i' s' /\
    s.vs_initial_fmp = s'.vs_initial_fmp.
This is sufficient for lowered_mem_fact at *every* eom, by
unitMemInvScript.sml:66-71 and o1PassContractScript.sml:510-513. It is stronger
than logically necessary; whether DFT gives this relation is unproved.

For a source bound H(k), the candidate memory constraint is
  R_k(a) <=> !fn' i' s'. RR_k(vs',C',fn',i',s') ==>
    ?fn i s. RR_H(k)(I(a),C,fn,i,s) /\ Obs(fn,i,s;fn',i',s').
Choose H monotone. Then Q_k(a) = T_k(a) /\ R_k(a) is nested.
Entry resolution must be transported separately. The context layout bound
ctx_eom_bounded must also remain a separate lemma (owner requirement); it
is not established by oracle compactness or by Obs. Combining R_k for all k
with mem_inv_raw_reachable (unitMemInvScript.sml:96-103) yields the memory
fact transport, provided these separate entry/layout obligations are proved.

## 3. Finite dependence and exact missing semantic premises

### Terminal constraints
For a finite fixed context, fixed fuel permits only finitely many GAS reads,
uniformly over oracle values. A conservative candidate bound is obtained by
letting B be at least 1 and every block's instruction count, and recursively
V(0)=0, V(SUC f)=B+(B+1)*V(f). In a run_blocks(SUC f), at most B instructions
execute in its selected block, at most B INVOKEs run with budget f, and at
most one continuation run has budget f. exec_block recursion increases the
index; run_blocks and nested INVOKE decrease the budget before executing
another block. This follows the recursion at venomExecSemanticsScript.sml:
1665-1734. Phantom functions outside the fixed context should not be included
in this bound without enlarging B. run_context only performs entry setup.

To prove this as an observable prefix bound requires a recursion-induction
replay theorem; it is NOT yet proved by the numeric argument. It must track
the consumed count, leave arbitrary oracle tails, and quotient away those
tails in terminal observations. For T_k, no uniform bound on *target* g is
needed for finite dependence: equal source observations and termination
flags give exactly the same predicate (?g. dead_result_rel ... target_g).

### Memory constraints
At bounded derivation height and bounded rule fuels, the raw observation
set is finite for a fixed finite context and initial stream projection.
active_inst may select among finitely many instructions; enters_block is
functional (contextCodegenRelScript.sml:234-248); the rules add only finite
branching. A source derivation of height h contains at most h sequential
next/block edges, each executing step_inst at fuel <= h. A conservative
oracle coordinate bound is h*(1+V(h)), enlarged if entry setup consumes gas
(it does not). PHIs, setup_callee and enters_block consume no GAS.
A HOL bounded-raw replay/observation theorem is still required.

Crucially, H(k) has NOT been supplied by any proved lemma. Without a source
bound, the existential raw match is in general an OPEN union of finite
cylinders, not a closed condition: witnesses can move to later and later
source times and vanish at a limit. Finite derivability alone is insufficient.
No inference from E0018 supplies H, cross-context Obs, or reverse raw adequacy.

### Required simultaneous finite matching lemma (unproved)
Under the actual frozen premises, produce a context-dependent monotone H
and prove
  !k. ?a. S_N(a) /\ T_k(a) /\ R_k(a).
A proof must construct ONE allocation for the entire bounded family, not one
allocation per fuel or per observation. A plausible sufficient construction
is a shared finite unfolded execution/prefix with residual pure instructions
across suspended calls, and an injective matching from source nonzero reads
to the N target oracle slots. Reads matched to exhausted target slots or
left unobserved can be zero. Injectivity would give the support cap, including
repeated loop visits; it must be proved globally on the finite family.

Neither gas_pair_commute nor the accepted finite single-machine forward
segments prove this lemma. Pairwise swaps cannot simply be applied to a
completed call when the relevant observation is inside a suspended call.
Even finite target observations may require source GAS instructions moved
across a call to be executed before entering it. The finite family must share
that reservation, and its call continuation may need a later target value.
There is presently no checked invariant expressing this deferred reservation.

## 4. Adversarial cases (analysis, not checked counterexamples)

* Two swapped GAS reads: target values [u,v] can be assigned source [v,u].
  Support does not increase. A shared occurrence permutation works for all
  fuels in this simple block, unlike unrelated per-fuel choices.
* Source G;CALL versus target CALL;G with a returning callee: if the callee
  consumes q readings before return, source G needs target slot q, while its
  callee needs target slots 0..q-1. q is an occurrence count, not a fuel bound
  or LENGTH xs. For smaller out-of-fuel budgets, a missing return imposes no
  ctx_sim termination requirement; memory observations inside the call still
  require the same callee allocation. A largest-budget completed trace could
  serve all smaller budgets only after proving fuel-prefix consistency and
  raw coverage, not just result monotonicity.
* A returning callee can require arbitrarily large fuel across examples.
  A family satisfying bounds through k cannot infer divergence from failure
  at k. For each fixed program/state its return time may be finite but large;
  chronological zero commitment at the cutoff remains unsound.
* Genuinely nonreturning callee: target G after CALL never occurs. Source G
  may be zero if independent of the call and its arguments, but source reads
  inside the callee must still reproduce every bounded target memory
  observation. A finite witness can have very late nonzero positions; the
  compactness argument permits this and does not itself validate independence.
* Repeated visits: occurrence identities include visit and call nesting.
  Counting static GAS instructions, or bounding occurrence count by N, fails.
  The support cap is on assigned NONZERO values only; zero reads remain real
  events. Finite witnesses for larger bounds must include smaller-bound
  constraints explicitly, not just permute the last completed run.
* Memory observation in a suspended call: raw callee rule has no return
  premise. Terminal simulation can be vacuous while this obligation is not.
  H(k) must bound reaching a matching *interior* source observation, allowing
  extra caller-local pure work before CALL. None of the existing forward
  segment projections establish this cross-context bound.

## Verdict

The abstract bounded-support compactness proposal passes the mathematical
finite-branching audit. Terminal constraints have a viable finite-dependence
interface even with existential target fuel. Raw constraints require an
additional uniform source observation bound H(k), and simultaneous finite
matching remains the principal unproved semantic lemma. This report does
not derisk that lemma merely by naming it. Do not start compactness machinery
or general reverse/raw adequacy until the strategist supplies a concrete
bounded matching invariant/consumer, or chooses a different global argument.
