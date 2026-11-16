# Independent fixed-proof reuse audit (C1.5.5.2 / L0041)

## Result and scope

The integrated package contains the fixed_init proof and reduced premise
assembly executed in E0133. I compared the actual archived source, original
typed capture, successful-prefix/later-failure output and post-QED marker;
I did not infer closure from the producer's summary alone. The 19 selected
premises supply the captured conjunction without new hypotheses. There is
no remaining fixed-residual theorem to extract from this observation.

This is a diagnostic source/evidence audit, not a HOL theorem, a supplier
acceptance or a passing Consumer build/check. No Consumer, contract or helper
source was edited or rebuilt by this audit. The current PLAN explicitly
forbids retrying the known-red Consumer cone here; its final ordinary build
belongs to C1.5.5.8.

## Integrated source identity and comparison

At this lane's synchronized head a640ef10c (merge of integration cb214dbaf),
`git rev-parse HEAD:<path>` returned:

| Path in this directory, unless otherwise stated | Exact Git blob |
| --- | --- |
| Consumer.base.txt | 5a295bb9c0d27cebf180e7355caefe7dd3edac34 |
| Consumer.reconstructed.txt | 2970c304716a8db3019f7f0b490e31c98bce8270 |
| Consumer.base-and-patch.txt | eba254ab97f10014d1558f5f489c3d26596c085d |
| ../bodyFullForArrayLocalContractsScript.sml | f363d2c91cc5a2dd39819e6b0359b0224bc4a986 |

These agree with the producer's recorded base/reconstruction/patch/contract
identities. The unchanged patch has +31/-5 across four hunks. In particular,
its fixed_init hunk at base line 1456 introduces the 19-premise projection,
retains the original already-closing proof in a comment, and adds the marker
after QED. The seven quotations and theorem header are outside these hunks.

I compared reconstructed lines 1356-1533 against the actual historical
source readback m1066_t002 (full ID below): setup, contract application,
19 selectors, reduced solver, commented original solver, endpoint witnesses,
Head assembly, QED and marker agree line-for-line. The diagnostic version
captured by m1041/m1042 differs deliberately at reconstructed 1474: it had
`capture_goal "fixed-premise-assembly"` where the archive now retains the
closing solver at 1474-1480. This is the intended capture-to-reuse change,
not an unrecorded discrepancy. m1044 subsequently reaches dynamic_init at
1535 and fails at 1547-1550, matching the archived next Resume location;
m1045 records the post-fixed_init marker.

## Exact reuse boundary for the final join

All following line numbers refer to **Consumer.reconstructed.txt**, not the
base snapshot or a future production file:

- 1356-1444: fixed_init setup, root-linked allocation/block facts, horizon
  existence, operand availability, freshness and array shape facts.
- 1445-1455: apply the existing labelled `fixed` antecedent to actual compiler,
  state, ghost, scope and block facts, then specialize av, tv and vs.
- 1456-1480: implication-premise conjunction proof; select exactly 19 existing
  facts with qpat_assum/mp_tac, drop the irrelevant context locally, reintroduce
  those facts, and run the retained closing solver.
- 1481-1488: original already-closing solver preserved as a comment (not a
  second proof obligation).
- 1489-1531: keep the selected arr_base/dst/cc/Gentry/tnentry witnesses and
  derive the initial Head at each valid H'.
- 1533: diagnostic marker only.

Reuse this actual fixed_init span, not a fabricated local_fixed_residual
lemma. Head's full abbreviation is retained at 663-693. The old labels
fixed-residual and head-leaf are fallback names, not evidence of open goals
in the executed fixed_init path. This audit does not dispose of other paths
or the separate head-disposition component.

## Independent 19-premise/conclusion comparison

`raw-goals.txt` lines 10-27 list all 18 free variable types; they agree with
the typed output in m1042. In particular H has type
`(bool # 256 word # type_value) list # num list`, not a new execution witness.
Its numbered assumptions 0-18 and conclusion 51-62 match m1042's printed
sequent modulo ASCII logical spellings and bound-variable alpha-renaming
(`sz` versus `z` in the return-buffer clause). There are 18 conclusion
conjuncts. Each is supplied as follows:

| Capture assumptions | Call-site provenance in retained source / original full context | Discharge |
| --- | --- | --- |
| 0, 1, 2: initial instruction index, block, nonhalted | Full m1038 context facts 57, 56, 55 from the initial stmt_frag_full context; selected at 1470-1472 | Direct matching of the last three conjuncts |
| 3: ~ctx_has_dalloca ctx | Derived from body_inv_no_dalloca at 503; present as full-context fact 12; selected at 1470 | Direct matching; no inference from alloca_inv |
| 4: valid_horizon cx st0 H es.storage_trace | 1389-1392 derives existence using storage_trace_horizon and the existing storage_trace_domain (full-context fact 58); the live witness H is selected at 1469 | Witness the required existential with this H |
| 5: alloca_history func s0 | Full-context fact 51, retained at 1469 | Direct matching |
| 6: vs = array_elements ent.type av | 1442-1444 from ent.type and the existing vs abbreviation | Direct matching |
| 7: ent.value = ArrayV av | Existing source-packet fact (full-context 24), retained at 1468 | Direct matching |
| 8: ent.type = ArrayTV tv (Fixed (LENGTH vs)) | 1438-1441 from existing ent.type and LENGTH vs = n proved at 1359-1363 | Direct matching |
| 9: not_fresh_at start ap | 1401-1404 from local_ptrs_reserved and the existing name binding | Var constructor injectivity in saved-base clause |
| 10: return-PC pointer reservation | 1405-1408 from ret_pc_ok cenv start s0 (full-context fact 46) | Direct matching |
| 11: return-buffer pointer reservation | Inherited full-context fact 47, retained at 1464 | Direct matching up to bound-variable alpha-renaming |
| 12: local_ptrs_reserved cenv start | Inherited full-context fact 45, retained at 1463 | Direct matching |
| 13: every old variable differs from idx | 1435-1437 from ~not_fresh_at start idx proved at 1409-1413 | Direct matching |
| 14: p <> idx | 1431-1434 from actual generated-name equations 1364-1365 | Direct matching |
| 15: LENGTH vs < dimword (:256) | Existing source-packet/full-context fact 26, retained at 1461 | Direct matching |
| 16, 17: typed size equality and +64 bound | Runtime 642-645; full-context facts 62-63; retained at 1459-1460 | Linear arithmetic gives type_memory_size tv < dimword (:256) |
| 18: fn_inst_ids_distinct func | Full-context fact 44, retained at 1458 | Direct matching |

Thus 15 conjuncts are direct assumption matches. The three remaining ones
are precisely: (i) the size inequality, using equality plus the +64 strict
bound, (ii) `!x. Var ap = Var x ==> not_fresh_at start x`, using injectivity
and assumption 9, and (iii) horizon existence, using assumption 4. No scalar
size assumption is introduced. The projection code does not assume any of
these conclusions: qpat_assum selects facts already in the context, and its
by-proof uses no new semantic antecedent. Domain evidence precedes horizon
instantiation; the code does not extract allocation safety from a vacuous
all-H statement.

The reduced conjunction is only the antecedent still left by the matching
chain at 1445-1455, not the entire fixed supplier contract. Compiler/code,
state/ghost and scope premises consumed by that chain remain part of the
unchanged surrounding proof. The `fixed` fact is still an assumed approved
cut, not an independently qualified supplier delivery.

## Observed closure and outstanding validation

The original capture m1042 intentionally fails before solving this reduced
conjunction. m1044 fails later in dynamic_init, and m1045 prints
`FIXED-INIT-AND-REDUCED-ASSEMBLY-CLOSED`. Together with the retained source,
these establish local execution past fixed_init, including its conjunction
and Head assembly. They do not establish a finalised Consumer theorem.
Dynamic_static was suspended; other suspended/unfinished obligations remain.
No general unreachable-fallback claim is made.

The endpoint and ghost witnesses are selected at 1490 before H' is introduced
at 1492; lo is retained, not specialized. The Head proof transports the same
selected path/ghost tuple, storage and return-PC information. It supplies no
arbitrary shadow compiler witness and says nothing about the outstanding
actual-root body-shadow linkage or initialized suffix.

C1.5.5.8 must reconstruct/reconcile the full Consumer from the integrated
archive under its ownership; preserve the seven quotations and frozen
headers byte-identically; connect the actual checked helper conclusions and
discharge all their premises; remove every reachable unfinished proof point;
then perform the ordinary default Consumer build and source/diff admission
and ownership audit. Supplier-instance/facade qualification is separate.
Historical execution and this diagnostic audit waive none of these checks.

## Evidence actually read for this audit

Historical original evidence:
- TO_statement_cases-L0016-20261116T193214352355Z_m1038_t001: full fixed premise context and origins.
- TO_statement_cases-L0016-20261116T193214352355Z_m1041_t001: reduced-context capture source point.
- TO_statement_cases-L0016-20261116T193214352355Z_m1042_t001: exact free types, 19 assumptions and conclusion.
- TO_statement_cases-L0016-20261116T193214352355Z_m1044_t001: continued execution, later dynamic_init failure.
- TO_statement_cases-L0016-20261116T193214352355Z_m1045_t001: post-QED marker.
- TO_statement_cases-L0016-20261116T200109121105Z_m1066_t002: historical retained fixed_init source span.

Independent L0041 readbacks/comparisons:
- TO_statement_cases-L0041-20261116T222418076790Z_m0005_t001 / m0007_t003: typed/reduced sequent readbacks.
- TO_statement_cases-L0041-20261116T222418076790Z_m0006_t001 / m0005_t002: later failure / marker readbacks.
- TO_statement_cases-L0041-20261116T222418076790Z_m0005_t003 / m0008_t001: integrated versus historical retained proof text.
- TO_statement_cases-L0041-20261116T222418076790Z_m0006_t002 / m0007_t002 / m0008_t002: surrounding source, Head and full-context provenance.
- TO_statement_cases-L0041-20261116T222418076790Z_m0007_t001: exact integrated archive and LocalContracts blob identities.
