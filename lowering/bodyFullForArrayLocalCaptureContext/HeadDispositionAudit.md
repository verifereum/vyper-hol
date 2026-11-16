# Independent head-label disposition audit — C1.5.5.3 / L0042

## Conclusion and limits

The integrated capture note's disposition is supported by the retained source
and original execution evidence: `head-leaf` is the last, unvisited fallback
of the completed `fixed_init` conjunction solver. No unresolved sequent was
observed at that label, so no separate `local_head_leaf` theorem or speculative
premise interface is needed for this label. This retires the old label-based
helper request only. It does not assert global unreachability, completion of
all head-like goals, or qualification of the Consumer.

This is an independent diagnostic audit, not a proof extraction or a supplier
acceptance. No production HOL file, quotation, theorem header, logical premise
or proof was changed. No build was run: the current component expressly calls
for source/evidence comparison without replaying the incomplete Consumer.

## Integrated inputs inspected

This lane's synchronized HEAD is
`e17452b54355922ec95745f06968acf0a6c69ce2`, holding integration `c1452608f226`.
The exact Git objects inspected are:

| Input | Blob |
| --- | --- |
| Consumer.reconstructed.txt (in this directory) | 2970c304716a8db3019f7f0b490e31c98bce8270 |
| Consumer.base.txt (in this directory) | 5a295bb9c0d27cebf180e7355caefe7dd3edac34 |
| ../bodyFullForArrayLocalContractsScript.sml | f363d2c91cc5a2dd39819e6b0359b0224bc4a986 |

I read the integrated `../bodyFullForArrayLocalCaptureHeadLeaf.md`, the
archive manifest, and the independent `FixedReuseAudit.md`, then compared the
actual archived proof with the original historical source readback and build
output. The conclusion below is not inferred from those notes alone.
All following source line numbers refer to `Consumer.reconstructed.txt`.

## Source and execution cross-check

1. Lines 663–693 abbreviate `Head`; this carries the exact Value suffix,
   state/storage/ghost relations, return and allocation frames, pointer
   coverage, register preservation and return-PC facts. It is proof-local
   syntax, not a newly accepted semantic definition.
2. `fixed_init` ends at lines 1489–1531 by selecting
   `arr_base,dst,cc,Gentry,tnentry` at 1490, before introducing the arbitrary
   horizon `H'` at 1492. The actual entry path and post are specialized at
   that same horizon. No new execution is selected by the Head assembly.
3. Lines 1497–1514 transport storage and ghost gas-observation fields and
   derive literal taint, saved array-base lookup, dead-lo and return-PC facts.
   Lines 1515–1518 unfold Head locally and rewrite the generated index and
   memory-size identities. The conjunction solver at 1519–1529 tries the
   existing assumptions and small literal/length/transport/address arithmetic
   alternatives. Only its final alternative at 1530 is
   `capture_goal "head-leaf"` (with the original FAIL_TAC retained in a comment).
4. I compared this whole endpoint/Head span against original source readback
   `TO_statement_cases-L0016-20261116T200109121105Z_m1066_t002`.
   The selected tuple, horizon placement, transport facts, FIRST alternatives,
   fallback, QED, marker and following dynamic_init agree line-for-line.
5. Original build output
   `TO_statement_cases-L0016-20261116T193214352355Z_m1044_t001`
   reports failure in the **following** Resume `dynamic_init` (line 1535),
   specifically its MLOAD stage-equation by-proof at 1547–1550. The independent
   log query `TO_statement_cases-L0016-20261116T193214352355Z_m1045_t001`
   records `FIXED-INIT-AND-REDUCED-ASSEMBLY-CLOSED`, placed after fixed_init's
   QED at line 1533. Thus the executed fixed_init tactic chain completed
   without invoking its failing head fallback. No per-conjunct trace is
   available or claimed; I do not assign particular conjunction leaves to
   particular FIRST alternatives.

The later failing build is not a passing Consumer build or finalisation.
The reduced fixed-premise proof preceding 1489 is audited by its own owner;
this note neither duplicates it nor adds any premise to its use site.

## Distinct head and continuation paths not retired

- Lines 1803–1807 contain `common_cert_head`, a different Resume applying
  `gas_exempt_cert_error_bool`. Its presence is not evidence of an unresolved
  `head-leaf`, and this audit does not claim it was executed by the historical
  build, which stopped earlier in dynamic_init.
- `common_round` starts at 1815. At 1833–1841 it expands the actual Inv/Head
  hypothesis and specializes it at `storage_trace_horizon ee.storage_trace`
  with domain evidence. At 1842–1851 it derives the nonempty suffix index,
  rewrites the actual cons equality via MAP_EQ_CONS, and substitutes the
  Value head. This is retained source for reuse, not a request to reprove a
  Value-head lemma and not independently qualified runtime code.
- Lines 1984–2000 derive `body_stmts_full_ok` and apply the existing labelled
  `body_fragment` cut at the extended environment and actual scoped body
  state. That cut remains an assumed LocalContracts antecedent, not a supplier
  theorem established here. Lines 2001–2008 tie ordinary body compilation
  to sb1; `body-shadow-packet` at 2009 remains a distinct unfinished point.
- The explicit `initialized-loop-suffix`, `dynamic-entry-premises`, and
  `dynamic-entry-apply` captures at 2013, 2020 and 2024 are unchanged. This
  disposition neither removes those obligations nor supplies shadow code,
  an arbitrary code_ready witness, or an identification of ordinary and
  shadow states.

No additional unresolved head sequent was observed by this source/evidence
inspection. This is deliberately weaker than asserting none can appear in
future execution of the suspended/later branches.

## Effect on final Consumer assembly

C1.5.5.8 should reuse the actual retained fixed_init assembly, rather than
import an invented local_head_leaf lemma. It must reconstruct/reconcile the
archived Consumer, preserve all seven quotations and frozen headers, discharge
all real helper premises, and execute/build/audit the complete assembled
Consumer at project defaults. It must close every reachable unfinished point.
If this exposes a genuine head goal, print its exact typed context and request
a scoped PLAN refinement before proving a new helper. This audit grants no
Consumer, facade, or genuine-supplier completion credit.

## Evidence read in this lane

- TO_statement_cases-L0042-20261116T223716747514Z_m0004_t001: integrated producer disposition.
- TO_statement_cases-L0042-20261116T223716747514Z_m0004_t002: independent fixed reuse audit.
- TO_statement_cases-L0042-20261116T223716747514Z_m0005_t001: actual archived fixed Head assembly and next Resume.
- TO_statement_cases-L0042-20261116T223716747514Z_m0005_t002: separate common certificate/Value-head path.
- TO_statement_cases-L0042-20261116T223716747514Z_m0005_t003: actual body-fragment linkage and remaining capture points.
- TO_statement_cases-L0042-20261116T223716747514Z_m0005_t004: original post-QED marker readback.
- TO_statement_cases-L0042-20261116T223716747514Z_m0005_t005: original later dynamic_init failure readback.
- TO_statement_cases-L0042-20261116T223716747514Z_m0005_t006: current Git input identities.
- TO_statement_cases-L0042-20261116T223716747514Z_m0006_t001: full proof-local Head abbreviation.
- TO_statement_cases-L0042-20261116T223716747514Z_m0006_t002: original source readback for independent comparison.
- TO_statement_cases-L0042-20261116T223716747514Z_m0006_t003: integrated archival/replay boundaries.
