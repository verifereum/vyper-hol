# Finite closure: generalization boundary audit

The finite experiment is complete, not a general MakeSSA simulation. Accepted
source: makeSsaCurrentFinite{History,Tables,Transfer,Availability}Script.sml.
No theorem is asserted by this note. All candidate formulas below are UNPROVED
unless a precise existing theorem is named.

## Premise inventory

1. **Independent graph and seeds.** `current_finite_edge fn fn' c d k` is
   membership of both cuts in `current_finite_cuts fn fn'` AND
   `current_static_edge fn fn' c d k`. `current_finite_contexts` substitutes
   `[""]` at entry; other contexts come from `current_pred_map`. Dispatch
   uses indices 0/0, cleanup uses fixed source prefix length and incrementing
   target indices, body increments both indices, CFG transfer uses block end.
   These are syntactic definitions, not operational coverage theorems.
   `current_finite_edges_exact` is general but only equates the quadratic
   enumerator with that already restricted edge relation. Fixture sparse
   coverage (`current_loop_sparse_coverage`, `current_backedges_sparse_coverage`)
   does NOT prove successful executions remain in this graph.
   Missing general facts: predecessor map completeness for actual transferred
   labels at this interface; paired source/target phase alignment at all cuts;
   representation of every successful CFG step including re-entry. Errors,
   returns and calls need separate interpreter cases, not extra CFG edges.

2. **Entry predecessor canonicalization.** `current_finite_probe_entry_batches`
   checks empty source and target batches for the two fixtures, independently
   of `p`. General use needs both entry batches PHI-free, and an explicit
   argument that replacing runtime predecessor text by "" does not change
   dispatch substitution or seed/edge behavior. `first_block_no_phi fn`
   addresses the input only; do not silently infer target entry behavior or
   syntactic equality of runtime and canonical cuts from it.

3. **Ordinary suffix alignment.** `current_finite_probe_alignment` checks
   `current_finite_alignment` for the two fixtures: opcodes and operand/output
   arities agree along the entire suffix, not just a truncated ZIP.
   General `current_cleanup_if_ordinary_index` (CleanupShape, lines 151-158)
   assumes lookup of a precleanup block `bb`, its decomposition `pre ++ tail`,
   EVERY PHI pre, maximality of pre, and `i < LENGTH tail`. It yields lookup
   after optional cleanup, equal block length, and equality of
   `current_inst_no_id (EL (LENGTH pre+i) ...)` with the old tail instruction.
   Thus cleanup preserves the ordinary suffix once its boundary is known.
   Missing here: deriving `current_static_body_start` and full LIST_REL
   alignment from the actual structural certificate, insertion and renaming.
   No existing finite alignment computation discharges that compiler theorem.

4. **History/ownership versus selectors.** General
   `current_provenance_tree_ownership` (ActualRetention, lines 521-533)
   assumes paired old/inserted blocks with block provenance, distinct flattened
   annotation tokens, supply coverage, distinct dom-tree labels, and a genuine
   current_tree_trace initialized at empty history/CurrentDefault. It concludes
   history validity and exit owner names for event variables. The actual
   finite histories have been bound to those traces. This establishes names,
   not availability of their values, and does not relate every incoming
   selector to the matching source operand at every operational cut.
   `current_static_owner` deliberately uses provenance, not name spelling.
   General seed-owner completeness and edge-selected operand correspondence
   remain obligations at the static-demand interface.

5. **Backward closure and producer compatibility.** General
   `current_finite_table_contains` takes seed containment and read/read
   pullback closure, and proves finite-demand containment by rule induction.
   General `current_table_safe_edges_sound` takes safe table rows and coverage
   of finite edges, and classifies each demanded pullback as two reads or
   equal-index Produced markers. `current_table_entry_sound` similarly takes
   an entry table check. Their premises are computed only for the fixtures.
   Required compiler-wide candidate shape (UNPROVED):

       current_finite_edge fn fn' c d k /\
       current_finite_demand fn fn' H d x y ==>
       ?a b. current_static_back fn fn' c k x y a b /\
         ((?u v. a = CurrentStaticRead u /\ b = CurrentStaticRead v) \/
          (?i. a = CurrentStaticProduced i /\ b = CurrentStaticProduced i))

   This needs the real compiler certificate and frozen input premises, not
   an assumption named transfer_safe. Equal Produced indices additionally
   need semantic equal-output values under paired successful instruction
   execution; marker equality alone does not establish them. A candidate
   entry property is demand at `CurrentStaticCut "" entry 0 0 ==> x = y`.
   Neither follows merely by induction on demand: induction also needs
   backward propagation to respect the compiler's renaming/placement invariant.

6. **Unary existence.** FiniteAvailability checks empty entry, every finite
   edge `D(d) subset D(c) union current_source_completed fn c k`, and
   `current_finite_seed ... c (Var v) y /\ current_extra_read_cut ... c ==>
   MEM v (D c)` for the fixtures. Cleanup and CFG edges add no source outputs;
   source leading PHI outputs are added atomically at dispatch. Selected PHI
   reads are checked at incoming 0/0, not after that dispatch.
   General availability may use already proved `current_available fn v h i`
   (all entry-to-h paths have a prior definition). It must establish source
   existence only for extra reads; ordinary paired instructions can fail.
   `current_actual_prefix_body_available` (ActualAvailable, lines 53-60)
   takes wf_function, fn_inst_wf, fn_entry_state, an actual prefix ending at
   CurrentBody fuel bb, and current_available at its current block/index;
   it gives `?value. lookup_var v before = SOME value`.
   It does not prove static availability for any compiler extra seed.
   `current_actual_exit_demand_defined` handles predecessor exit with a
   successful terminator and current_demand; it is not a general paired demand
   or a proof of cleanup seed availability.

## Smallest proposed semantic bridge (UNPROVED here)

Before a whole operational induction, the batch source-definedness bridge can
be stated without a compiler certificate, target state, or readiness premise:

    lookup_block h fn.fn_blocks = SOME old /\
    eval_phis st old.bb_instructions = OK post /\
    (!v. MEM v (D (CurrentStaticCut p h 0 0)) ==>
         v IN FDOM st.vs_vars) /\
    current_availability_row fn D
      (CurrentStaticCut p h 0 0) d 0 ==>
    !v. MEM v (D d) ==> v IN FDOM post.vs_vars

This is a one-step boundary, no new runtime induction: expand only the row and
completed-output definitions, use lookup equality and MEM_FLAT/MEM_MAP, then
`current_eval_phis_domain` and `current_eval_phis_outputs` from ActualDefined.
Their verified signatures are respectively `eval_phis st insts = OK post ==>
FDOM st.vs_vars SUBSET FDOM post.vs_vars`, and successful eval plus membership
of inst in TAKE(phi_prefix_length insts) insts plus membership in inst outputs
implies output membership in FDOM post.vs_vars. Hence syntactic completion is
converted to existence only after successful source batch evaluation.
An ordinary-step analogue needs opcode/result-sensitive output and domain
preservation; do not assume every successful control/return constructor is an
OK ordinary write. This small bridge does not resolve graph coverage or the
compiler-wide extra-seed availability theorem.

## Owning-ancestor decision still required

The finite experiment supports separating paired equality from unary existence.
The unresolved general invariant is: compiler-derived backward demands are
compatible with allocation/edge renaming at every aligned phase, and every
extra seed has a prior source definition at its actual incoming or cleanup cut.
No further fixtures or conditional replay wrappers can discharge that invariant.
The strategist must choose a general placement/renaming invariant and graph
coverage proof before global fuel/operational induction. Existing
`current_certificate_mixed_dispatch_continue` explicitly assumes inserted
incoming name agreement AND a source lookup witness (CompletedBatch lines
116-120); it cannot generate these missing premises from itself.
