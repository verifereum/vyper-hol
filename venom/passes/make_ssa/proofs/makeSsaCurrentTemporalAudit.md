# Chronological readiness audit (C1.12.edge.temporal_audit)

This is a diagnostic, not a proved simulation, new HOL definition, or counterexample to the frozen contracts. No accepted theory is changed. The proposed relation below is not authorized for production use until its edge and cleanup clauses have been proved.

## 1. Actual induction domain

Use `current_actual_prefix` and `current_execution_edge` in
`makeSsaCurrentExecutionHistoryScript.sml:51-100`, not
`current_completed_blocks` as the source execution relation. The latter
(`makeSsaCurrentDefinedScript.sml:83-90`) calls `exec_block` at index zero
without the parallel `eval_phis` dispatch. There is no established conversion
of an actual PHI-containing run into that relation.

Induct on the derivation of the finite source prefix (equivalently its list
of actual execution edges, NOT the static dominator event list). Entry at
`CurrentEntry (SUC f)` evaluates the fixed incoming snapshot's whole PHI
batch, then sets the index to `phi_prefix_length`. Body nonterminators
execute `step_inst f ctx inst` and increment the index. Body terminators
produce either termination or `CurrentEntry f`. These are the actual
`run_defs` recurrences (`venomExecSemanticsScript.sml:1663-1723`). The
existing edge relation excludes INVOKE; recursive calls remain the separate
PLAN consumer and must not be claimed covered by this induction.

The induction conclusion constructs an existential target prefix and final
state. Target execution is NOT a premise on a source-prefix constructor.
Target cleanup uses extra steps; no equal instruction-count/fuel assertion
is intended here.

## 2. One candidate invariant (schematic HOL signatures)

All symbols introduced in this section are proposed abbreviations, not
existing constants. Quantification is explicit:

    !s fn fn' s' A H events ctx ctx' seed seed' f phases loc result st.
      current_structural_certificate s fn fn' s' A H events /\
      FrozenPremises s fn /\ InitialSeed fn H seed seed' /\
      current_actual_prefix fn ctx (CurrentEntry f) seed
        phases (SOME loc) result st ==>
      ?target_phases target_loc target_result st'.
        current_actual_prefix fn' ctx' (CurrentEntry target_fuel) seed'
          target_phases (SOME target_loc) target_result st' /\
        AlignedValueCut fn fn' H events loc target_loc st st'

Here target_fuel must itself be existentially quantified, or chosen by the
later finite-run consumer; it is not a free hidden parameter. `FrozenPremises`
means exactly the source hypotheses of the task, not additional validity
assumptions. The bounded non-INVOKE version uses the same context and leaves
calls out explicitly.

At a completed ordinary cut `(l,i)` the proposed `AlignedValueCut` is:

* equality of `execution_frame`, current label and previous label; indices
  are related by actual phase alignment, not equality;
* `!v. current_demand fn v l i ==> lookup_var v st =
  lookup_var (latest_current_name (Selector l i) v) st'`;
* `current_singleton_agree (current_instruction_singleton_table fn H) st st'`;
* for each collapsed inserted copy `x <- y` relevant to demand under the
  current selector, target lookup at x equals lookup at y **only after that
  copy has executed**. Before its execution one instead needs a proof that
  lookup y is the current source owner value. Equality after a prior visit
  is not sufficient. No blanket pre-batch selected-self equality is claimed.

`Selector` is the certificate's actual per-cut renaming selector. At a
predecessor exit it is exactly `current_event_exit_rs ev`, where
`MEM ev events /\ current_event_label ev = p`. A static event is reused
on each dynamic visit but the states in this invariant are the current
visit's stores. `InitialSeed` supplies related initial stores/frames and
empty/fresh singleton bindings at the actual entry; initialization must
prove this from the contract's initial-state interface, not assume arbitrary
stores agree on future allocated names.

No origin maps are needed to state this value invariant. Origins in
`current_joint_rel` are a stronger implementation interface; obtaining
matching origin maps is a separate premise of OrdinaryJoint, not a theorem
that follows merely from the value clauses above.

## 3. Entry and successor checks

### Entry

`first_block_no_phi` removes the source entry batch, and
`first_block_no_preds` prevents an inserted entry merge. Need prove the
certificate selector is the initial spelling for demands and that fresh
canonical singleton names have the matching empty lookup before definition.
Neither a future successful cleanup nor target PHI availability is allowed
in the seed. The audit has not proved entry initialization for arbitrary
contract initial states.

### Ordinary step

Backward demand closure gives the input set
`operand_vars inst.inst_operands ++ current_before_outputs inst.inst_outputs D`
for a desired successor demand set D. `current_demand` has ordinary, skip,
edge and cross constructors (`makeSsaCurrentDemandScript.sml:10-36`).
For variables not written, lookups persist. For outputs, aligned indexed
writes update both stores; repeated output slots must use the last dynamic
write, not the first static token. Singleton bindings refresh on every
execution of their unique defining instruction and persist between visits.

The exact existing stronger interface is
`current_inst_trace_ordinary_joint` (OrdinaryJoint:37-55): besides allocation,
annotation and environment hypotheses and `D SUBSET U` expressed with MEM,
it assumes `current_joint_rel V M N rs
 (operand_vars inst.inst_operands ++ current_before_outputs inst.inst_outputs D)
 st st'` and a successful source `step_inst_base`. It produces target success,
paired indexed writes and joint relation at rt D. It does NOT discharge the
incoming joint relation from a value-only invariant. No unconditional
ordinary source-to-target theorem is inferred here.

### Control edge / pre-batch (first unresolved edge clause)

Let h be the actual successor of predecessor p, pred its source block,
ev its certificate event, out the target h block, and target_phis its
leading PHIs. Required, with ALL displayed variables universally bound:

    !s fn fn' s' A H events p h pred out ev target_phis target_tail st st' v n.
      current_structural_certificate s fn fn' s' A H events /\
      FrozenPremises s fn /\
      lookup_block p fn.fn_blocks = SOME pred /\ fn_cfg_edge fn p h /\
      MEM ev events /\ current_event_label ev = p /\
      lookup_block h fn'.fn_blocks = SOME out /\
      out.bb_instructions = target_phis ++ target_tail /\
      EVERY (\j. j.inst_opcode = PHI) target_phis /\
      (target_tail = [] \/ (HD target_tail).inst_opcode <> PHI) /\
      current_actual_inserted fn v h /\
      current_token_name H (CurrentInserted v h) = SOME n /\
      MEM n (FLAT (MAP (\j. j.inst_outputs) target_phis)) ==>
      current_demand fn v p (LENGTH pred.bb_instructions)

This is a proposed static *surviving insertion demand* lemma, not an
existing theorem. With the demanded exit value clause its conclusion gives
exactly `current_name_agree (current_event_exit_rs ev) [v] st st'`.
To obtain the OTHER required conjunct, the actual source-prefix induction
must prove a separate runtime interpretation:

    !fn ctx loc0 seed phases loc result st v p pred.
      ActualEntrySeed fn loc0 seed /\ FrozenSourcePremises fn /\
      current_actual_prefix fn ctx loc0 seed phases (SOME loc) result st /\
      CompletedPredecessorExit loc p pred st /\
      current_available fn v p (LENGTH pred.bb_instructions) ==>
      ?value. lookup_var v st = SOME value

`CompletedPredecessorExit` must denote an actually executed terminator exit,
not merely `vs_current_bb = p` (a branch already changes that label).
This requires a PHI-aware executed-definition/FDOM monotonicity induction.
`current_available` alone quantifies CFG paths, not stores (Availability:7-18).

Does ordinary demand already include the insertions? Not directly from
its constructors. Placement implies selected liveness at the destination
post-PHI cut. Demand's `cross` constructor requires demand at destination
index ZERO. Moving a post-PHI demand to zero is blocked by definitions in
that batch. The Python liveness transport also has an operand exclusion:
`current_live_cut_to_pred_exit` (LiveTransport:61-71) requires BOTH no
leading definition of v and no occurrence of v in ANY leading PHI pair.
Neither exclusion is supplied by `current_actual_inserted` (PlacementCut:7-15).
A same-header reinserted original output must first be shown to collapse
and hence not be among target_phis. An operand-singleton exception needs
its own canonical-name/selector bridge (singleton equality by itself is not
the demanded exit-selector equality). Thus analysis validity does not yet
establish the proposed inclusion by the existing transport lemma.

This static surviving-insertion demand implication is the earliest missing
interface *in the edge proof*, even granting entry and ordinary preservation.
It must be resolved before implementing a chronological readiness theorem.
The runtime implication above is a second, distinct obligation; proving
static inclusion alone cannot produce SOME rather than NONE = NONE.

### Parallel batch

Once the exact incoming premise is established,
`current_certificate_mixed_batch_ready` (MixedBatchReady:109-134) gives
`?post'. eval_phis st' target_phis = OK post' /\ singleton_agreement post post'`.
Its incoming premise is, verbatim,

    !v n. current_actual_inserted fn v h /\
      current_token_name H (CurrentInserted v h) = SOME n /\
      MEM n (FLAT (MAP (\j. j.inst_outputs) target_phis)) ==>
      current_name_agree (current_event_exit_rs ev) [v] st st' /\
      ?value. lookup_var v st = SOME value

Original retained PHIs use incoming singleton operand bindings and evaluate
against fixed snapshots; new PHIs use this demand clause. Batch readiness
and singleton persistence do NOT conclude full demanded post-PHI equality.
The retained batch and inserted batch output values must additionally be
connected to the destination selector.

### Sequential cleanup, before ordinary tail

After the parallel batch, target retained originals are already defined.
For each cleanup instruction in order:

* NOP: `current_cleanup_nop_step` leaves the store unchanged. A demanded
  selected name whose PHI becomes NOP needs proof it was not needed, or a
  prior dynamic binding with the right value; NOP itself proves neither.
* ASSIGN `[Var y] [x]`: `current_cleanup_assign_step` is an exact lookup
  case (CleanupRuntime:20-29). Need `lookup_var y evolving_target = SOME a`
  and `lookup_var owner source_post = SOME a` BEFORE the copy. Then x
  acquires the desired equality. Subsequent distinct outputs preserve it.
* Same-header reinsertion copy: y is the retained original output, so the
  retained batch supplies its binding, before sequential copies start.
* Selected-self collapsed insertion on a loop: equality x = y established
  on an earlier visit is not enough; a body definition may have changed
  the owner. Need last-write/nonclobber plus entry-edge selector reasoning
  to show the current y carries this visit's owner value. Static equality
  of tokens cannot discharge that premise.

The generic cleanup frame and untouched-name lemmas
(CleanupRuntime:56-98) are conditional on success. They cannot establish the
missing pre-copy lookup. Names not written in batch/copies persist;
inserted names written in the batch require incoming value reasoning;
canonical original singleton names must be proved excluded from cleanup
outputs. Only after the last copy may the ordinary-cut invariant be asserted.

## 4. Definedness interface warning and conclusion

`current_source_phi_edge_defined` (SourcePhiRuntime:15-26) and
`current_all_paths_endpoint_binding` (Defined:158-164) use
`current_completed_blocks`. Their statements are checked facts about that
relation, but do not bridge actual parallel-PHI source prefixes. In
particular source success on an ordinary instruction does not imply that
an unrelated inserted-PHI owner has already been defined. Do not reuse these
lemmas by silently identifying the two prefix relations.

Deliverable result: one candidate induction is specified and tested through
all phase cuts; it is not yet verified. The first edge gap is the displayed
surviving-insertion demand inclusion (with an actual-prefix definedness
bridge also needed). Full demanded restoration after selected-self cleanup
remains unverified. No counterexample to either frozen theorem is claimed.
The next strategist decision should validate/repair that exact inclusion
and the PHI-aware runtime bridge, rather than add another theorem assuming
incoming readiness or target cleanup success.
