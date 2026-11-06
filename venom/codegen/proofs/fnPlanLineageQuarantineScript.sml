Theory fnPlanLineageQuarantine
Ancestors
  fnPlanLineageInventory fnPlanLineageSetup stackPlanGen venomInst
Libs wordsLib

(* The unrestricted dispatcher probe admits malformed instructions. OFFSET
   reads HD outputs even when outputs=[], so the requested-name exclusions
   alone do not ensure stack non-recreation. This is not a ready-program
   counterexample and says nothing about the frozen lineage theorem. *)
Theorem native_quarantine_offset_empty_outputs_obstruction:
  ~MEM (Var (HD ([] : string list))) (init_plan_state 0).ps_stack /\
  ~MEM (Var (HD ([] : string list)))
    (mk_inst 0 OFFSET [Lit 0w; Label "L"] []).inst_operands /\
  ~MEM (HD ([] : string list))
    (mk_inst 0 OFFSET [Lit 0w; Label "L"] []).inst_outputs /\
  (!targets. (mk_inst 0 OFFSET [Lit 0w; Label "L"] []).inst_opcode = JMP /\
    join_target_ops lv fn lbl (mk_inst 0 OFFSET [Lit 0w; Label "L"] []) =
      SOME targets ==> ~MEM (Var (HD ([] : string list))) targets) /\
  generate_inst_plan lv dfg cfg fn
    (mk_inst 0 OFFSET [Lit 0w; Label "L"] []) nl halt term lbl
    (init_plan_state 0) =
    SOME ([SOPushOfst "L" 0],
      (init_plan_state 0) with ps_stack := [Var (HD ([] : string list))]) /\
  MEM (Var (HD ([] : string list))) [Var (HD ([] : string list))]
Proof
  EVAL_TAC >> simp[]
QED

Theorem ready_member_instruction_shape:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions ==> inst_wf inst /\ codegen_ready_inst inst
Proof
  simp[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def,
    listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ready_non_phi_operand_bound:
  codegen_ready_inst inst /\ inst.inst_opcode <> PHI ==>
  LENGTH (compute_operands inst) <= 16
Proof
  simp[codegen_ready_inst_def]
QED

Theorem offset_declared_output_stack_support:
  inst_wf inst /\ inst.inst_opcode = OFFSET /\
  generate_offset_plan inst ps = (ops,qs) /\ MEM (Var v) qs.ps_stack ==>
  MEM (Var v) ps.ps_stack \/ MEM v inst.inst_outputs
Proof
  strip_tac >> drule_all venomWfTheory.inst_wf_offset_shape >> strip_tac >>
  gvs[generate_offset_plan_def, stackModelTheory.stack_push_def]
QED

(* Reorder-bound probes are arbitrary native states, not reachable fixtures.
   The unrelated b spill is deliberately retained. *)
Definition quarantine_short_state_def:
  quarantine_short_state = (init_plan_state 0) with
    <| ps_stack := [Var "a"]; ps_spilled := FEMPTY |+ (Var "b", 0) |>
End

Theorem quarantine_short_reorder:
  (SND (reorder_plan dfg_empty (REPLICATE 3 (Var "a"))
    quarantine_short_state)).ps_stack = [Var "a"] /\
  (SND (reorder_plan dfg_empty (REPLICATE 3 (Var "a"))
    quarantine_short_state)).ps_spilled = quarantine_short_state.ps_spilled
Proof
  EVAL_TAC
QED

Theorem quarantine_deep_reorder_one:
  (SND (reorder_one dfg_empty (REPLICATE 18 (Var "a")) 0 (Var "a")
    quarantine_short_state)).ps_stack =
      MAP (\n. EL n ([] : operand list))
        [16;0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15] ++ [Var "a"] /\
  (SND (reorder_one dfg_empty (REPLICATE 18 (Var "a")) 0 (Var "a")
    quarantine_short_state)).ps_spilled = quarantine_short_state.ps_spilled
Proof
  EVAL_TAC
QED

Theorem quarantine_missing_deep_targets:
  (SND (reorder_plan dfg_empty (REPLICATE 18 (Var "missing"))
    quarantine_short_state)).ps_stack = [Var "a"]
Proof
  EVAL_TAC
QED

Theorem quarantine_missing_join_rejected:
  join_target_ops lv fn lbl inst = SOME (REPLICATE 18 (Var "missing")) ==>
  ~join_reached lv fn lbl inst quarantine_short_state
Proof
  simp[join_reached_def, quarantine_short_state_def,
    stackModelTheory.stack_pop_def] >> EVAL_TAC
QED

(* Native reorder call-site safety table (C3.gate.reorder_audit).

   ordinary       ready_non_phi_operand_bound gives n<=16, so final_dist
                  is <=15 for every indexed target. A found dist is an
                  actual stack index. do_swap_safe_stack_support explicitly
                  permits d<=16 OR d<height; an undersized stack does not
                  invalidate the first disjunct. quarantine_short_reorder
                  checks the saturated-index behavior with an unrelated
                  stale spill. Thus the existing LENGTH tops<=height support
                  theorem is unnecessarily strong for this call site.
   commutative    Both dry-run lists have the same n<=16; swapped exchanges
                  only the last two entries when n>=2. Either cost-selected
                  result has the same target support. No independent source
                  of new operand names is introduced by choosing a result.
   JMP join       A separate restore_spilled_plan/reorder_plan stage targets
                  input_vars_from, with no <=16 bound. The existing budget
                  n<=height+CARD(set targets INTER FDOM spilled) suffices,
                  by restore_reorder_stack_support. It is NOT a consequence
                  of readiness's ordinary compute_operands bound (JMP's
                  ordinary operand list excludes its label).

   The exact checked quarantine_deep_reorder_one equation shows the unsafe
   long fallback: final_dist=17 on a singleton stack produces out-of-range
   EL n [] operands, not a permutation. These are opaque HOL operands; the
   theorem does NOT show that any is an unrequested Var, or certify a native
   dispatcher mismatch. In particular EL n [] is not uniformly HD []; a
   trial such simplification failed and was removed. The distinct-index
   terms are retained exactly in the checked equation.

   quarantine_missing_deep_targets checks a complete long reorder with no
   requested names available: it is identity, despite an unrelated spill.
   quarantine_missing_join_rejected separately checks that join_reached
   rejects that resulting short stack. In the unsafe long fallback case,
   the opaque operands prevent a concrete support-violation claim, so there
   is no established introduced-Var example to test through dispatcher
   filtering. Successful join_reached certifies a final suffix only, not
   the safety of earlier EL indices or exclusion of an earlier phantom
   from a residual prefix. No success-filter safety theorem is inferred.

   Smallest justified candidate boundary for strategist review:
   Generalize request-sensitive reorder support to the alternative
     LENGTH tops<=17 OR LENGTH tops<=LENGTH incoming.ps_stack,
   using the existing small-swap/valid-index support at every iteration;
   retain the restoration support premise for names requested. For long
   join lists retain the existing explicit materialisation budget unless
   an actual native producer or successful-result support argument proves
   it unnecessary. The alternatives and their derivability are NOT newly
   proved here. No operand availability/global U premise has been assumed.
   Next action is review, not an unrestricted dispatcher proof.
*)
