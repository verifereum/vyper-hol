Theory fnPlanLineageQuarantine
Ancestors
  fnPlanLineageInventory deepResidualBudget fnPlanLineageSetup fnPlanLineageCallers stackPlanGen venomInst
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

Theorem generate_inst_plan_jmp_stack_support:
  !lv dfg cfg fn inst next halt term cur ps targets ops qs x.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops lv fn cur inst = SOME targets /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs) /\
    MEM x qs.ps_stack ==>
    MEM x targets \/ MEM x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `?target. inst.inst_operands = [Label target]` by
    (gvs[join_target_ops_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def,
       venomInstTheory.is_param_opcode_def] >>
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, emit_input_plan_def,
       stackPlanTypesTheory.is_label_operand_def,
       venomEffectsTheory.is_commutative_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  Cases_on `restore_spilled_plan targets ps` >> simp[] >>
  rename1 `restore_spilled_plan targets ps = (rOps,psR)` >>
  Cases_on `reorder_plan dfg targets psR` >> simp[stackModelTheory.stack_pop_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `join_reached _ _ _ _ _` mp_tac >>
  simp[join_reached_def, generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, emit_input_plan_def,
       stackPlanTypesTheory.is_label_operand_def,
       venomEffectsTheory.is_commutative_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def,
       release_dead_spills_stack] >>
  strip_tac >> gvs[stackModelTheory.stack_pop_def, release_dead_spills_stack] >>
  irule restore_reorder_success_stack_support >>
  goal_assum (drule_at Any) >> simp[stackModelTheory.stack_pop_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem emit_one_input_stack_support:
  !opc nl op ps ops qs x.
    emit_one_input opc nl op ps = (ops,qs) /\ MEM x qs.ps_stack ==>
    x = op \/ MEM x ps.ps_stack
Proof
  rpt gen_tac >> simp[emit_one_input_def] >> pairarg_tac >> simp[] >>
  `!a. MEM a ps1.ps_stack ==> a = op \/ MEM a ps.ps_stack` by
    (Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)` >>
     gvs[] >> metis_tac[do_restore_stack_support]) >>
  Cases_on `op`
  >- (simp[stackModelTheory.stack_push_def] >> strip_tac >> gvs[] >> metis_tac[]) 
  >- (rename1 `Var name` >> Cases_on `MEM name nl` >> simp[] >>
      Cases_on `stack_get_depth (Var name) ps1.ps_stack` >> simp[] >>
      rpt strip_tac >> gvs[] >>
      drule stackModelTheory.stack_get_depth_props >> strip_tac >>
      drule doSwapSimTheory.do_dup_stack_exact >> strip_tac >>
      pairarg_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `opc = INVOKE` >> simp[stackModelTheory.stack_push_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem emit_input_plan_stack_support:
  !opc operands nl ps ops qs x.
    emit_input_plan opc operands nl ps = (ops,qs) /\ MEM x qs.ps_stack ==>
    MEM x operands \/ MEM x ps.ps_stack
Proof
  gen_tac >> Induct
  >- (simp[emit_input_plan_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> simp[emit_input_plan_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> disch_then drule >>
  metis_tac[emit_one_input_stack_support]
QED

Theorem popmany_plan_stack_support:
  !items ps ops qs x.
    popmany_plan items ps = (ops,qs) /\ MEM x qs.ps_stack ==>
    MEM x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  drule popmany_plan_resource_nonincrease >>
  disch_then (qspec_then `x` mp_tac) >>
  `qs.ps_spilled = ps.ps_spilled` by
    (qspecl_then [`items`, `ps`] mp_tac popmany_plan_spilled_unchanged >> simp[]) >>
  simp[] >> strip_tac >>
  gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]
QED

Theorem regular_post_emit_tail_stack_support:
  !outputs nl halt dfg inst term ps ps8 ps9 qs x.
    ps8 = (if outputs <> [] /\ (~halt \/ LENGTH outputs > 1)
      then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps)
      else ps) /\
    ps9 = (if outputs <> [] /\ FILTER (\v. MEM v nl) outputs <> []
      then SND (optimistic_swap_plan dfg inst nl term ps8) else ps8) /\
    qs = release_dead_spills nl ps9 /\ MEM x qs.ps_stack ==>
    MEM x ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `MEM x ps9.ps_stack` by gvs[release_dead_spills_stack] >>
  `MEM x ps8.ps_stack` by
    (Cases_on `outputs <> [] /\ FILTER (\v. MEM v nl) outputs <> []` >> gvs[] >>
     metis_tac[SRULE [pred_setTheory.EXTENSION] optimistic_swap_plan_slots]) >>
  Cases_on `outputs <> [] /\ (~halt \/ LENGTH outputs > 1)` >> gvs[] >>
  Cases_on `popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps` >>
  gvs[] >> metis_tac[popmany_plan_stack_support]
QED

Theorem native_regular_stack_support:
  !lv dfg cfg fn inst nl halt term lbl ps ops qs v.
    (inst.inst_opcode <> JMP \/ join_target_ops lv fn lbl inst = NONE) /\
    LENGTH (compute_operands inst) <= 16 /\
    generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps = (ops,qs) /\
    MEM (Var v) qs.ps_stack ==>
    MEM (Var v) ps.ps_stack \/ MEM (Var v) (compute_operands inst) \/
    MEM v inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  (drule_at (Pos last) native_regular_stages >>
  (impl_tac >- simp[]) >> strip_tac >>
  `MEM (Var v) ps7.ps_stack` by
    metis_tac[regular_post_emit_tail_stack_support] >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >>
  disch_then (strip_assume_tac o SRULE [parameter_push_fold]) >>
  `MEM (Var v) ps4.ps_stack \/ MEM v inst.inst_outputs` by
    (gvs[stackModelTheory.stack_pop_def, listTheory.MEM_MAP] >>
     metis_tac[rich_listTheory.MEM_TAKE]) >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `MEM (Var v) selected \/ MEM (Var v) ps1.ps_stack \/ MEM v inst.inst_outputs` by
    (Cases_on `MEM v inst.inst_outputs` >- simp[] >> gvs[] >>
     drule_at (Pos (el 2)) reorder_plan_stack_support >>
     disch_then (qspec_then `Var v` mp_tac) >> simp[]) >>
  metis_tac[emit_input_plan_stack_support, sortingTheory.PERM_MEM_EQ])
QED

Theorem phi_declared_output_stack_support:
  !inst nl halt ps ops qs v.
    inst.inst_outputs <> [] /\
    generate_phi_plan inst nl halt ps = (ops,qs) /\
    MEM (Var v) qs.ps_stack ==>
    MEM (Var v) ps.ps_stack \/ MEM v inst.inst_outputs
Proof
  rpt gen_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- (simp[generate_phi_plan_def] >> metis_tac[]) >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  `d < LENGTH ps.ps_stack` by
    (fs[stackModelTheory.stack_get_phi_depth_def] >>
     drule planWfTheory.stack_find_bound >> simp[]) >>
  Cases_on `inst.inst_outputs` >- simp[] >>
  Cases_on `do_dup d ps` >>
  rename1 `do_dup d ps = (dops,ds)` >>
  `ds.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
    (drule doSwapSimTheory.do_dup_stack_exact >> simp[]) >>
  `!x. MEM x ds.ps_stack ==> MEM x ps.ps_stack` by
    (gvs[stackModelTheory.stack_peek_def] >>
     `LENGTH ps.ps_stack - (d + 1) < LENGTH ps.ps_stack` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  simp[generate_phi_plan_def] >>
  IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule_all popmany_plan_stack_support >> simp[] >>
      strip_tac >> drule stack_poke_mem_subset_nb >> simp[] >> metis_tac[])
  >- (strip_tac >> gvs[] >>
      drule stack_poke_mem_subset_nb >> simp[] >> metis_tac[])
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule_all popmany_plan_stack_support >> simp[] >>
      strip_tac >> drule stack_poke_mem_subset_nb >> simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  drule stack_poke_mem_subset_nb >> simp[] >> metis_tac[]
QED

Theorem wellformed_jmp_outputs_empty:
  inst_wf inst /\ inst.inst_opcode = JMP ==> inst.inst_outputs = []
Proof
  strip_tac >> gvs[venomWfTheory.inst_wf_def]
QED

Theorem native_special_stack_support:
  !lv dfg cfg fn inst nl halt term lbl ps ops qs v.
    inst_wf inst /\
    (inst.inst_opcode = PHI \/ inst.inst_opcode = OFFSET \/
     is_param_opcode inst.inst_opcode \/ inst.inst_opcode = NOP) /\
    generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
    MEM (Var v) qs.ps_stack ==>
    MEM (Var v) ps.ps_stack \/ MEM v inst.inst_outputs
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (strip_tac >> `inst.inst_outputs <> []` by
        (gvs[venomWfTheory.inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[]) >>
      gvs[generate_inst_plan_def, AllCaseEqs()] >>
      metis_tac[phi_declared_output_stack_support]) >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (strip_tac >> gvs[generate_inst_plan_def, AllCaseEqs()] >>
      metis_tac[offset_declared_output_stack_support]) >>
  strip_tac >> gvs[generate_inst_plan_def, AllCaseEqs()]
QED

Theorem native_inst_stack_quarantine:
  !lv dfg cfg fn inst nl halt term lbl ps ops qs v.
    inst_wf inst /\ codegen_ready_inst inst /\
    generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
    ~MEM (Var v) ps.ps_stack /\ ~MEM (Var v) inst.inst_operands /\
    ~MEM v inst.inst_outputs /\
    (!targets. inst.inst_opcode = JMP /\
      join_target_ops lv fn lbl inst = SOME targets ==> ~MEM (Var v) targets) ==>
    ~MEM (Var v) qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI \/ inst.inst_opcode = OFFSET \/
    is_param_opcode inst.inst_opcode \/ inst.inst_opcode = NOP`
  >- metis_tac[native_special_stack_support] >>
  `~MEM (Var v) (compute_operands inst)` by
    (strip_tac >> drule fnPlanLineageCallersTheory.compute_operands_inst_uses >>
     gvs[venomInstTheory.inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  Cases_on `inst.inst_opcode = JMP /\ join_target_ops lv fn lbl inst <> NONE`
  >- (gvs[] >> Cases_on `join_target_ops lv fn lbl inst` >> gvs[] >>
      drule_all wellformed_jmp_outputs_empty >> strip_tac >>
      metis_tac[generate_inst_plan_jmp_stack_support]) >>
  `LENGTH (compute_operands inst) <= 16` by
    metis_tac[ready_non_phi_operand_bound] >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps = (ops,qs)` by
    gvs[generate_inst_plan_def, AllCaseEqs()] >>
  metis_tac[native_regular_stack_support]
QED

Theorem native_regular_inst_physical_reset:
  !lv dfg cfg fn inst nl halt term lbl ps ops qs v.
    inst_wf inst /\ codegen_ready_inst inst /\
    generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
    ~MEM (Var v) ps.ps_stack /\ ~MEM (Var v) inst.inst_operands /\
    ~MEM v inst.inst_outputs /\
    (!targets. inst.inst_opcode = JMP /\
      join_target_ops lv fn lbl inst = SOME targets ==> ~MEM (Var v) targets) /\
    ~MEM v nl /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> OFFSET /\
    ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> NOP ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[native_inst_stack_quarantine] >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps = (ops,qs)` by
    gvs[generate_inst_plan_def, AllCaseEqs()] >>
  metis_tac[native_regular_spilled_live_upper]
QED
