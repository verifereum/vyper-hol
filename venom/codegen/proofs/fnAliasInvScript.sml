(*
 * The cross-block DFG alias invariant of the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation.
 *
 * gen_fn_frame_simulation assumes that every operand on the planner's
 * stack or in its spill map has the value of its ASSIGN-chain root
 * (normalize_operand), read through the frame view.  The planner's
 * alias-only reorder steps rely on it.  The induction must re-establish
 * it at the successor block, whose lineage state carries the stack and
 * spill map the current block's code leaves (fnPlanLineage).
 *
 * TOP-LEVEL:
 *   lineage_alias_successor — CHEATED: one block preserves the invariant
 *)

Theory fnAliasInv
Ancestors
  fnPlanLineage frameRel codegenRel unitShapeDefs stackPlanGen stackPlanTypes
  venomExecSemantics venomState livenessDefs dfgDefs cfgDefs
  fnAliasInvOrdering fnAliasInvAvailability dfgAnalysisProps allocaRemapSSA
  venomInst venomInstProps venomWf venomExecProps venomExecProofs list rich_list stackModel
  stackPlanOps reorderSim sorting genericInputReady cleanOpsSim
  fnFrameBoundaryEntryParams joinSpillWitness frameViewFacts instSimHelpers

(* A final successful JMP checks its target suffix; block finalization leaves
   that checked state unchanged.  No coverage assumption on entry is needed. *)
Theorem alias_jmp_plan_join_reached:
  inst.inst_opcode = JMP /\
  generate_inst_plan liveness dfg cfg fn inst live halting next_term lbl ps =
    SOME (ops, ps') ==>
  join_reached liveness fn lbl inst ps'
Proof
  strip_tac >>
  gvs[generate_inst_plan_def, is_param_opcode_def, AllCaseEqs()]
QED

Theorem alias_block_insts_final_jmp_join_reached:
  !prefix i ps ops ps'.
  inst.inst_opcode = JMP /\
  generate_block_insts_plan liveness dfg cfg fn lbl halting np blen i
    (prefix ++ [inst]) ps = SOME (ops, ps') ==>
  join_reached liveness fn lbl inst ps'
Proof
  Induct >> simp[Once generate_block_insts_plan_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> strip_tac
  >- (gvs[generate_block_insts_plan_def] >>
      drule_all alias_jmp_plan_join_reached >> simp[]) >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem alias_block_plan_final_jmp_inputs:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  non_param_insts bb = prefix ++ [inst] /\
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
  lookup_block target fn.fn_blocks = SOME target_bb /\
  MEM v (input_vars_from bb.bb_label target_bb.bb_instructions
    (live_vars_at liveness target 0)) ==>
  MEM (Var v) ps'.ps_stack
Proof
  simp[generate_block_plan_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all alias_block_insts_final_jmp_join_reached >>
  simp[join_reached_def, join_target_ops_def] >> strip_tac >>
  qpat_x_assum `_ ++ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  simp[MEM_MAP]
QED

Theorem alias_ready_entry_no_preds:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME lbl ==>
  cfg_preds_of (cfg_analyze fn) lbl = []
Proof
  simp[codegen_ready_fn_def, block_entries_ready_def, fn_entry_label_def] >>
  Cases_on `entry_block fn` >> simp[] >> rpt strip_tac >> gvs[NULL_EQ]
QED

Theorem alias_ready_join_predecessor_jmp:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  MEM pred (cfg_preds_of (cfg_analyze fn) lbl) /\
  lookup_block pred fn.fn_blocks = SOME pb ==>
  ~NULL pb.bb_instructions /\ (LAST pb.bb_instructions).inst_opcode = JMP
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  gvs[codegen_ready_fn_def, block_entries_ready_def, EVERY_MEM] >>
  qpat_x_assum `!b. MEM b fn.fn_blocks ==> _ \/ _`
    (qspec_then `bb` mp_tac) >> simp[] >>
  disch_then assume_tac >> first_x_assum drule >> simp[]
QED

Theorem alias_ready_jmp_edge_operands:
  codegen_ready_fn fn /\ lookup_block pred fn.fn_blocks = SOME pb /\
  ~NULL pb.bb_instructions /\ (LAST pb.bb_instructions).inst_opcode = JMP /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) ==>
  (LAST pb.bb_instructions).inst_operands = [Label lbl]
Proof
  strip_tac >>
  `MEM pb fn.fn_blocks /\ pb.bb_label = pred` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[codegen_ready_fn_def] >>
  `inst_wf (LAST pb.bb_instructions)` by
    metis_tac[fn_inst_wf_def, LAST_MEM, NULL_EQ] >>
  gvs[inst_wf_def] >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
  strip_tac >> gvs[] >> Cases_on `pb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, get_label_def, is_terminator_def,
      NULL_EQ]
QED

Theorem alias_lineage_join_historical_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) ==>
  ?pred. lineage_entry liveness dfg cfg fn
           (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred lbl ps /\
         MEM pred (cfg_preds_of cfg lbl) /\
         (!v. MEM v (input_vars_from pred bb.bb_instructions
                        (live_vars_at liveness lbl 0)) ==>
              MEM (Var v) ps.ps_stack)
Proof
  strip_tac >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  simp[Once lineage_state_cases] >> strip_tac
  >- (gvs[] >> drule_all alias_ready_entry_no_preds >>
      disch_then assume_tac >> gvs[]) >>
  gvs[] >> qexists_tac `lbl'` >> conj_tac
  >- (simp[lineage_entry_def] >> metis_tac[]) >>
  conj_asm1_tac
  >- metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  drule_all alias_ready_join_predecessor_jmp >> strip_tac >>
  drule_all alias_ready_jmp_edge_operands >> strip_tac >>
  `bb'.bb_label = lbl'` by metis_tac[lookup_block_label] >>
  `?prefix. non_param_insts bb' = prefix ++ [LAST bb'.bb_instructions]` by
    (qexists_tac `FILTER (\i. ~is_param_opcode i.inst_opcode)
                     (FRONT bb'.bb_instructions)` >>
     `bb'.bb_instructions = FRONT bb'.bb_instructions ++
                              [LAST bb'.bb_instructions]` by
       metis_tac[APPEND_FRONT_LAST, NULL_EQ] >>
     simp[non_param_insts_def] >>
     pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[FILTER_APPEND, is_param_opcode_def]) >>
  rpt strip_tac >> irule alias_block_plan_final_jmp_inputs >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem alias_phi_ready_ordinary_input:
  phi_block_ready liveness bb /\
  MEM v (live_vars_at liveness bb.bb_label 0) /\
  MEM v (live_vars_at liveness bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions))) ==>
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at liveness bb.bb_label 0))
Proof
  strip_tac >> irule alias_input_vars_ordinary_intro >>
  gvs[phi_block_ready_def, EVERY_MEM] >> metis_tac[]
QED

Theorem alias_lineage_join_ordinary_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of cfg lbl) /\
  MEM v (live_vars_at liveness lbl 0) /\
  MEM v (live_vars_at liveness lbl
    (LENGTH (collect_phis bb.bb_instructions))) ==>
  MEM (Var v) ps.ps_stack
Proof
  strip_tac >>
  drule_all alias_lineage_join_historical_coverage >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  first_x_assum irule >>
  Cases_on `NULL (collect_phis bb.bb_instructions)`
  >- gvs[input_vars_from_def] >>
  `phi_block_ready (liveness_analyze fn) bb` by
    (gvs[codegen_ready_fn_def, phi_operands_ready_def, EVERY_MEM] >>
     metis_tac[]) >>
  metis_tac[alias_phi_ready_ordinary_input]
QED

Theorem alias_do_swap_stack:
  dist < LENGTH ps.ps_stack ==>
  (SND (do_swap dist ps)).ps_stack = stack_swap dist ps.ps_stack
Proof
  strip_tac >> Cases_on `dist = 0`
  >- (gvs[do_swap_def, stack_swap_def, LUPDATE_SAME]) >>
  Cases_on `dist <= 16` >- simp[do_swap_def] >>
  simp[do_swap_def] >> pairarg_tac >> simp[] >>
  simp[top_n_def, GSYM LASTN_def, LASTN_DROP] >>
  irule LIST_EQ >>
  simp[stack_swap_def, LENGTH_LUPDATE] >>
  rpt strip_tac >>
  simp[EL_APPEND_EQN, EL_MAP, EL_GENLIST, EL_LUPDATE, EL_DROP] >>
  Cases_on `x = LENGTH ps.ps_stack - (dist + 1)`
  >- (gvs[] >> simp[]) >>
  Cases_on `x = LENGTH ps.ps_stack - 1`
  >- (gvs[] >> simp[HD_DROP]) >>
  Cases_on `x < LENGTH ps.ps_stack - (dist + 1)` >>
  simp[EL_TAKE]
QED

Theorem alias_select_spill_candidate_large:
  16 < target_len ==>
  select_spill_candidate stk forbidden target_dist target_len = NONE
Proof
  strip_tac >>
  Cases_on `select_spill_candidate stk forbidden target_dist target_len`
  >- simp[] >>
  drule planWfTheory.select_spill_candidate_below_target >>
  gvs[select_spill_candidate_def] >>
  imp_res_tac FIND_SOME_MEM >> gvs[MEM_GENLIST, arithmeticTheory.MIN_DEF]
QED

Theorem alias_reduce_depth_plan_large:
  16 < target_len ==>
  reduce_depth_plan fuel target_ops target_op f target_len ps = ([],ps)
Proof
  strip_tac >> Cases_on `fuel` >>
  simp[reduce_depth_plan_def, alias_select_spill_candidate_large] >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >> simp[]
QED

Theorem alias_reorder_one_large_step:
  16 < LENGTH pending /\ idx < LENGTH pending /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
    (LENGTH pending) ps.ps_stack = SOME d /\
  reorder_one dfg pending idx op ps = (ops,qs) ==>
  LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
  qs.ps_spilled = ps.ps_spilled /\
  (!at. LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack) /\
  stack_peek (LENGTH pending - (idx + 1)) qs.ps_stack = op /\
  (!i. i < idx ==> stack_peek (LENGTH pending - 1 - i) qs.ps_stack =
                   stack_peek (LENGTH pending - 1 - i) ps.ps_stack)
Proof
  strip_tac >>
  drule_then strip_assume_tac stack_get_unfixed_depth_props >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, alias_reduce_depth_plan_large] >>
  Cases_on `d = LENGTH pending - (idx + 1)`
  >- (gvs[] >> simp[]) >>
  `LENGTH pending - (idx + 1) < LENGTH ps.ps_stack` by decide_tac >>
  simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek (LENGTH pending - (idx + 1)) ps.ps_stack)`
  >- (simp[] >> disch_then strip_assume_tac >> gnvs[] >>
      conj_tac >- simp[stack_poke_def, LENGTH_LUPDATE] >>
      conj_tac
      >- (gen_tac >> irule doSwapSimTheory.stack_poke_exchange_multiplicity >> simp[]) >>
      simp[stack_peek_def, stack_poke_def, EL_LUPDATE] >>
      rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  disch_then strip_assume_tac >> gnvs[] >>
  rename1 `do_swap (LENGTH pending - (idx + 1)) ps3 = (swap2_ops,qs)` >>
  `LENGTH ps3.ps_stack = LENGTH ps.ps_stack /\
   ps3.ps_spilled = ps.ps_spilled` by
    (drule planWfTheory.do_swap_length >>
     qspec_then `d` (qspec_then `ps` mp_tac) do_swap_spilled_unchanged >> simp[]) >>
  `LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
   qs.ps_spilled = ps.ps_spilled` by
    (qspec_then `LENGTH pending - (idx + 1)`
       (qspec_then `ps3` mp_tac) planWfTheory.do_swap_length >>
     qspec_then `LENGTH pending - (idx + 1)`
       (qspec_then `ps3` mp_tac) do_swap_spilled_unchanged >> simp[]) >>
  simp[] >> conj_tac
  >- (gen_tac >>
      qspec_then `d` (qspec_then `ps` mp_tac) doSwapSimTheory.do_swap_multiplicity >>
      qspec_then `LENGTH pending - (idx + 1)`
        (qspec_then `ps3` mp_tac) doSwapSimTheory.do_swap_multiplicity >> simp[]) >>
  `ps3.ps_stack = stack_swap d ps.ps_stack` by
    (drule alias_do_swap_stack >> simp[]) >>
  `LENGTH pending - (idx + 1) < LENGTH ps3.ps_stack` by simp[] >>
  `qs.ps_stack = stack_swap (LENGTH pending - (idx + 1)) ps3.ps_stack` by
    metis_tac[alias_do_swap_stack, pairTheory.SND] >>
  simp[stack_peek_def, stack_swap_def, EL_LUPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem alias_plan_steps_large_materialised:
  !rest done pending dfg ps ops qs.
  pending = done ++ rest /\ 16 < LENGTH pending /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (!at. LIST_ELEM_COUNT at pending <= LIST_ELEM_COUNT at ps.ps_stack) /\
  (!i. i < LENGTH done ==>
    stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
    (MAPi (\i op. (LENGTH done + i,op)) rest) ps = (ops,qs) ==>
  LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
  qs.ps_spilled = ps.ps_spilled /\
  (!at. LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack) /\
  (!i. i < LENGTH pending ==>
    stack_peek (LENGTH pending - 1 - i) qs.ps_stack = EL i pending)
Proof
  Induct_on `rest`
  >- (simp[foldlSimTheory.plan_steps_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `plan_steps _ _ _ = _` mp_tac >>
  simp[indexedListsTheory.MAPi_def, combinTheory.o_DEF, arithmeticTheory.ADD_CLAUSES] >>
  strip_tac >> drule plan_steps_cons_result >> strip_tac >> gvs[] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH done < LENGTH (done ++ h::rest)` by simp[] >>
  `EL (LENGTH done) (done ++ h::rest) = h` by simp[EL_APPEND_EQN] >>
  `?d. stack_get_unfixed_depth h
    (LENGTH (done ++ h::rest) - (LENGTH done + 1))
    (LENGTH (done ++ h::rest)) ps.ps_stack = SOME d` by
    (qspecl_then [`done ++ h::rest`, `LENGTH done`, `ps`]
       mp_tac materialised_pending_next_on_stack_window >>
       `SUC (LENGTH done + LENGTH rest) - (LENGTH done + 1) = LENGTH rest` by decide_tac >>
       simp[arithmeticTheory.ADD_CLAUSES]) >>
  drule_at (Pat `reorder_one _ _ _ _ _ = _`) alias_reorder_one_large_step >>
  simp[] >> disch_then strip_assume_tac >>
  first_x_assum (qspec_then `done ++ [h]` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, LENGTH_APPEND, LENGTH] >>
  disch_then (qspecl_then [`dfg`, `ps1`, `rest_ops`, `qs`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rpt strip_tac >> Cases_on `i = LENGTH done`
      >- (`SUC (LENGTH done + LENGTH rest) - (i + 1) = LENGTH rest` by decide_tac >>
          simp[]) >>
      `i < LENGTH done` by decide_tac >>
      `SUC (LENGTH done + LENGTH rest) - (i + 1) = LENGTH done + LENGTH rest - i` by decide_tac >>
      first_x_assum (qspec_then `i` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES]) >>
  disch_then strip_assume_tac >> rpt strip_tac >>
  `SUC (LENGTH done + LENGTH rest) - (i + 1) = LENGTH done + LENGTH rest - i` by decide_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem alias_reorder_plan_large_materialised:
  16 < LENGTH pending /\ LENGTH pending <= LENGTH ps.ps_stack /\
  (!at. LIST_ELEM_COUNT at pending <= LIST_ELEM_COUNT at ps.ps_stack) /\
  reorder_plan dfg pending ps = (ops,qs) ==>
  LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
  qs.ps_spilled = ps.ps_spilled /\
  (!at. LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack) /\
  qs.ps_stack = TAKE (LENGTH qs.ps_stack - LENGTH pending) qs.ps_stack ++ pending
Proof
  strip_tac >>
  `LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
   qs.ps_spilled = ps.ps_spilled /\
   (!at. LIST_ELEM_COUNT at qs.ps_stack = LIST_ELEM_COUNT at ps.ps_stack) /\
   (!i. i < LENGTH pending ==>
     stack_peek (LENGTH pending - 1 - i) qs.ps_stack = EL i pending)` by
    (irule alias_plan_steps_large_materialised >> simp[] >>
     qexistsl_tac [`dfg`, `[]`, `ops`, `pending`] >>
     simp[GSYM reorder_plan_eq_plan_steps]) >>
  `qs.ps_stack = stack_pop (LENGTH pending) qs.ps_stack ++ pending` by
    (irule fixed_suffix_decompose >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  qpat_x_assum `qs.ps_stack = stack_pop _ _ ++ _` mp_tac >>
  simp[stack_pop_def]
QED

Theorem alias_emit_reorder_consumed_window:
  emit_input_plan opc inputs nl ps = (iops,prepared) /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  PERM inputs selected /\
  reorder_plan dfg selected prepared = (rops,arranged) ==>
  LENGTH selected <= LENGTH prepared.ps_stack /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected
Proof
  `!xs : operand list. !ys.
     (!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x ys) ==>
     LENGTH xs <= LENGTH ys` by
    (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     `MEM h ys` by
       (simp[GSYM LIST_ELEM_COUNT_MEM] >>
        first_x_assum (qspec_then `h` mp_tac) >>
        simp[LIST_ELEM_COUNT_THM]) >>
     qpat_x_assum `MEM h ys` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
     gvs[] >>
     first_x_assum (qspec_then `l1 ++ l2` mp_tac) >>
     impl_tac >-
       (gen_tac >> first_x_assum (qspec_then `x` mp_tac) >>
        simp[elem_count_append, LIST_ELEM_COUNT_THM] >>
        Cases_on `h = x` >> simp[LIST_ELEM_COUNT_THM] ) >>
     simp[]) >>
  rpt strip_tac >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  `LENGTH selected = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `!x. LIST_ELEM_COUNT x selected <= LIST_ELEM_COUNT x prepared.ps_stack` by
    metis_tac[] >>
  `LENGTH selected <= LENGTH prepared.ps_stack` by metis_tac[] >>
  Cases_on `LENGTH selected <= 16`
  >- (match_mp_tac fixed_suffix_decompose >> conj_tac
      >- (irule reorder_plan_materialised_length_floor >>
          simp[] >> qexistsl [`dfg`, `rops`, `prepared`] >> simp[]) >>
      rpt strip_tac >> irule reorder_plan_materialised_order >>
      simp[] >> qexistsl [`dfg`, `rops`, `prepared`] >> simp[]) >>
  `16 < LENGTH selected` by decide_tac >>
  drule_all alias_reorder_plan_large_materialised >> strip_tac >>
  qpat_x_assum `arranged.ps_stack = _` mp_tac >> simp[stack_pop_def]
QED


Theorem normalize_operand_non_assign_output:
  !fn inst x visited.
    ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
    inst.inst_opcode <> ASSIGN ==>
    normalize_operand (dfg_build_function fn) visited (Var x) = Var x
Proof
  rpt strip_tac >> Cases_on `MEM x visited` >> simp[Once normalize_operand_def] >>
  Cases_on `dfg_get_def (dfg_build_function fn) x` >>
  gvs[dfg_get_def_def] >>
  rename1 `FLOOKUP (dfg_build_function fn).dfg_defs x = SOME def` >>
  `dfg_get_def (dfg_build_function fn) x = SOME def` by simp[dfg_get_def_def] >>
  drule dfg_build_function_correct >> strip_tac >>
  `def = inst` by
    (irule ssa_unique_output >> conj_tac >- (qexists_tac `fn` >> simp[]) >>
     qexists_tac `x` >> simp[]) >>
  gvs[] >> simp[Once normalize_operand_def]
QED

(* Value-level copy boundary: neither operand needs a physical planner slot.
   Normalization transport and root noninterference are separate premises. *)
Theorem alias_assign_value_boundary:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [src] /\
  inst.inst_outputs = [x] /\ step_inst fuel ctx inst s = OK s' /\
  (!l. FLOOKUP s.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  normalize_operand dfg [] (Var x) = normalize_operand dfg [] src /\
  operand_val (frame_view fn ra s) lo src =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] src) /\
  operand_val (frame_view fn ra s') lo (normalize_operand dfg [] src) =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] src) ==>
  operand_val (frame_view fn ra s') lo (Var x) =
    operand_val (frame_view fn ra s') lo (normalize_operand dfg [] (Var x))
Proof
  strip_tac >>
  `step_inst_base inst s = OK s'` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
     simp[Once step_inst_def]) >>
  `?v. eval_operand src s = SOME v /\ s' = update_var x v s` by
    (qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
     simp[Once step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  `MEM x inst.inst_outputs` by simp[] >>
  `eval_operand src (frame_view fn ra s) =
    SOME (if retpc_var fn x then ra else v)` by
    (drule_all assign_eval_frame_view >>
     disch_then (qspecl_then [`ra`, `s.vs_memory`] mp_tac) >>
     Cases_on `src` >>
     simp[frame_view_def, eval_operand_def, lookup_var_def]) >>
  `operand_val (frame_view fn ra s) lo src =
    SOME (if retpc_var fn x then ra else v)` by
    (Cases_on `src` >> gvs[operand_val_def, eval_operand_def,
      lookup_var_def, frame_view_def]) >>
  gvs[frame_view_update_var, operand_val_update_var_eq]
QED

Theorem alias_phi_output_value_boundary:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ MEM x inst.inst_outputs ==>
  operand_val (frame_view fn ra s) lo (Var x) =
    operand_val (frame_view fn ra s) lo
      (normalize_operand (dfg_build_function fn) [] (Var x))
Proof
  strip_tac >>
  `normalize_operand (dfg_build_function fn) [] (Var x) = Var x` by
    (irule normalize_operand_non_assign_output >> simp[] >>
     qexists_tac `inst` >> simp[]) >> simp[]
QED

Theorem alias_step_survivor_value:
  step_inst fuel ctx inst s = OK s' /\
  (!x. at = Var x ==> ~MEM x inst.inst_outputs) /\
  (!x. normalize_operand dfg [] at = Var x ==> ~MEM x inst.inst_outputs) /\
  operand_val (frame_view fn ra s) lo at =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] at) ==>
  operand_val (frame_view fn ra s') lo at =
    operand_val (frame_view fn ra s') lo (normalize_operand dfg [] at)
Proof
  strip_tac >>
  `!x. ~MEM x inst.inst_outputs ==>
    FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x` by
    (Cases_on `is_terminator inst.inst_opcode` >>
     metis_tac[step_preserves_non_output_vars, step_terminator_preserves_vars,
               lookup_var_def]) >>
  Cases_on `normalize_operand dfg [] at` >> Cases_on `at` >>
  gvs[operand_val_def, frame_view_vars_lookup]
QED

Theorem alias_phis_survivor_value:
  eval_phis s instructions = OK s' /\
  (!x inst. at = Var x /\ MEM inst instructions /\ inst.inst_opcode = PHI ==>
    ~MEM x inst.inst_outputs) /\
  (!x inst. normalize_operand dfg [] at = Var x /\
    MEM inst instructions /\ inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs) /\
  operand_val (frame_view fn ra s) lo at =
    operand_val (frame_view fn ra s) lo (normalize_operand dfg [] at) ==>
  operand_val (frame_view fn ra s') lo at =
    operand_val (frame_view fn ra s') lo (normalize_operand dfg [] at)
Proof
  strip_tac >>
  `!x. (!inst. MEM inst instructions /\ inst.inst_opcode = PHI ==>
    ~MEM x inst.inst_outputs) ==>
    FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x` by
      metis_tac[eval_phis_flookup_not_phi_output] >>
  Cases_on `normalize_operand dfg [] at` >> Cases_on `at` >>
  gvs[operand_val_def, frame_view_vars_lookup] >> metis_tac[]
QED

(* Pointwise demand interface ledger (C1.21.2.3).
   Both survivor boundaries quantify over arbitrary operands and arbitrary dfg;
   neither assumes liveness nor physical ownership, so dead retained names are
   covered too. Label operands use lo, not vs_labels: no label preservation
   premise is needed for these survivor statements. Terminator and ordinary
   execution cases are both discharged by their exported preservation lemmas.

   Consumers still need STATIC producers, not additional transport lemmas:
   - New ASSIGN output: alias_assign_value_boundary consumes actual source
     equality, normalization transport and root-read stability, plus SSA,
     membership and the runtime label-map premise. None follows from mere
     successful planning or an absent physical source.
   - Other outputs: normalize_operand_non_assign_output gives reflexive
     equality; alias_phi_output_value_boundary already specializes this to PHI.
   - PHI survivors: alias_phis_survivor_value excludes both the demanded name
     and its variable root from ALL physical PHI outputs in the batch. These
     exclusions still need production under the target assumptions.
   - Ordinary survivors: alias_step_survivor_value requires the two output
     exclusions. This includes dead retained aliases; the earlier live-only
     root exclusion is not a producer for that case.
   - Backward traces still need initial equality coverage and final-held demand
     inclusion from actual lineage. Neither prev=NONE nor static JMP planning
     establishes runtime predecessor agreement or missing initial equality.
*)

(* Semantic-prefix interface probe (C1.20.1).

   Candidate ordinary-prefix assertion, written here rather than installed as a
   new global predicate until its entry producer has been validated:

     !x. MEM x (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
       operand_val (frame_view fn ra s) lo (Var x) =
       operand_val (frame_view fn ra s) lo
         (normalize_operand (dfg_build_function fn) [] (Var x)).

   The index is the NEXT instruction, s.vs_inst_idx = i. The initial state is
   s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions, where
   eval_phis entry bb.bb_instructions = OK s_phi. The actual recursion is
   exec_block (not block_step): at a nonterminator it calls itself on
   s' with vs_inst_idx := SUC i after step_inst fuel ctx inst s = OK s'.
   Induct on LENGTH bb.bb_instructions - i, keeping fuel fixed. Terminators
   stop recursion. Require lookup_block bb.bb_label fn.fn_blocks = SOME bb,
   fn_reachable fn bb.bb_label, wf_function fn, ssa_form fn and
   def_dominates_uses fn throughout. This is a proposal, NOT a proved theorem
   or a claim that the frozen target already supplies its base case.

   Premise ledger:

   * Entry: the frozen ownership and equality premises supply equality only
     for input_vars_from pred instructions (live_vars_at ... label 0), when
     entry.vs_prev_bb = SOME pred. To initialize the assertion after PHIs,
     each live non-PHI output x needs entry equality of x AND preservation
     of its normalized root through the entire PHI batch. The necessary
     implication from this entry demand to input_vars_from is UNVALIDATED:
     input_vars_from uses op_map over all PHI sources and a placed-index
     deduplication; it is not simply union of the selected sources and the
     ordinary survivors. Source collisions must be checked, not assumed away.

   * Parallel PHIs: a PHI output is a self root by
     alias_phi_output_value_boundary, independent of its selected value or
     physical location. A survivor x instead needs both x and any variable
     root r excluded from PHI outputs. eval_phis_flookup_not_phi_output and
     eval_phis_only_updates_vs_vars then preserve the two framed reads;
     literal/label roots need only unchanged labels. Producing the root
     exclusion from SSA/dominance at this batch boundary is UNVALIDATED.
     eval_phis reads EVERY source in entry, not in partially updated states.

   * Skipped physical PHI: E0072 already supplies this case. Runtime PHI
     equality is reflexive at its self root even if planning skips it. A
     later ASSIGN consumes semantic source equality, not source heldness,
     through alias_assign_value_boundary above. No new fixture is needed.

   * Ordinary survivor: backward live transfer supplies liveness at i if x
     is live at SUC i and is not an output. The proved
     alias_live_after_root_not_defined excludes its variable root from this
     instruction's definitions. step_preserves_non_output_vars (for
     nonterminators) and step_terminator_preserves_vars preserve reads.
     step_inst_preserves_labels_always preserves label-root reads.

   * New ASSIGN output: alias_assign_value_boundary separates source equality,
     normalization transport, and root-value preservation. Source liveness
     at i supplies the first from the prefix assertion. For a variable source,
     alias_live_root_not_defined supplies root exclusion at i. Literal and
     label sources use their immediate reads and unchanged labels. Transport
     across normalize_operand's visited list needs an acyclicity/rank result:
     normalize_operand_codegen_assign in fnFrameStepsRevertForward provides
     precisely this interface under codegen_ready_fn, but importing that
     theory (or relocating its rank infrastructure) is NOT validated here.
     Do not replace the cycle obligation with a syntactic one-step rewrite.

   * Other new outputs: normalize_operand_non_assign_output is reflexive;
     no semantic source equality is required. INVOKE belongs here, but old
     survivors still require step_preserves_non_output_vars, whose step_inst
     statement includes INVOKE, rather than an assumption that callee execution
     preserves the caller environment without merge_callee_state/bind_outputs.

   * Frame/retpc: perform the proof on operand_val (frame_view ...), never
     silently substitute raw vs_vars equality for framed equality. The checked
     ASSIGN boundary uses assign_eval_frame_view and frame_view_update_var,
     including the retpc-dependent destination value; labels use the frozen
     label-map premise, propagated by step_inst_preserves_labels_always.

   * prev = NONE: successful eval_phis forces an empty PHI prefix (otherwise
     eval_one_phi fails). It DOES NOT supply ordinary live-input equality:
     the frozen selected-input premise is vacuous. A separate lineage/entry
     argument or a weaker backward-demand interface is needed for this base
     case. This gap is not a counterexample to lineage_alias_successor.

   Even a proved live-prefix assertion would not cover final retained dead
   aliases: those remain the separate retained-name obligation in the PLAN.
*)

(* Actual single steps followed by normalize_operand, including literal roots. *)
Definition alias_assign_step_def:
  alias_assign_step dfg at src <=>
    ?v inst. at = Var v /\ FLOOKUP dfg.dfg_defs v = SOME inst /\
      inst.inst_opcode = ASSIGN /\ inst.inst_operands = [src]
End

Theorem alias_assign_source_available:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  alias_assign_step (dfg_build_function fn) (Var x) (Var y) /\
  alias_path_available fn l i x ==>
  alias_path_available fn l i y
Proof
  strip_tac >>
  `?assign. dfg_get_def (dfg_build_function fn) x = SOME assign /\
      assign.inst_opcode = ASSIGN /\ assign.inst_operands = [Var y]` by
    gvs[alias_assign_step_def, dfg_get_def_def] >>
  drule dfg_build_function_correct >> strip_tac >>
  `!bb j. MEM bb fn.fn_blocks /\ j < LENGTH bb.bb_instructions /\
       MEM x (inst_defs (EL j bb.bb_instructions)) ==>
       alias_path_available fn bb.bb_label j y` by
    (rpt strip_tac >>
     `EL j bb.bb_instructions = assign` by
       (irule ssa_unique_output >> conj_tac
        >- (qexists_tac `fn` >>
            gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
        qexists_tac `x` >> gvs[inst_defs_def]) >>
     irule alias_ordinary_use_available >>
     simp[inst_uses_def, operand_vars_def, operand_var_def]) >>
  rewrite_tac[alias_path_available_def] >> rpt strip_tac >>
  qpat_x_assum `alias_path_available fn l i x` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac
  >- (`?j. j < LENGTH bb.bb_instructions /\
           EL j bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
      `alias_path_available fn bb.bb_label j y` by
        metis_tac[lookup_block_MEM] >>
      `!p n. is_fn_path fn p ==> is_fn_path fn (TAKE n p)` by
        (Induct >- simp[is_fn_path_def] >>
         qx_gen_tac `head` >> Cases >- simp[is_fn_path_def] >>
         Cases_on `p` >> simp[is_fn_path_def] >>
         Cases_on `n'` >> simp[is_fn_path_def] >> strip_tac >>
         qpat_x_assum `!n. is_fn_path fn (h::t) ==> _`
           (qspec_then `SUC n` mp_tac) >> simp[]) >>
      qpat_x_assum `alias_path_available fn bb.bb_label j y` mp_tac >>
      rewrite_tac[alias_path_available_def] >>
      disch_then (qspec_then `TAKE (SUC k) path` mp_tac) >>
      impl_tac >- (simp[LENGTH_TAKE, HD_TAKE, LAST_EL, EL_TAKE] >>
                    metis_tac[lookup_block_label]) >>
      simp[LENGTH_TAKE, EL_TAKE] >> strip_tac >> disj1_tac
      >- (gvs[EL_TAKE] >> qexistsl_tac [`k'`,`bb'`,`inst'`] >> simp[] >> decide_tac) >>
      `bb.bb_label = EL k path` by metis_tac[lookup_block_label] >>
      gvs[] >> qexistsl_tac [`k`,`bb`,`EL j' bb.bb_instructions`] >>
      simp[EL_MEM]) >>
  `alias_path_available fn bb.bb_label j y` by
    metis_tac[lookup_block_MEM] >>
  qpat_x_assum `alias_path_available fn bb.bb_label j y` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[lookup_block_label] >>
  strip_tac >- metis_tac[] >>
  `bb.bb_label = l` by metis_tac[lookup_block_label] >> gvs[] >>
  disj2_tac >> qexists_tac `j'` >> simp[]
QED

Theorem normalize_operand_assign_chain:
  !dfg visited at.
    normalize_operand dfg visited at <> at ==>
    TC (alias_assign_step dfg) at (normalize_operand dfg visited at)
Proof
  recInduct normalize_operand_ind >>
  rpt strip_tac >>
  gvs[Once normalize_operand_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP dfg.dfg_defs v` >> gvs[] >>
  rename1 `FLOOKUP dfg.dfg_defs v = SOME inst` >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `inst.inst_operands = src::rest` >>
  Cases_on `rest` >> gvs[] >>
  gvs[Once normalize_operand_def] >>
  `alias_assign_step dfg (Var v) src` by
    (simp[alias_assign_step_def] >> metis_tac[]) >>
  Cases_on `normalize_operand dfg (v::visited) src = src`
  >- metis_tac[relationTheory.TC_SUBSET] >>
  metis_tac[relationTheory.TC_RULES]
QED

Theorem alias_normalize_available:
  !dfg visited at.
    dfg = dfg_build_function fn /\ wf_function fn /\ ssa_form fn /\
    def_dominates_uses fn /\
    (!v. at = Var v ==> alias_path_available fn l i v) /\
    normalize_operand dfg visited at = Var r ==>
    alias_path_available fn l i r
Proof
  recInduct normalize_operand_ind >> rpt strip_tac >>
  gvs[Once normalize_operand_def, AllCaseEqs()] >>
  first_x_assum irule >> rpt strip_tac >> gvs[] >>
  irule alias_assign_source_available >>
  simp[alias_assign_step_def] >> metis_tac[]
QED

Theorem alias_path_available_index_mono:
  alias_path_available fn l i x /\ i <= j ==>
  alias_path_available fn l j x
Proof
  simp[alias_path_available_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac
  >- metis_tac[] >>
  disj2_tac >> qexistsl_tac [`bb`, `j'`] >> simp[] >> decide_tac
QED

Theorem alias_available_suffix_not_output:
  wf_function fn /\ ssa_form fn /\ fn_reachable fn l /\
  lookup_block l fn.fn_blocks = SOME bb /\
  alias_path_available fn l i x /\ i <= j /\
  j < LENGTH bb.bb_instructions ==>
  ~MEM x (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `alias_path_available fn l j x` by
    metis_tac[alias_path_available_index_mono] >>
  metis_tac[alias_definition_not_available, inst_defs_def]
QED

Theorem alias_available_root_suffix_not_output:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  (!x. at = Var x ==> alias_path_available fn l i x) /\
  normalize_operand (dfg_build_function fn) [] at = Var r /\
  i <= j /\ j < LENGTH bb.bb_instructions ==>
  ~MEM r (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `alias_path_available fn l i r` by
    (irule alias_normalize_available >> simp[] >> metis_tac[]) >>
  metis_tac[alias_available_suffix_not_output]
QED

Theorem alias_available_entry_not_output:
  wf_function fn /\ ssa_form fn /\ fn_reachable fn l /\
  lookup_block l fn.fn_blocks = SOME bb /\
  alias_path_available fn l 0 x /\ MEM inst bb.bb_instructions ==>
  ~MEM x inst.inst_outputs
Proof
  strip_tac >>
  `?j. j < LENGTH bb.bb_instructions /\ inst = EL j bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  gvs[] >> irule alias_available_suffix_not_output >> simp[] >>
  qexistsl_tac [`fn`, `0`, `l`] >> simp[]
QED

Theorem alias_available_root_entry_not_output:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  (!x. at = Var x ==> alias_path_available fn l 0 x) /\
  normalize_operand (dfg_build_function fn) [] at = Var r /\
  MEM inst bb.bb_instructions ==>
  ~MEM r inst.inst_outputs
Proof
  strip_tac >>
  `alias_path_available fn l 0 r` by
    (irule alias_normalize_available >> simp[] >> metis_tac[]) >>
  metis_tac[alias_available_entry_not_output]
QED

Theorem alias_live_root_not_defined:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  MEM x (live_vars_at (liveness_analyze fn) l i) /\
  normalize_operand (dfg_build_function fn) [] (Var x) = Var r ==>
  ~MEM r (inst_defs (EL i bb.bb_instructions))
Proof
  strip_tac >>
  `alias_path_available fn l i x` by
    metis_tac[alias_live_available_after_phis] >>
  `alias_path_available fn l i r` by
    (irule alias_normalize_available >> simp[] >>
     qexistsl_tac [`Var x`,`[]`] >> simp[]) >>
  metis_tac[alias_definition_not_available]
QED

Theorem alias_live_after_root_not_defined:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  LENGTH (collect_phis bb.bb_instructions) <= SUC i /\
  MEM x (live_vars_at (liveness_analyze fn) l (SUC i)) /\
  ~MEM x (inst_defs (EL i bb.bb_instructions)) /\
  normalize_operand (dfg_build_function fn) [] (Var x) = Var r ==>
  ~MEM r (inst_defs (EL i bb.bb_instructions))
Proof
  strip_tac >>
  `alias_path_available fn l (SUC i) x` by
    metis_tac[alias_live_available_after_phis] >>
  `alias_path_available fn l i x` by
    metis_tac[alias_available_nondef_backward] >>
  `alias_path_available fn l i r` by
    (irule alias_normalize_available >> simp[] >>
     qexistsl_tac [`Var x`,`[]`] >> simp[]) >>
  metis_tac[alias_definition_not_available]
QED

(* Inventory boundaries do not depend on cleanup metadata or allocator fields. *)
Theorem alias_stack_find_singleton:
  !xs p v. FILTER p xs = [v] ==>
    ?d. stack_find p xs = SOME d /\ d < LENGTH xs /\ EL d xs = v /\
        (!j. j < LENGTH xs /\ p (EL j xs) ==> j = d)
Proof
  Induct >> simp[stack_find_def] >> rpt gen_tac >>
  Cases_on `p h` >> simp[stack_find_def]
  >- (strip_tac >> gvs[] >>
      rpt strip_tac >> Cases_on `j` >> gvs[] >>
      gvs[FILTER_EQ_NIL, EVERY_EL]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `SUC d` >> simp[arithmeticTheory.ADD1, EL_CONS] >>
  rpt strip_tac >> Cases_on `j` >> gvs[] >> metis_tac[]
QED

Theorem alias_phi_singleton_poke:
  FILTER (\at. MEM at inputs) stk = [v] /\ ~MEM ret inputs ==>
  ?d. stack_get_phi_depth inputs stk = SOME d /\
      stack_peek d stk = v /\
      (!at. MEM at inputs ==> ~MEM at (stack_poke d ret stk))
Proof
  strip_tac >>
  `FILTER (\at. MEM at inputs) (REVERSE stk) = [v]` by
    simp[FILTER_REVERSE] >>
  drule alias_stack_find_singleton >> strip_tac >>
  qexists_tac `d` >> simp[stack_get_phi_depth_def] >> conj_tac
  >- (gvs[LENGTH_REVERSE] >>
      qspecl_then [`d`,`stk`] mp_tac EL_REVERSE >> simp[stack_peek_def, arithmeticTheory.PRE_SUB1]) >>
  rpt strip_tac >>
  `?j. j < LENGTH (stack_poke d ret stk) /\
       EL j (stack_poke d ret stk) = at` by metis_tac[MEM_EL] >>
  gvs[stack_poke_def, LENGTH_LUPDATE, EL_LUPDATE] >>
  Cases_on `j = LENGTH stk - 1 - d` >> gvs[] >>
  `LENGTH stk - 1 - j = d` by
    (first_x_assum irule >>
     simp[EL_REVERSE, GSYM arithmeticTheory.ADD1]) >>
  decide_tac
QED

Definition plan_holds_def:
  plan_holds ps at <=> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
End

Theorem do_spill_tos_plan_holds:
  do_spill_tos ps = (ops,ps') /\ plan_holds ps at ==>
  plan_holds ps' at
Proof
  simp[do_spill_tos_def] >> pairarg_tac >> gvs[] >>
  qspec_then `ps.ps_stack` strip_assume_tac SNOC_CASES >>
  gvs[plan_holds_def, stack_pop_def, stack_peek_def,
      LENGTH_SNOC, TAKE_SNOC, EL_SNOC, EL_LENGTH_SNOC, MEM_SNOC] >>
  rpt strip_tac >> gvs[]
QED

Theorem stack_swap_mem_iff:
  dist < LENGTH (stk : operand list) ==>
  (MEM at (stack_swap dist stk) <=> MEM at stk)
Proof
  strip_tac >>
  `0 < LENGTH stk` by decide_tac >>
  qspecl_then [`stk`, `0`, `dist`, `at`] mp_tac
    doSwapSimTheory.stack_poke_exchange_multiplicity >>
  simp[stack_poke_def, stack_peek_def, stack_swap_def,
       GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem stack_swap_mem_unbounded:
  MEM at (stk : operand list) ==> MEM at (stack_swap dist stk)
Proof
  strip_tac >>
  `0 < LENGTH stk` by (Cases_on `stk` >> gvs[]) >>
  `MIN dist (LENGTH stk - 1) < LENGTH stk` by simp[arithmeticTheory.MIN_DEF] >>
  `stack_swap dist stk = stack_swap (MIN dist (LENGTH stk - 1)) stk` by
    (simp[stack_swap_def, arithmeticTheory.MIN_DEF] >> IF_CASES_TAC >> simp[] >>
     `LENGTH stk - (dist + 1) = 0` by decide_tac >> simp[]) >>
  metis_tac[stack_swap_mem_iff]
QED

Theorem swap_desired_index_mem:
  2 <= chunk /\ j < chunk ==>
  MEM j ([chunk - 1] ++ GENLIST (\i. i + 1) (chunk - 2) ++ [0])
Proof
  strip_tac >> simp[MEM_GENLIST] >>
  Cases_on `j = 0` >- simp[] >>
  Cases_on `j = chunk - 1` >- simp[] >>
  gvs[] >> qexists_tac `j - 1` >> decide_tac
QED

Theorem top_n_stack_decomposition:
  TAKE (LENGTH stk - n) stk ++ top_n n stk = stk
Proof
  Cases_on `n <= LENGTH stk`
  >- (simp[top_n_def, GSYM LASTN_def] >>
      metis_tac[BUTLASTN_TAKE, APPEND_BUTLASTN_LASTN]) >>
  simp[top_n_def, TAKE_LENGTH_TOO_LONG]
QED

Theorem swap_desired_values_mem:
  2 <= chunk /\ LENGTH items <= chunk /\ MEM at items ==>
  MEM at (MAP (\idx. EL idx items)
    ([chunk - 1] ++ GENLIST (\i. i + 1) (chunk - 2) ++ [0]))
Proof
  strip_tac >>
  qpat_x_assum `MEM at items` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  pure_rewrite_tac[MEM_MAP] >> qexists_tac `n` >>
  conj_tac >- simp[] >> irule swap_desired_index_mem >> decide_tac
QED

Theorem do_swap_plan_holds:
  do_swap dist ps = (ops,ps') /\ plan_holds ps at ==> plan_holds ps' at
Proof
  Cases_on `dist = 0`
  >- (simp[do_swap_def] >> strip_tac >> gvs[]) >>
  Cases_on `dist <= 16`
  >- (simp[do_swap_def] >> strip_tac >> gvs[plan_holds_def] >>
      metis_tac[stack_swap_mem_unbounded]) >>
  simp[do_swap_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  gvs[plan_holds_def] >>
  `MEM at (TAKE (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack) \/
   MEM at (top_n (dist + 1) ps.ps_stack)` by
    metis_tac[top_n_stack_decomposition, MEM_APPEND] >>
  simp[] >>
  `MEM at (MAP (\idx. EL idx (top_n (dist + 1) ps.ps_stack))
     ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]))` by
    (drule_at (Pat `MEM _ _`) swap_desired_values_mem >>
     disch_then (qspec_then `dist + 1` mp_tac) >>
     simp[top_n_def, LENGTH_TAKE_EQ]) >>
  gvs[]
QED

Theorem do_spill_at_plan_holds:
  dist < LENGTH ps.ps_stack /\ do_spill_at dist ps = (ops,ps') /\
  plan_holds ps at ==> plan_holds ps' at
Proof
  Cases_on `dist = 0`
  >- (simp[do_spill_at_def] >> metis_tac[do_spill_tos_plan_holds]) >>
  simp[do_spill_at_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `plan_holds (ps with ps_stack := stack_swap dist ps.ps_stack) at` by
    gvs[plan_holds_def, stack_swap_mem_iff] >>
  drule_all do_spill_tos_plan_holds >> simp[]
QED

Theorem do_restore_plan_holds:
  do_restore op ps = (ops,ps') /\ plan_holds ps at ==>
  plan_holds ps' at
Proof
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def, plan_holds_def, stack_push_def] >>
  rpt strip_tac >> gvs[MEM_SNOC]
QED

Theorem restore_spilled_plan_holds:
  !pending ps ops ps' at.
    restore_spilled_plan pending ps = (ops,ps') /\ plan_holds ps at ==>
    plan_holds ps' at
Proof
  Induct >> simp[restore_spilled_plan_def] >>
  rpt gen_tac >> pairarg_tac >> gvs[] >>
  Cases_on `restore_spilled_plan pending ps1` >> simp[] >>
  strip_tac >> gvs[] >>
  drule_all do_restore_plan_holds >> strip_tac >>
  first_x_assum (qspec_then `ps1` mp_tac) >>
  disch_then irule >> simp[]
QED

Theorem reduce_depth_plan_holds:
  !fuel target_ops target_op f target_len ps ops ps' at.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops,ps') /\
    plan_holds ps at ==> plan_holds ps' at
Proof
  Induct >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  Cases_on `f + 1 < target_len` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops dist target_len` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  Cases_on `do_spill_at cand ps` >> simp[] >>
  rename1 `do_spill_at _ _ = (sops,ps1)` >>
  Cases_on `reduce_depth_plan fuel target_ops target_op f target_len ps1` >>
  simp[] >> strip_tac >> gvs[] >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand < LENGTH ps.ps_stack` by
    metis_tac[planWfTheory.select_spill_candidate_bound] >>
  drule_all do_spill_at_plan_holds >> strip_tac >>
  first_x_assum (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`, `ps1`]
    mp_tac) >> simp[]
QED

Theorem stack_poke_exchange_mem:
  d < LENGTH (stk : operand list) /\ e < LENGTH stk ==>
  (MEM at (stack_poke e (stack_peek d stk)
    (stack_poke d (stack_peek e stk) stk)) <=> MEM at stk)
Proof
  strip_tac >>
  qspecl_then [`stk`, `d`, `e`, `at`] mp_tac
    doSwapSimTheory.stack_poke_exchange_multiplicity >>
  simp[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem reorder_one_plan_holds:
  reorder_one dfg pending idx op ps = (ops,ps') /\ plan_holds ps at ==>
  plan_holds ps' at
Proof
  simp[reorder_one_def] >> pairarg_tac >>
  `plan_holds ps at ==> plan_holds ps1 at` by
    (qpat_x_assum `_ = (restore_ops,ps1)` mp_tac >>
     Cases_on `stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
       (LENGTH pending) ps.ps_stack` >> simp[]
     >- (Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
         metis_tac[do_restore_plan_holds]) >>
     strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
    (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >>
  `plan_holds ps1 at ==> plan_holds ps2 at` by
    (qpat_x_assum `_ = (reduce_ops,ps2)` mp_tac >>
     IF_CASES_TAC >> simp[]
     >- metis_tac[reduce_depth_plan_holds] >> strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
    (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME d` >>
  Cases_on `d = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` >> simp[]
  >- (IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[] >>
          drule stack_get_unfixed_depth_props >> strip_tac >>
          gvs[plan_holds_def, stack_poke_exchange_mem]) >>
      pairarg_tac >> gvs[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      dxrule_all do_swap_plan_holds >> strip_tac >>
      drule_all do_swap_plan_holds >> simp[]) >>
  pairarg_tac >> gvs[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  dxrule_all do_swap_plan_holds >> strip_tac >>
  drule_all do_swap_plan_holds >> simp[]
QED

Theorem reorder_plan_holds:
  reorder_plan dfg pending ps = (ops,ps') /\ plan_holds ps at ==>
  plan_holds ps' at
Proof
  `!steps acc ps ops ps'.
    FOLDL (\(acc,st) (idx,op).
      (\(sops,st'). (acc ++ sops,st'))
        (reorder_one dfg pending idx op st)) (acc,ps) steps = (ops,ps') /\
    plan_holds ps at ==> plan_holds ps' at` by
    (Induct >- (simp[] >> rpt strip_tac >> gvs[]) >>
     simp[] >> rpt gen_tac >> PairCases_on `h` >>
     Cases_on `reorder_one dfg pending h0 h1 ps` >> simp[] >>
     strip_tac >> drule_all reorder_one_plan_holds >> strip_tac >>
     first_x_assum (qspecl_then [`acc ++ q`, `r`, `ops`, `ps'`] mp_tac) >>
     simp[]) >>
  simp[reorder_plan_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem stack_pop_retains_noninputs:
  n <= LENGTH stk /\
  (!i. i < n ==> MEM (stack_peek i stk) pending) /\
  ~MEM at pending /\ MEM at stk ==>
  MEM at (stack_pop n stk)
Proof
  strip_tac >>
  qpat_x_assum `MEM at stk` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `j < LENGTH stk` >>
  Cases_on `j < LENGTH stk - n`
  >- (simp[stack_pop_def, MEM_EL] >> qexists_tac `j` >>
      simp[LENGTH_TAKE_EQ, EL_TAKE]) >>
  `LENGTH stk - 1 - j < n` by decide_tac >>
  `stack_peek (LENGTH stk - 1 - j) stk = at` by
    (simp[stack_peek_def] >>
     `LENGTH stk - (LENGTH stk - 1 - j + 1) = j` by decide_tac >> simp[]) >>
  metis_tac[]
QED

Theorem reorder_consume_retains_noninputs:
  LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack /\
  (!x. MEM x pending ==>
    LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
  reorder_plan dfg pending ps = (ops,ps') /\
  plan_holds ps at /\ ~MEM at pending ==>
  plan_holds (ps' with ps_stack := stack_pop (LENGTH pending) ps'.ps_stack) at
Proof
  strip_tac >>
  drule_all reorder_plan_holds >> strip_tac >>
  drule_all reorder_plan_materialised_length_floor >> strip_tac >>
  drule_at (Pat `reorder_plan _ _ _ = _`) reorder_plan_materialised_order >>
  simp[] >> disch_tac >>
  `!d. d < LENGTH pending ==> MEM (stack_peek d ps'.ps_stack) pending` by
    (rpt strip_tac >>
     first_x_assum (qspec_then `LENGTH pending - 1 - d` mp_tac) >>
     `LENGTH pending - 1 - d < LENGTH pending` by decide_tac >>
     `LENGTH pending - 1 - (LENGTH pending - 1 - d) = d` by decide_tac >>
     simp[] >> strip_tac >> simp[MEM_EL] >>
     qexists_tac `LENGTH pending - (d + 1)` >> simp[]) >>
  gvs[plan_holds_def] >> disj1_tac >> irule stack_pop_retains_noninputs >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `pending` >> simp[]
QED

Definition alias_var_mass_def:
  alias_var_mass x ps =
    LIST_ELEM_COUNT (Var x) ps.ps_stack +
    (if Var x IN FDOM ps.ps_spilled then 1 else 0)
End

Theorem alias_var_mass_positive:
  0 < alias_var_mass x ps <=> plan_holds ps (Var x)
Proof
  simp[alias_var_mass_def, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[]
QED

Theorem emit_one_input_plan_holds:
  plan_holds ps at ==> plan_holds (SND (emit_one_input opc nl op ps)) at
Proof
  mp_tac (Q.SPECL [`opc`, `nl`, `op`, `ps`] emit_one_input_inventory_mono_aux) >>
  disch_then (qspec_then `at` mp_tac) >>
  simp[plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
  rpt IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem emit_input_plan_holds:
  !operands opc nl ps at.
    plan_holds ps at ==> plan_holds (SND (emit_input_plan opc operands nl ps)) at
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >> simp[] >>
  Cases_on `emit_input_plan opc operands nl r` >> simp[] >> strip_tac >>
  `plan_holds r at` by
    (drule emit_one_input_plan_holds >>
     disch_then (qspecl_then [`opc`, `h`, `operand_vars operands ++ nl`] mp_tac) >>
     simp[]) >>
  first_x_assum (qspecl_then [`opc`, `nl`, `r`, `at`] mp_tac) >> simp[]
QED

Theorem emit_input_plan_live_surplus:
  !operands opc nl ps x.
    MEM x nl /\ plan_holds ps (Var x) ==>
    alias_var_mass x ps + LIST_ELEM_COUNT (Var x) operands <=
    alias_var_mass x (SND (emit_input_plan opc operands nl ps))
Proof
  Induct >> simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >> rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >> simp[] >>
  Cases_on `emit_input_plan opc operands nl r` >> simp[] >> strip_tac >>
  `plan_holds r (Var x)` by
    (drule emit_one_input_plan_holds >>
     disch_then (qspecl_then [`opc`, `h`, `operand_vars operands ++ nl`] mp_tac) >>
     simp[]) >>
  first_x_assum (qspecl_then [`opc`, `nl`, `r`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `Var x = h`
  >- (gvs[] >>
      mp_tac (Q.SPECL [`opc`, `operand_vars operands ++ nl`, `Var x`, `ps`]
        emit_one_input_inventory_inc) >>
      simp[is_var_operand_def, GSYM plan_holds_def, GSYM alias_var_mass_def,
           LIST_ELEM_COUNT_THM] >>
      decide_tac) >>
  mp_tac (Q.SPECL [`opc`, `operand_vars operands ++ nl`, `h`, `ps`]
    emit_one_input_inventory_mono_aux) >>
  disch_then (qspec_then `Var x` mp_tac) >>
  simp[GSYM alias_var_mass_def, LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem alias_emit_reorder_consume_live:
  emit_input_plan opc inputs nl ps = (iops,prepared) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  PERM inputs selected /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  MEM x nl /\ plan_holds ps (Var x) ==>
  plan_holds
    (arranged with ps_stack := stack_pop (LENGTH selected) arranged.ps_stack)
    (Var x)
Proof
  strip_tac >>
  `!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    gvs[plan_holds_def] >>
  drule_all alias_emit_reorder_consumed_window >> strip_tac >>
  drule_all emit_input_plan_materialised >> disch_tac >>
  drule perm_operand_counts >> strip_tac >>
  `LENGTH selected = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `!op. LIST_ELEM_COUNT op selected <=
    LIST_ELEM_COUNT op prepared.ps_stack` by metis_tac[] >>
  `!op. MEM op selected ==>
    LIST_ELEM_COUNT op selected <= LIST_ELEM_COUNT op prepared.ps_stack` by
    simp[] >>
  reverse (Cases_on `LENGTH inputs <= 16`)
  >- (`16 < LENGTH selected` by decide_tac >>
      drule_all alias_reorder_plan_large_materialised >> strip_tac >>
      mp_tac (Q.SPECL [`inputs`, `opc`, `nl`, `ps`, `x`]
        emit_input_plan_live_surplus) >> simp[] >>
      `0 < alias_var_mass x ps` by simp[alias_var_mass_positive] >>
      qpat_x_assum `arranged.ps_stack = stack_pop _ _ ++ _`
        (mp_tac o Q.AP_TERM `LIST_ELEM_COUNT (Var x)`) >>
      simp[elem_count_append, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM,
           alias_var_mass_def] >>
      rpt IF_CASES_TAC >> gvs[alias_var_mass_def] >> decide_tac) >>
  Cases_on `MEM (Var x) selected`
  >- (`LENGTH selected <= 16` by simp[] >>
      drule_all reorder_plan_materialised_counts >>
      strip_tac >>
      `MEM (Var x) inputs` by metis_tac[PERM_MEM_EQ] >>
      drule emit_input_plan_vars_not_spilled >>
      disch_then (qspec_then `Var x` mp_tac) >>
      simp[is_var_operand_def] >> strip_tac >>
      mp_tac (Q.SPECL [`inputs`, `opc`, `nl`, `ps`, `x`]
        emit_input_plan_live_surplus) >>
      simp[alias_var_mass_def] >>
      `0 < alias_var_mass x ps` by simp[alias_var_mass_positive] >>
      qpat_x_assum `arranged.ps_stack = _` (mp_tac o
        Q.AP_TERM `LIST_ELEM_COUNT (Var x)`) >>
      simp[elem_count_append, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
      gvs[alias_var_mass_def] >> rpt IF_CASES_TAC >> gvs[] >> decide_tac) >>
  `plan_holds prepared (Var x)` by
    (drule emit_input_plan_holds >>
     disch_then (qspecl_then [`inputs`, `opc`, `nl`] mp_tac) >> simp[]) >>
  irule reorder_consume_retains_noninputs >> simp[] >>
  qexistsl [`dfg`, `rops`, `prepared`] >> simp[]
QED

Definition alias_var_budget_def:
  alias_var_budget pending ps <=>
    !x. alias_var_mass x ps <= SUC (LIST_ELEM_COUNT (Var x) pending)
End

Theorem alias_var_mass_fields:
  ps.ps_stack = qs.ps_stack /\ FDOM ps.ps_spilled = FDOM qs.ps_spilled ==>
  alias_var_mass x ps = alias_var_mass x qs
Proof
  simp[alias_var_mass_def]
QED

Theorem alias_var_budget_empty:
  alias_var_budget [] ps <=>
  !x. LIST_ELEM_COUNT (Var x) ps.ps_stack +
    (if Var x IN FDOM ps.ps_spilled then 1 else 0) <= 1
Proof
  simp[alias_var_budget_def, alias_var_mass_def, LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_push:
  alias_var_mass x (ps with ps_stack := stack_push op ps.ps_stack) =
  alias_var_mass x ps + (if op = Var x then 1 else 0)
Proof
  simp[alias_var_mass_def, stack_push_def, SNOC_APPEND, elem_count_append,
       LIST_ELEM_COUNT_THM] >>
  Cases_on `op = Var x` >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_restore:
  alias_var_mass x (SND (do_restore op ps)) = alias_var_mass x ps
Proof
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def, alias_var_mass_def, stack_push_def,
       SNOC_APPEND, elem_count_append, LIST_ELEM_COUNT_THM, finite_mapTheory.FDOM_DOMSUB] >>
  Cases_on `op = Var x` >>
  gvs[finite_mapTheory.flookup_thm, LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_spill_tos:
  !ps x. ps.ps_stack <> [] ==>
  alias_var_mass x (SND (do_spill_tos ps)) <= alias_var_mass x ps
Proof
  rpt gen_tac >> strip_tac >>
  `?a stk. ps.ps_stack = SNOC a stk` by metis_tac[SNOC_CASES] >>
  simp[do_spill_tos_def, alias_var_mass_def] >>
  pairarg_tac >> gvs[] >>
  simp[stack_pop_def, stack_peek_def, SNOC_APPEND, TAKE_APPEND,
       EL_APPEND_EQN, elem_count_append, LIST_ELEM_COUNT_THM] >>
  Cases_on `a = Var x` >> simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[]
QED

Theorem alias_var_mass_spill:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_spill_at d ps)) <= alias_var_mass x ps
Proof
  strip_tac >> Cases_on `d = 0`
  >- (simp[do_spill_at_def] >> irule alias_var_mass_spill_tos >>
      strip_tac >> gvs[]) >>
  `LIST_ELEM_COUNT (Var x) (stack_swap d ps.ps_stack) =
   LIST_ELEM_COUNT (Var x) ps.ps_stack` by
    (mp_tac (Q.SPECL [`ps.ps_stack`, `0`, `d`, `Var x`]
       doSwapSimTheory.stack_poke_exchange_multiplicity) >>
     simp[stack_poke_def, stack_peek_def, stack_swap_def]) >>
  `stack_swap d ps.ps_stack <> []` by
    (strip_tac >> gvs[stack_swap_def]) >>
  qspecl_then [`ps with ps_stack := stack_swap d ps.ps_stack`, `x`] mp_tac
    alias_var_mass_spill_tos >>
  simp[do_spill_at_def, alias_var_mass_def] >>
  pairarg_tac >> gvs[]
QED

Theorem alias_var_mass_dup:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_dup d ps)) = alias_var_mass x ps +
    (if stack_peek d ps.ps_stack = Var x then 1 else 0)
Proof
  strip_tac >>
  drule_then assume_tac doSwapSimTheory.do_dup_stack_exact >>
  Cases_on `d <= 15` >>
  simp[alias_var_mass_def, do_dup_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[alias_var_mass_def, stack_dup_def, elem_count_append] >>
  Cases_on `stack_peek d ps.ps_stack = Var x` >>
  simp[LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_swap:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_swap d ps)) = alias_var_mass x ps
Proof
  strip_tac >> drule_then (qspec_then `Var x` assume_tac)
    doSwapSimTheory.do_swap_multiplicity >>
  simp[alias_var_mass_def, do_swap_spilled_unchanged]
QED

Theorem alias_var_mass_restore_spilled:
  !ops ps x.
  alias_var_mass x (SND (restore_spilled_plan ops ps)) = alias_var_mass x ps
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`ps1`, `x`] mp_tac) >>
  mp_tac (Q.INST [`op` |-> `h`] alias_var_mass_restore) >> gvs[]
QED

Theorem alias_var_mass_reduce_depth:
  !fuel targets op f n ps x.
  alias_var_mass x (SND (reduce_depth_plan fuel targets op f n ps)) <=
  alias_var_mass x ps
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x' n` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all_then strip_assume_tac planWfTheory.select_spill_candidate_bound >>
  drule_then (qspec_then `x` mp_tac) (GEN_ALL alias_var_mass_spill) >>
  first_x_assum (qspecl_then [`targets`, `op`, `f`, `n`, `ps'`, `x`] mp_tac) >>
  gvs[] >> decide_tac
QED

Theorem alias_reduce_depth_length_floor:
  !fuel targets op f n ps.
  n <= LENGTH ps.ps_stack ==>
  n <= LENGTH (SND (reduce_depth_plan fuel targets op f n ps)).ps_stack
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x n` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all_then strip_assume_tac planWfTheory.select_spill_candidate_bound >>
  drule_then assume_tac planWfTheory.select_spill_candidate_below_target >>
  `LENGTH ps'.ps_stack = LENGTH ps.ps_stack - 1` by
    (Cases_on `x' = 0` >>
     gvs[do_spill_at_def, do_spill_tos_def, LET_THM,
         stack_swap_def, stack_pop_def] >>
     rpt (pairarg_tac >> gvs[]) >> simp[LENGTH_LUPDATE, LENGTH_TAKE_EQ]) >>
  first_x_assum (qspecl_then [`targets`, `op`, `f`, `n`, `ps'`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem alias_reorder_one_bounds:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_one dfg targets idx op ps)).ps_stack /\
  alias_var_mass x (SND (reorder_one dfg targets idx op ps)) <= alias_var_mass x ps
Proof
  strip_tac >> simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps1.ps_stack /\
   alias_var_mass x ps1 = alias_var_mass x ps` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps.ps_stack` >> gvs[] >>
     Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >>
     mp_tac alias_var_mass_restore >>
     qspecl_then [`op`, `ps`] mp_tac planWfTheory.do_restore_length >> gvs[] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps1.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps2.ps_stack /\
   alias_var_mass x ps2 <= alias_var_mass x ps1` by
    (Cases_on `x' > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `targets`, `op`,
       `LENGTH targets - (idx + 1)`, `LENGTH targets`, `ps1`]
       mp_tac alias_reduce_depth_length_floor >>
     qspecl_then [`LENGTH ps1.ps_stack`, `targets`, `op`,
       `LENGTH targets - (idx + 1)`, `LENGTH targets`, `ps1`, `x`]
       mp_tac alias_var_mass_reduce_depth >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps2.ps_stack` >> simp[] >>
  suspend "exchange"
QED

Resume alias_reorder_one_bounds[exchange]:
  drule_then strip_assume_tac stack_get_unfixed_depth_props >>
  `LENGTH targets - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `x'' = LENGTH targets - (idx + 1)` >> simp[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH targets - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (qspecl_then [`ps2.ps_stack`, `x''`, `LENGTH targets - (idx + 1)`, `Var x`]
        mp_tac doSwapSimTheory.stack_poke_exchange_multiplicity >>
      simp[] >> strip_tac >>
      gvs[alias_var_mass_def, stack_poke_def, LENGTH_LUPDATE]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack /\
   alias_var_mass x ps3 = alias_var_mass x ps2` by
    (qspecl_then [`x''`, `ps2`] mp_tac planWfTheory.do_swap_length >>
     mp_tac (Q.INST [`d` |-> `x''`, `ps` |-> `ps2`] alias_var_mass_swap) >>
     gvs[]) >>
  qspecl_then [`LENGTH targets - (idx + 1)`, `ps3`]
    mp_tac planWfTheory.do_swap_length >>
  mp_tac (Q.INST [`d` |-> `LENGTH (targets : operand list) - (idx + 1)`, `ps` |-> `ps3`]
    alias_var_mass_swap) >> gvs[] >> decide_tac
QED

Finalise alias_reorder_one_bounds

Theorem alias_reorder_one_length_floor:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_one dfg targets idx op ps)).ps_stack
Proof
  metis_tac[alias_reorder_one_bounds]
QED

Theorem alias_var_mass_reorder_one:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (reorder_one dfg targets idx op ps)) <= alias_var_mass x ps
Proof
  metis_tac[alias_reorder_one_bounds]
QED

Theorem alias_reorder_fold_bounds:
  !steps ops ps.
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)).ps_stack /\
  alias_var_mass x (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)) <= alias_var_mass x ps
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> simp[] >> pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps'.ps_stack /\
   alias_var_mass x ps' <= alias_var_mass x ps` by
    (mp_tac (Q.INST [`idx` |-> `h0`, `op` |-> `h1`] alias_reorder_one_bounds) >>
     gvs[]) >>
  first_x_assum (qspecl_then [`ops ++ step_ops`, `ps'`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem alias_reorder_plan_length_floor:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_plan dfg targets ps)).ps_stack
Proof
  strip_tac >> simp[reorder_plan_def] >>
  metis_tac[alias_reorder_fold_bounds]
QED

Theorem alias_var_mass_reorder_plan:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (reorder_plan dfg targets ps)) <= alias_var_mass x ps
Proof
  strip_tac >> simp[reorder_plan_def] >>
  metis_tac[alias_reorder_fold_bounds]
QED

Theorem alias_var_budget_reorder_plan:
  LENGTH targets <= LENGTH ps.ps_stack /\ alias_var_budget pending ps ==>
  alias_var_budget pending (SND (reorder_plan dfg targets ps))
Proof
  rw[alias_var_budget_def] >>
  drule_then (qspecl_then [`x`, `dfg`] assume_tac)
    (GEN_ALL alias_var_mass_reorder_plan) >>
  first_x_assum (qspec_then `x` mp_tac) >> decide_tac
QED

Theorem alias_var_mass_pop:
  alias_var_mass x (ps with ps_stack := stack_pop n ps.ps_stack) +
  LIST_ELEM_COUNT (Var x) (top_n n ps.ps_stack) = alias_var_mass x ps
Proof
  `TAKE (LENGTH ps.ps_stack - n) ps.ps_stack ++ top_n n ps.ps_stack =
   ps.ps_stack` by
    (Cases_on `n <= LENGTH ps.ps_stack`
     >- simp[top_n_def, GSYM rich_listTheory.LASTN_def,
             rich_listTheory.LASTN_DROP, TAKE_DROP] >>
     `LENGTH ps.ps_stack <= n` by decide_tac >>
     simp[top_n_def, TAKE_LENGTH_TOO_LONG]) >>
  pop_assum (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
  simp[elem_count_append, alias_var_mass_def, stack_pop_def] >> decide_tac
QED

Theorem alias_var_budget_pop_window:
  alias_var_budget (pending ++ consumed) ps /\
  (!x. LIST_ELEM_COUNT (Var x) consumed <=
       LIST_ELEM_COUNT (Var x) (top_n n ps.ps_stack)) ==>
  alias_var_budget pending (ps with ps_stack := stack_pop n ps.ps_stack)
Proof
  rw[alias_var_budget_def] >>
  first_x_assum (qspec_then `x` assume_tac) >>
  first_x_assum (qspec_then `x` mp_tac) >>
  mp_tac alias_var_mass_pop >> simp[elem_count_append] >> decide_tac
QED

Theorem alias_var_budget_reorder_pop:
  qs = SND (reorder_plan dfg targets ps) /\
  LENGTH targets <= LENGTH ps.ps_stack /\
  alias_var_budget (pending ++ consumed) ps /\
  (!x. LIST_ELEM_COUNT (Var x) consumed <=
       LIST_ELEM_COUNT (Var x) (top_n n qs.ps_stack)) ==>
  alias_var_budget pending (qs with ps_stack := stack_pop n qs.ps_stack)
Proof
  strip_tac >> irule alias_var_budget_pop_window >>
  qexists_tac `consumed` >> simp[] >>
  metis_tac[alias_var_budget_reorder_plan]
QED

Theorem alias_var_mass_emit_one:
  !opc live op ps x.
  alias_var_mass x (SND (emit_one_input opc live op ps)) <=
  alias_var_mass x ps + (if op = Var x then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[emit_one_input_def, is_var_operand_def, alias_var_mass_push]
  >~ [`SOPushLabel l`] >-
    (Cases_on `opc = INVOKE` >> simp[alias_var_mass_push]) >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps1 = alias_var_mass x ps` by
    (Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var s))` >>
     gvs[] >> metis_tac[alias_var_mass_restore, pairTheory.SND]) >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var s) ps1.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  pairarg_tac >> simp[] >>
  drule_then (qspec_then `x` mp_tac) (GEN_ALL alias_var_mass_dup) >>
  gvs[]
QED

Theorem alias_var_mass_emit_inputs:
  !inputs opc live ps x.
  alias_var_mass x (SND (emit_input_plan opc inputs live ps)) <=
  alias_var_mass x ps + LIST_ELEM_COUNT (Var x) inputs
Proof
  Induct >> simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`opc`, `live`, `ps1`, `x`] mp_tac) >>
  qspecl_then [`opc`, `operand_vars inputs ++ live`, `h`, `ps`, `x`]
    mp_tac alias_var_mass_emit_one >>
  gvs[] >> Cases_on `h = Var x` >> simp[LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem alias_var_mass_emit_inputs_dead:
  !inputs opc live ps x. ~MEM x live ==>
  alias_var_mass x (SND (emit_input_plan opc inputs live ps)) +
    (if MEM (Var x) inputs then 1 else 0) <=
  alias_var_mass x ps + LIST_ELEM_COUNT (Var x) inputs
Proof
  `!ops v. MEM v (dfgDefs$operand_vars ops) <=> MEM (Var v) ops` by
    (Induct >> simp[dfgDefsTheory.operand_vars_def] >>
     rpt gen_tac >> Cases_on `h` >>
     simp[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def]) >>
  Induct >> simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> strip_tac >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`opc`, `live`, `ps1`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `h = Var x`
  >- (gvs[] >> Cases_on `MEM (Var x) inputs`
      >- (qspecl_then [`opc`, `operand_vars inputs ++ live`, `Var x`, `ps`, `x`]
            mp_tac alias_var_mass_emit_one >>
          gvs[LIST_ELEM_COUNT_THM] >> decide_tac) >>
      `~MEM x (operand_vars inputs ++ live)` by
        simp[passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
      qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
      simp[emit_one_input_def, is_var_operand_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      `alias_var_mass x ps1 = alias_var_mass x ps` by
        (Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var x))` >>
         gvs[] >> metis_tac[alias_var_mass_restore, pairTheory.SND]) >>
      simp[LIST_ELEM_COUNT_THM] >> decide_tac) >>
  qspecl_then [`opc`, `operand_vars inputs ++ live`, `h`, `ps`, `x`]
    mp_tac alias_var_mass_emit_one >>
  simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `MEM (Var x) inputs` >> gvs[] >> decide_tac
QED

Theorem alias_emit_reorder_pop_var_support:
  alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) inputs) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  emit_input_plan opc inputs live ps = (iops,mid) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  plan_holds (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)
         (Var x) ==> MEM x live
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `PERM inputs targets` by metis_tac[PERM_SYM] >>
  `!op. MEM op inputs /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[plan_holds_def] >>
  drule_all alias_emit_reorder_consumed_window >> strip_tac >>
  `LENGTH targets = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `alias_var_mass x qs <= alias_var_mass x mid` by
    (mp_tac (Q.INST [`targets` |-> `targets`, `ps` |-> `mid`,
                    `dfg` |-> `dfg`, `x` |-> `x`] alias_var_mass_reorder_plan) >>
     simp[]) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs_dead >> simp[] >> strip_tac >>
  `alias_var_mass x qs =
   alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) +
   LIST_ELEM_COUNT (Var x) inputs` by
    (drule perm_operand_counts >> strip_tac >>
     qpat_x_assum `qs.ps_stack = _`
       (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
     simp[alias_var_mass_def, elem_count_append] >> decide_tac) >>
  `0 < alias_var_mass x
     (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)` by
    (gvs[plan_holds_def, alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM] >>
     decide_tac) >>
  Cases_on `MEM (Var x) inputs`
  >- (gvs[] >> decide_tac) >>
  `~plan_holds ps (Var x)` by metis_tac[] >>
  `alias_var_mass x ps = 0` by
    gvs[plan_holds_def, alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM] >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem alias_emit_reorder_pop_support:
  alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) inputs) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  emit_input_plan opc inputs live ps = (iops,mid) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  !x. plan_holds (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)
         (Var x) ==> MEM x live
Proof
  simp[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  irule alias_emit_reorder_pop_var_support >> metis_tac[]
QED

Theorem alias_var_budget_emit_inputs:
  alias_var_budget pending ps ==>
  alias_var_budget (pending ++ inputs) (SND (emit_input_plan opc inputs live ps))
Proof
  simp[alias_var_budget_def, elem_count_append] >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs >> decide_tac
QED

Theorem alias_popmany_singleton_inventory:
  plan_holds (SND (popmany_plan [v] ps)) at ==> plan_holds ps at
Proof
  Cases_on `stack_get_depth v ps.ps_stack` >>
  simp[popmany_plan_def, is_contiguous_top_def, popmany_individual_def,
       QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `x = 0`
  >- (gvs[plan_holds_def, stack_pop_def] >> metis_tac[MEM_TAKE]) >>
  Cases_on `x = 1` >> gvs[] >> pairarg_tac >> simp[] >>
  `!a. MEM a ps'.ps_stack \/ a IN FDOM ps'.ps_spilled ==>
       MEM a ps.ps_stack \/ a IN FDOM ps.ps_spilled` by
    metis_tac[do_swap_inventory_subset] >>
  simp[plan_holds_def, stack_pop_def] >> metis_tac[MEM_TAKE]
QED

Theorem alias_phi_singleton_consumed:
  inputs = FILTER is_var_operand inst.inst_operands /\
  ret = Var (HD inst.inst_outputs) /\
  FILTER (\at. MEM at inputs) ps.ps_stack = [Var v] /\
  MEM (Var v) inputs /\ ~MEM v next_liveness /\ ~MEM ret inputs /\
  (!at. MEM at inputs ==> at NOTIN FDOM ps.ps_spilled) ==>
  !at. MEM at inputs ==>
    ~plan_holds (SND (generate_phi_plan inst next_liveness is_halting ps)) at
Proof
  strip_tac >>
  `?d. stack_get_phi_depth inputs ps.ps_stack = SOME d /\
       stack_peek d ps.ps_stack = Var v /\
       (!at. MEM at inputs ==> ~MEM at (stack_poke d ret ps.ps_stack))` by
    metis_tac[alias_phi_singleton_poke] >>
  `!at. MEM at inputs ==>
      ~plan_holds (ps with ps_stack := stack_poke d ret ps.ps_stack) at` by
    (simp[plan_holds_def] >> metis_tac[]) >>
  gvs[] >> simp[generate_phi_plan_def, operand_to_string_def] >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >> rpt strip_tac >>
      metis_tac[alias_popmany_singleton_inventory, pairTheory.SND]) >>
  simp[]
QED
(* Generic projection for spill release; unlike the specialized stack
   theorem in fnFrameBoundaryGenRet this also describes arbitrary deletion
   batches, without importing the frame-simulation dependency chain. *)
Theorem alias_release_fold_fields:
  !xs ps.
    (FOLDL (\ps' (op,off).
       ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps xs).ps_stack = ps.ps_stack /\
    (!at. at IN FDOM (FOLDL (\ps' (op,off).
       ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps xs).ps_spilled <=>
      at IN FDOM ps.ps_spilled /\ ~MEM at (MAP FST xs))
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  metis_tac[]
QED

Theorem alias_release_dead_spills_domain:
  at IN FDOM (release_dead_spills live ps).ps_spilled <=>
    at IN FDOM ps.ps_spilled /\ (?v. at = Var v /\ MEM v live)
Proof
  Cases_on `at` >>
  simp[release_dead_spills_def, alias_release_fold_fields, MEM_MAP, MEM_FILTER,
       pairTheory.FORALL_PROD, alistTheory.MEM_pair_fmap_to_alist_FLOOKUP] >>
  metis_tac[finite_mapTheory.flookup_thm]
QED

Theorem release_dead_spills_plan_holds:
  MEM x live /\ plan_holds ps (Var x) ==>
  plan_holds (release_dead_spills live ps) (Var x)
Proof
  simp[plan_holds_def, release_dead_spills_def, alias_release_fold_fields,
       alias_release_dead_spills_domain]
QED

Theorem optimistic_swap_plan_holds:
  optimistic_swap_plan dfg inst live next_term ps = (ops,qs) /\
  plan_holds ps at ==> plan_holds qs at
Proof
  simp[optimistic_swap_plan_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  metis_tac[do_swap_plan_holds]
QED

Theorem alias_var_mass_release_dead_spills:
  alias_var_mass x (release_dead_spills live ps) <= alias_var_mass x ps
Proof
  `(release_dead_spills live ps).ps_stack = ps.ps_stack` by
    simp[release_dead_spills_def, alias_release_fold_fields] >>
  simp[alias_var_mass_def, alias_release_dead_spills_domain] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[] >>
  Cases_on `MEM x live` >> simp[]
QED

Theorem alias_emit_ops_inventory:
  (SND (generate_emit_ops inst topics ps)).ps_stack = ps.ps_stack /\
  (SND (generate_emit_ops inst topics ps)).ps_spilled = ps.ps_spilled
Proof
  rw[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[asmIRTheory.venom_to_evm_name_def, fresh_label_def]
  >~ [`FILTER is_label_operand inst.inst_operands`] >- suspend "jnz"
  >~ [`FILTER is_label_operand inst.inst_operands`] >- suspend "jnz"
  >~ [`HD inst.inst_operands`] >- suspend "invoke"
  >~ [`HD inst.inst_operands`] >- suspend "invoke"
  >> suspend "jmp"
QED

Resume alias_emit_ops_inventory[jnz]:
  markerLib.RESUME_TAC >>
  Cases_on `FILTER is_label_operand inst.inst_operands` >> simp[] >>
  rename1 `h::t` >> Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >> rename1 `h::t` >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Resume alias_emit_ops_inventory[invoke]:
  markerLib.RESUME_TAC >>
  Cases_on `HD inst.inst_operands` >> simp[]
QED

Resume alias_emit_ops_inventory[jmp]:
  markerLib.RESUME_TAC >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::t` >> Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Finalise alias_emit_ops_inventory

Theorem alias_var_mass_emit_ops:
  alias_var_mass x (SND (generate_emit_ops inst topics ps)) = alias_var_mass x ps
Proof
  simp[alias_var_mass_def, alias_emit_ops_inventory]
QED

Theorem pop_foldl_body_plan_holds:
  at <> v /\ plan_holds ps at ==>
  plan_holds (SND (pop_foldl_body (ops,ps) v)) at
Proof
  strip_tac >> Cases_on `stack_get_depth v ps.ps_stack`
  >- simp[pop_foldl_body_def] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  simp[pop_foldl_body_def] >> IF_CASES_TAC >> simp[]
  >- (gvs[plan_holds_def] >> disj1_tac >>
      irule stack_pop_retains_noninputs >> simp[] >>
      qexists_tac `[stack_peek 0 ps.ps_stack]` >> simp[]) >>
  pairarg_tac >> simp[] >>
  `plan_holds ps1 at` by metis_tac[do_swap_plan_holds] >>
  `ps1.ps_stack = stack_swap x ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >>
  `0 < LENGTH ps1.ps_stack /\ stack_peek 0 ps1.ps_stack = v` by
    (simp[stack_swap_def, stack_peek_def, EL_LUPDATE] >>
     gvs[stack_peek_def]) >>
  gvs[plan_holds_def] >> disj1_tac >>
  irule stack_pop_retains_noninputs >> simp[] >>
  qexists_tac `[stack_peek x ps.ps_stack]` >> simp[]
QED

Theorem pop_fold_plan_holds:
  !dead ops ps. ~MEM at dead /\ plan_holds ps at ==>
  plan_holds (SND (FOLDL pop_foldl_body (ops,ps) dead)) at
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  first_x_assum irule >> simp[] >>
  mp_tac (Q.INST [`v` |-> `h`] pop_foldl_body_plan_holds) >> simp[]
QED

Theorem popmany_individual_plan_holds:
  !dead ps at. ~MEM at dead /\ plan_holds ps at ==>
  plan_holds (SND (popmany_individual dead ps)) at
Proof
  rpt gen_tac >> simp[popmany_individual_eq_foldl] >> strip_tac >>
  irule pop_fold_plan_holds >> simp[QSORT_MEM]
QED

Theorem popmany_plan_plan_holds:
  ~MEM at to_pop /\ plan_holds ps at ==>
  plan_holds (SND (popmany_plan to_pop ps)) at
Proof
  strip_tac >> Cases_on `to_pop` >- simp[popmany_plan_def] >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC >- metis_tac[popmany_individual_plan_holds] >>
  reverse IF_CASES_TAC >- metis_tac[popmany_individual_plan_holds] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  `!d. 1 <= d /\ d <= LENGTH (h::t) ==>
       MEM (stack_peek d ps.ps_stack) (h::t)` by
    (rpt strip_tac >>
     `MEM d (GENLIST SUC (LENGTH (h::t)))` by
       (simp[MEM_GENLIST] >> qexists_tac `d - 1` >> simp[] >> fs[] >> decide_tac) >>
     `MEM d (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) (h::t)))` by
       (fs[is_contiguous_top_def] >>
        qpat_x_assum `QSORT _ _ = _` (mp_tac o Q.AP_TERM `MEM d`) >>
        BETA_TAC >> pure_rewrite_tac[QSORT_MEM, MEM] >> metis_tac[]) >>
     qpat_x_assum `MEM d (MAP THE _)`
       (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
     rule_assum_tac (CONV_RULE (DEPTH_CONV BETA_CONV)) >>
     rename1 `y = stack_get_depth v ps.ps_stack` >>
     `IS_SOME (stack_get_depth v ps.ps_stack)` by
       (fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
     Cases_on `stack_get_depth v ps.ps_stack` >> gvs[] >>
     drule_then strip_assume_tac stack_get_depth_props >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `plan_holds ps' at` by metis_tac[do_swap_plan_holds] >>
  `ps'.ps_stack = stack_swap (SUC (LENGTH t)) ps.ps_stack` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`]
       doSwapSimTheory.do_swap_stack_result) >> fs[]) >>
  gvs[plan_holds_def] >> disj1_tac >>
  irule stack_pop_retains_noninputs >> simp[] >>
  qexists_tac `h::t` >> simp[] >>
  rpt strip_tac >>
  (simp[stack_peek_def, stack_swap_def, EL_LUPDATE] >>
   IF_CASES_TAC
   >- (first_x_assum (qspec_then `SUC (LENGTH t)` mp_tac) >>
       simp[stack_peek_def]) >>
   `1 <= i` by (Cases_on `i` >> fs[]) >>
   first_x_assum (qspec_then `i` mp_tac) >> simp[stack_peek_def])
QED

Theorem alias_var_mass_pop_foldl_body:
  alias_var_mass x (SND (pop_foldl_body (ops,ps) v)) <= alias_var_mass x ps
Proof
  simp[pop_foldl_body_def] >>
  Cases_on `stack_get_depth v ps.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  IF_CASES_TAC >> simp[]
  >- (mp_tac (Q.INST [`n` |-> `1`] alias_var_mass_pop) >> decide_tac) >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps1 = alias_var_mass x ps` by
    metis_tac[alias_var_mass_swap, pairTheory.SND] >>
  mp_tac (Q.INST [`n` |-> `1`, `ps` |-> `ps1`] alias_var_mass_pop) >>
  decide_tac
QED

Theorem alias_var_mass_pop_fold:
  !xs ops ps.
    alias_var_mass x (SND (FOLDL pop_foldl_body (ops,ps) xs)) <= alias_var_mass x ps
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  first_x_assum (qspecl_then [`q`, `r`] mp_tac) >>
  mp_tac (Q.INST [`v` |-> `h`] alias_var_mass_pop_foldl_body) >>
  simp[] >> decide_tac
QED

Theorem alias_var_mass_popmany_individual:
  alias_var_mass x (SND (popmany_individual to_pop ps)) <= alias_var_mass x ps
Proof
  simp[popmany_individual_eq_foldl, alias_var_mass_pop_fold]
QED

Theorem alias_var_mass_popmany:
  alias_var_mass x (SND (popmany_plan to_pop ps)) <= alias_var_mass x ps
Proof
  Cases_on `to_pop` >- simp[popmany_plan_def] >>
  simp[popmany_plan_def] >>
  IF_CASES_TAC >> simp[alias_var_mass_popmany_individual] >>
  IF_CASES_TAC >> simp[alias_var_mass_popmany_individual] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  fs[] >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps' = alias_var_mass x ps` by
    metis_tac[alias_var_mass_swap, pairTheory.SND] >>
  mp_tac (Q.INST [`n` |-> `SUC (LENGTH (t:operand list))`, `ps` |-> `ps'`] alias_var_mass_pop) >>
  decide_tac
QED

Theorem alias_unique_take_absent:
  LIST_ELEM_COUNT at stk <= 1 /\ i < LENGTH stk /\ k <= i /\ EL i stk = at ==>
  ~MEM at (TAKE k stk)
Proof
  strip_tac >>
  `MEM at (DROP k stk)` by
    (simp[MEM_EL] >> qexists_tac `i - k` >>
     simp[EL_DROP] >> `k + (i - k) = i` by decide_tac >> simp[]) >>
  `LIST_ELEM_COUNT at (TAKE k stk) + LIST_ELEM_COUNT at (DROP k stk) <= 1` by
    metis_tac[TAKE_DROP, elem_count_append] >>
  fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem alias_pop_foldl_body_deletes:
  LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (pop_foldl_body (ops,ps) at)).ps_stack
Proof
  strip_tac >> Cases_on `stack_get_depth at ps.ps_stack`
  >- (simp[pop_foldl_body_def] >>
      fs[stack_get_depth_NONE] >> strip_tac >> fs[MEM_EL] >>
      first_x_assum (qspec_then `LENGTH ps.ps_stack - 1 - n` mp_tac) >>
      simp[stack_peek_def] >>
      `LENGTH ps.ps_stack - 1 - (LENGTH ps.ps_stack - 1 - n) = n` by decide_tac >>
      simp[]) >>
  drule_then strip_assume_tac stack_get_depth_props >>
  simp[pop_foldl_body_def] >> IF_CASES_TAC >> simp[]
  >- (simp[stack_pop_def] >> irule alias_unique_take_absent >> simp[] >>
      qexists_tac `LENGTH ps.ps_stack - 1` >>
      gvs[stack_peek_def]) >>
  pairarg_tac >> simp[] >>
  `ps1.ps_stack = stack_swap x ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >>
  `LIST_ELEM_COUNT at ps1.ps_stack <= 1` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity, pairTheory.SND] >>
  gvs[] >> simp[stack_pop_def] >> irule alias_unique_take_absent >> simp[] >>
  qexists_tac `LENGTH ps.ps_stack - 1` >>
  simp[] >> simp[stack_swap_def, EL_LUPDATE, stack_peek_def] >>
  gvs[stack_peek_def]
QED

Theorem alias_pop_foldl_body_count:
  LIST_ELEM_COUNT at (SND (pop_foldl_body (ops,ps) v)).ps_stack <=
  LIST_ELEM_COUNT at ps.ps_stack
Proof
  `!stk:operand list. !n. LIST_ELEM_COUNT at (stack_pop n stk) <= LIST_ELEM_COUNT at stk` by
    (simp[stack_pop_def] >> rpt gen_tac >>
     `LIST_ELEM_COUNT at (TAKE (LENGTH stk - n) stk) +
      LIST_ELEM_COUNT at (DROP (LENGTH stk - n) stk) = LIST_ELEM_COUNT at stk` by
       metis_tac[elem_count_append, TAKE_DROP] >> decide_tac) >>
  Cases_on `stack_get_depth v ps.ps_stack` >> simp[pop_foldl_body_def] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[] >>
  `LIST_ELEM_COUNT at ps1.ps_stack = LIST_ELEM_COUNT at ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity, pairTheory.SND] >>
  metis_tac[]
QED

Theorem alias_pop_fold_count:
  !xs ops ps. LIST_ELEM_COUNT at (SND (FOLDL pop_foldl_body (ops,ps) xs)).ps_stack <=
    LIST_ELEM_COUNT at ps.ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  first_x_assum (qspecl_then [`q`, `r`] mp_tac) >>
  mp_tac (Q.INST [`v` |-> `h`] alias_pop_foldl_body_count) >> simp[] >> decide_tac
QED

Theorem alias_pop_fold_deletes:
  !xs ops ps. MEM at xs /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
    ~MEM at (SND (FOLDL pop_foldl_body (ops,ps) xs)).ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  `LIST_ELEM_COUNT at ps.ps_stack <= 1` by metis_tac[] >>
  `LIST_ELEM_COUNT at r.ps_stack <= LIST_ELEM_COUNT at ps.ps_stack` by
    metis_tac[alias_pop_foldl_body_count, pairTheory.SND] >>
  Cases_on `at = h`
  >- (`~MEM at r.ps_stack` by metis_tac[alias_pop_foldl_body_deletes, pairTheory.SND] >>
      mp_tac (Q.SPECL [`xs`, `q`, `r`] alias_pop_fold_count) >>
      gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  first_x_assum irule >> gvs[] >> decide_tac
QED

Theorem alias_popmany_individual_deletes:
  MEM at to_pop /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (popmany_individual to_pop ps)).ps_stack
Proof
  simp[popmany_individual_eq_foldl] >> strip_tac >>
  irule alias_pop_fold_deletes >> simp[QSORT_MEM]
QED

Theorem alias_popmany_contiguous_depth:
  MEM at to_pop /\
  EVERY IS_SOME (MAP (\v. stack_get_depth v stk) to_pop) /\
  is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v stk) to_pop)) ==>
  ?d. stack_get_depth at stk = SOME d /\ 1 <= d /\ d <= LENGTH to_pop
Proof
  strip_tac >>
  `IS_SOME (stack_get_depth at stk)` by (fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  Cases_on `stack_get_depth at stk` >> fs[] >>
  `MEM x (MAP THE (MAP (\v. stack_get_depth v stk) to_pop))` by
    (simp[MEM_MAP] >> qexists_tac `SOME x` >> simp[] >>
     qexists_tac `at` >> simp[]) >>
  fs[is_contiguous_top_def] >>
  `MEM x (GENLIST SUC (LENGTH to_pop))` by metis_tac[QSORT_MEM] >>
  fs[MEM_GENLIST] >> decide_tac
QED

Theorem alias_popmany_plan_deletes:
  MEM at to_pop /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (popmany_plan to_pop ps)).ps_stack
Proof
  disch_tac >> Cases_on `to_pop` >- fs[] >>
  `MEM at (h::t) /\ LIST_ELEM_COUNT at ps.ps_stack <= 1` by metis_tac[] >>
  qpat_x_assum `MEM _ _ /\ _` kall_tac >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC
  >- metis_tac[alias_popmany_individual_deletes] >>
  reverse IF_CASES_TAC
  >- metis_tac[alias_popmany_individual_deletes] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  `?d. stack_get_depth at ps.ps_stack = SOME d /\ 1 <= d /\ d <= LENGTH (h::t)` by
    (irule alias_popmany_contiguous_depth >> simp[]) >>
  drule_then strip_assume_tac stack_get_depth_props >>
  pairarg_tac >> simp[] >>
  `ps'.ps_stack = stack_swap (SUC (LENGTH t)) ps.ps_stack` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`] doSwapSimTheory.do_swap_stack_result) >>
     fs[]) >>
  `LIST_ELEM_COUNT at ps'.ps_stack <= 1` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`]
       doSwapSimTheory.do_swap_multiplicity) >> simp[] >>
     impl_tac >- fs[] >> disch_then (qspec_then `at` mp_tac) >> simp[]) >>
  suspend "positions"
QED

Resume alias_popmany_plan_deletes[positions]:
  markerLib.RESUME_TAC >>
  simp[stack_pop_def] >> irule alias_unique_take_absent >>
  conj_tac >- gvs[] >>
  qexists_tac `if d = SUC (LENGTH t) then LENGTH ps.ps_stack - 1
              else LENGTH ps.ps_stack - 1 - d` >>
  simp[] >>
  `LENGTH ps'.ps_stack = LENGTH ps.ps_stack` by simp[] >>
  `EL (if d = SUC (LENGTH t) then LENGTH ps.ps_stack - 1
       else LENGTH ps.ps_stack - 1 - d) ps'.ps_stack = at` by
    (Cases_on `d = SUC (LENGTH t)` >>
     `LENGTH ps.ps_stack - 1 - SUC (LENGTH t) <> LENGTH ps.ps_stack - 1` by
       (fs[] >> decide_tac) >>
     simp[stack_swap_def, EL_LUPDATE] >>
     gvs[stack_peek_def] >>
     `LENGTH ps.ps_stack - 1 - d <> LENGTH ps.ps_stack - 1` by decide_tac >>
     `LENGTH ps.ps_stack - 1 - d <> LENGTH ps.ps_stack - 1 - SUC (LENGTH t)` by
       (fs[] >> decide_tac) >> simp[]) >>
  gvs[] >> decide_tac
QED

Finalise alias_popmany_plan_deletes

Theorem alias_pop_fold_mass_zero:
  !xs ops ps. MEM (Var x) xs /\ alias_var_mass x ps <= 1 /\
    Var x NOTIN FDOM ps.ps_spilled ==>
    alias_var_mass x (SND (FOLDL pop_foldl_body (ops,ps) xs)) = 0
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  `alias_var_mass x ps <= 1 /\ Var x NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
  `alias_var_mass x r <= alias_var_mass x ps` by
    metis_tac[alias_var_mass_pop_foldl_body, pairTheory.SND] >>
  `Var x NOTIN FDOM r.ps_spilled` by
    (qpat_x_assum `pop_foldl_body _ _ = _` mp_tac >>
     Cases_on `stack_get_depth h ps.ps_stack`
     >- (simp[pop_foldl_body_def] >> strip_tac >> gvs[]) >>
     simp[pop_foldl_body_def] >> IF_CASES_TAC >> simp[]
     >- (strip_tac >> gvs[]) >>
     pairarg_tac >> simp[] >>
     strip_tac >> gvs[] >>
     metis_tac[do_swap_spilled_unchanged, pairTheory.SND]) >>
  Cases_on `Var x = h`
  >- (`LIST_ELEM_COUNT (Var x) ps.ps_stack <= 1` by
        fs[alias_var_mass_def] >>
      `~MEM (Var x) r.ps_stack` by
        metis_tac[alias_pop_foldl_body_deletes, pairTheory.SND] >>
      `alias_var_mass x r = 0` by
        (gvs[alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM]) >>
      mp_tac (Q.SPECL [`xs`, `q`, `r`] alias_var_mass_pop_fold) >> simp[]) >>
  first_x_assum irule >> gvs[] >> decide_tac
QED

Theorem alias_popmany_plan_mass_zero:
  MEM (Var x) to_pop /\ alias_var_mass x ps <= 1 /\
    Var x NOTIN FDOM ps.ps_spilled ==>
  alias_var_mass x (SND (popmany_plan to_pop ps)) = 0
Proof
  disch_tac >>
  `MEM (Var x) to_pop /\ alias_var_mass x ps <= 1 /\
   Var x NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
  qpat_x_assum `MEM _ _ /\ _` kall_tac >>
  `LIST_ELEM_COUNT (Var x) ps.ps_stack <= 1` by fs[alias_var_mass_def] >>
  `~MEM (Var x) (SND (popmany_plan to_pop ps)).ps_stack` by
    metis_tac[alias_popmany_plan_deletes] >>
  Cases_on `to_pop` >- fs[] >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC
  >- (simp[popmany_individual_eq_foldl] >> irule alias_pop_fold_mass_zero >>
      simp[QSORT_MEM]) >>
  reverse IF_CASES_TAC
  >- (simp[popmany_individual_eq_foldl] >> irule alias_pop_fold_mass_zero >>
      simp[QSORT_MEM]) >>
  pairarg_tac >> simp[] >>
  `ps'.ps_spilled = ps.ps_spilled` by
    metis_tac[do_swap_spilled_unchanged, pairTheory.SND] >>
  qpat_x_assum `~MEM _ (SND _).ps_stack` mp_tac >>
  simp[Once popmany_plan_def] >> simp[] >>
  simp[alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem alias_var_mass_optimistic_swap:
  alias_var_mass x (SND (optimistic_swap_plan dfg inst live next_term ps)) <=
  alias_var_mass x ps
Proof
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  simp[alias_var_mass_swap]
QED

Theorem alias_var_mass_outputs:
  !outs ps.
    alias_var_mass x (FOLDL (\ps' out.
      ps' with ps_stack := stack_push (Var out) ps'.ps_stack) ps outs) =
    alias_var_mass x ps + LIST_ELEM_COUNT x outs
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> simp[alias_var_mass_push] >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_DEF] >> decide_tac
QED

Theorem alias_var_mass_zero:
  alias_var_mass x ps = 0 <=> ~plan_holds ps (Var x)
Proof
  simp[alias_var_mass_def, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[]
QED

Theorem alias_emit_reorder_pop_mass:
  emit_input_plan opc inputs live ps = (iops,mid) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) <=
  alias_var_mass x ps
Proof
  strip_tac >>
  `PERM inputs targets` by metis_tac[PERM_SYM] >>
  `!op. MEM op inputs /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[plan_holds_def] >>
  drule_all alias_emit_reorder_consumed_window >> strip_tac >>
  `LENGTH targets = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `alias_var_mass x qs <= alias_var_mass x mid` by
    (mp_tac (Q.INST [`targets` |-> `targets`, `ps` |-> `mid`,
                    `dfg` |-> `dfg`, `x` |-> `x`] alias_var_mass_reorder_plan) >>
     simp[]) >>
  `alias_var_mass x qs =
   alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) +
   LIST_ELEM_COUNT (Var x) inputs` by
    (drule perm_operand_counts >> strip_tac >>
     qpat_x_assum `qs.ps_stack = _`
       (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
     simp[alias_var_mass_def, elem_count_append] >> decide_tac) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs >> simp[] >> decide_tac
QED

Theorem alias_regular_postprocess_holds:
  generate_emit_ops inst topics
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      consumed inst.inst_outputs) = (eops,emitted) /\
  (if inst.inst_outputs <> [] /\ (~is_halting \/ LENGTH inst.inst_outputs > 1)
   then popmany_plan (MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)) emitted
   else ([],emitted)) = (pops,post) /\
  MEM x live /\ (plan_holds consumed (Var x) \/ MEM x inst.inst_outputs) ==>
  plan_holds post (Var x)
Proof
  strip_tac >>
  `plan_holds emitted (Var x)` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs] >>
     strip_tac >> spose_not_then assume_tac >>
     `alias_var_mass x emitted = 0` by metis_tac[alias_var_mass_zero] >>
     `alias_var_mass x consumed <> 0 \/ LIST_ELEM_COUNT x inst.inst_outputs > 0` by
       metis_tac[alias_var_mass_zero, LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  (mp_tac (Q.INST [`at` |-> `Var x`, `ps` |-> `emitted`,
     `to_pop` |-> `MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)`]
     popmany_plan_plan_holds) >> simp[MEM_MAP, MEM_FILTER])
QED

Theorem alias_regular_plan_stages:
  inst.inst_opcode <> JMP /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  ?iops mid targets rops reordered topics eops emitted pops post.
    emit_input_plan inst.inst_opcode (compute_operands inst) live ps = (iops,mid) /\
    PERM targets (compute_operands inst) /\
    reorder_plan dfg targets mid = (rops,reordered) /\
    generate_emit_ops inst topics
      (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
        (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
        inst.inst_outputs) = (eops,emitted) /\
    (if inst.inst_outputs <> [] /\ (~is_halting \/ LENGTH inst.inst_outputs > 1)
     then popmany_plan (MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)) emitted
     else ([],emitted)) = (pops,post) /\
    (!x. alias_var_mass x qs <= alias_var_mass x post) /\
    (!x. MEM x live /\ plan_holds post (Var x) ==> plan_holds qs (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def] >>
  pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics` >>
  pairarg_tac >> simp[] >>
  `?targets. PERM targets (compute_operands inst) /\
     reorder_plan dfg targets ps1 = (reorder_ops,ps4)` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[]
     >- (pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
         IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
         >- metis_tac[PERM_REFL] >>
         `2 <= LENGTH (compute_operands inst)` by decide_tac >>
         drule last_two_reorder_perm >> metis_tac[PERM_SYM]) >>
     metis_tac[PERM_REFL]) >>
  qpat_x_assum `(if _ then _ else _) = _` kall_tac >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[] >>
      qexistsl_tac [`targets`, `reorder_ops`, `ps4`, `topics`, `emit_ops`, `ps7`] >>
      simp[] >> conj_tac
      >- (gen_tac >> mp_tac (Q.INST [`ps` |-> `ps7`]
            alias_var_mass_release_dead_spills) >> simp[]) >>
      metis_tac[release_dead_spills_plan_holds]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `!x. alias_var_mass x ps9 <= alias_var_mass x ps8` by
    (gen_tac >> qpat_x_assum `(if _ then _ else _) = (_,ps9)` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[alias_var_mass_optimistic_swap, pairTheory.SND]) >>
  `!at. plan_holds ps8 at ==> plan_holds ps9 at` by
    (gen_tac >> qpat_x_assum `(if _ then _ else _) = (_,ps9)` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[optimistic_swap_plan_holds, pairTheory.SND]) >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`targets`, `reorder_ops`, `ps4`, `topics`, `emit_ops`, `ps7`, `pop_ops`, `ps8`] >>
  simp[] >> conj_tac
  >- (gen_tac >>
      mp_tac (Q.INST [`ps` |-> `ps9`] alias_var_mass_release_dead_spills) >>
      first_x_assum (qspec_then `x` mp_tac) >> decide_tac) >>
  metis_tac[release_dead_spills_plan_holds]
QED

Theorem alias_regular_plan_forward_stages:
  inst.inst_opcode <> JMP /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  ?iops mid selected rops reordered.
    emit_input_plan inst.inst_opcode (compute_operands inst) live ps = (iops,mid) /\
    PERM selected (compute_operands inst) /\
    reorder_plan dfg selected mid = (rops,reordered) /\
    (!x. MEM x live /\
      (plan_holds (reordered with ps_stack :=
         stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack) (Var x) \/
       MEM x inst.inst_outputs) ==> plan_holds qs (Var x))
Proof
  strip_tac >> drule_all alias_regular_plan_stages >> strip_tac >>
  qexistsl_tac [`iops`, `mid`, `targets`, `rops`, `reordered`] >> simp[] >>
  rpt strip_tac >>
  `plan_holds post (Var x)` by
    (drule_at (Pos hd) alias_regular_postprocess_holds >>
     disch_then drule >> simp[]) >>
  metis_tac[]
QED

Theorem alias_regular_plan_holds_live:
  inst.inst_opcode <> JMP /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) /\
  MEM x live /\ (plan_holds ps (Var x) \/ MEM x inst.inst_outputs) ==>
  plan_holds qs (Var x)
Proof
  strip_tac >> (drule_all alias_regular_plan_forward_stages >> strip_tac >>
  reverse (Cases_on `plan_holds ps (Var x)`)
  >- metis_tac[] >>
  `PERM (compute_operands inst) selected` by metis_tac[PERM_SYM] >>
  `LENGTH selected = LENGTH (compute_operands inst)` by metis_tac[PERM_LENGTH] >>
  `plan_holds (reordered with ps_stack :=
     stack_pop (LENGTH selected) reordered.ps_stack) (Var x)` by
    metis_tac[alias_emit_reorder_consume_live] >>
  metis_tac[])
QED

Theorem alias_entry_live_param_output:
  codegen_ready_fn fn /\
  MEM x (live_vars_at (liveness_analyze fn)
    (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
  MEM x (MAP (\inst. HD inst.inst_outputs)
    (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  strip_tac >>
  `fn.fn_blocks <> []` by
    (gvs[codegen_ready_fn_def, callLayoutDefsTheory.canonical_param_prefix_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  Cases_on `fn.fn_blocks` >> gvs[] >>
  rename1 `fn.fn_blocks = entry::rest` >>
  `lookup_block entry.bb_label fn.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  `collect_phis entry.bb_instructions = []` by
    (gvs[codegen_ready_fn_def, block_entries_ready_def, entry_block_def, NULL_EQ]) >>
  `alias_path_available fn entry.bb_label
    (LENGTH (get_params entry.bb_instructions)) x` by
    (irule alias_live_available_after_phis >> simp[] >>
     gvs[codegen_ready_fn_def]) >>
  qpat_x_assum `alias_path_available _ _ _ _` mp_tac >>
  simp[alias_path_available_def] >>
  disch_then (qspec_then `[entry.bb_label]` mp_tac) >>
  simp[is_fn_path_def, fn_entry_label_def, entry_block_def] >>
  strip_tac >> gvs[] >>
  qspec_then `entry.bb_instructions` strip_assume_tac get_params_suffix >>
  `MEM (EL j entry.bb_instructions) (get_params entry.bb_instructions)` by
    (irule (iffRL MEM_EL) >> qexists_tac `j` >> simp[] >>
     qpat_x_assum `entry.bb_instructions = _ ++ _`
       (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th)))) >>
     simp[EL_APPEND1]) >>
  `param_insts_from 0 (get_params entry.bb_instructions)` by
    (drule canonical_get_params_layout >> simp[]) >>
  drule param_insts_flat_outputs >> disch_then (SUBST1_TAC o SYM) >>
  simp[MEM_FLAT, MEM_MAP] >>
  metis_tac[inst_defs_def]
QED

Theorem alias_prepare_params_holds_output:
  MEM x (MAP (\inst. HD inst.inst_outputs)
    (get_params (HD fn.fn_blocks).bb_instructions)) /\
  MEM x (live_vars_at liveness (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
  plan_holds (SND (prepare_params_plan liveness fn ps)) (Var x)
Proof
  strip_tac >>
  simp[prepare_params_plan_def, parameter_stack_fold] >>
  IF_CASES_TAC >- gvs[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  irule optimistic_swap_plan_holds >> goal_assum (drule_at Any) >>
  qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `popmany_plan dead_names prepared_state` >>
  `~MEM (Var x) dead_names /\ plan_holds prepared_state (Var x)` by
    (simp[Abbr `dead_names`, Abbr `prepared_state`, MEM_FILTER,
          operand_to_string_def, plan_holds_def, MEM_MAP] >>
     gvs[MEM_MAP] >> metis_tac[]) >>
  drule popmany_plan_plan_holds >>
  metis_tac[pairTheory.SND]
QED

Theorem alias_prepare_params_entry_demand:
  codegen_ready_fn fn /\
  MEM x (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
  plan_holds (SND (prepare_params_plan (liveness_analyze fn) fn ps)) (Var x)
Proof
  metis_tac[alias_prepare_params_holds_output, alias_entry_live_param_output]
QED

Theorem stack_poke_retains_other:
  MEM at stk /\ stack_peek d stk <> at ==>
  MEM at (stack_poke d ret stk)
Proof
  simp[MEM_EL, stack_peek_def, stack_poke_def, EL_LUPDATE] >>
  metis_tac[]
QED

Theorem alias_phi_plan_holds_live:
  MEM x live /\ plan_holds ps (Var x) ==>
  plan_holds (SND (generate_phi_plan inst live halting ps)) (Var x)
Proof
  strip_tac >> Cases_on `stack_get_phi_depth
    (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- simp[generate_phi_plan_def] >>
  rename1 `_ = SOME d` >>
  `d < LENGTH ps.ps_stack` by
    (gvs[stack_get_phi_depth_def] >> drule planWfTheory.stack_find_bound >> simp[]) >>
  simp[generate_phi_plan_def] >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) live` >> simp[]
  >- (Cases_on `do_dup d ps` >> simp[] >>
      `r.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
        metis_tac[doSwapSimTheory.do_dup_stack_exact, pairTheory.SND] >>
      `r.ps_spilled = ps.ps_spilled` by
        (Cases_on `d <= 15` >>
         gvs[do_dup_def] >> rpt (pairarg_tac >> gvs[])) >>
      `plan_holds (r with ps_stack := stack_poke 0 (Var (HD inst.inst_outputs)) r.ps_stack) (Var x)` by
        gvs[plan_holds_def, stack_poke_def, LUPDATE_APPEND2] >>
      IF_CASES_TAC
      >- (pairarg_tac >> simp[] >>
          `~MEM (Var x) [Var (HD inst.inst_outputs)]` by
            (simp[] >> metis_tac[]) >>
          metis_tac[popmany_plan_plan_holds, pairTheory.SND]) >>
      gvs[]) >>
  `stack_peek d ps.ps_stack <> Var x` by
    (strip_tac >> gvs[operand_to_string_def]) >>
  `plan_holds (ps with ps_stack := stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack) (Var x)` by
    (gvs[plan_holds_def] >> metis_tac[stack_poke_retains_other]) >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >>
      `~MEM (Var x) [Var (HD inst.inst_outputs)]` by
            (simp[] >> metis_tac[]) >>
      metis_tac[popmany_plan_plan_holds, pairTheory.SND]) >>
  gvs[]
QED

Theorem alias_phi_plan_holds_output:
  inst.inst_outputs = [out] /\ MEM out live /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d ==>
  plan_holds (SND (generate_phi_plan inst live halting ps)) (Var out)
Proof
  strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (gvs[stack_get_phi_depth_def] >> drule planWfTheory.stack_find_bound >> simp[]) >>
  simp[generate_phi_plan_def] >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) live` >> simp[]
  >- (Cases_on `do_dup d ps` >> simp[] >>
      `r.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
        metis_tac[doSwapSimTheory.do_dup_stack_exact, pairTheory.SND] >>
      simp[plan_holds_def, stack_poke_def, LUPDATE_APPEND2]) >>
  simp[plan_holds_def, stack_poke_def] >>
  disj1_tac >> irule (iffRL MEM_EL) >>
  qexists_tac `LENGTH ps.ps_stack - 1 - d` >> simp[EL_LUPDATE]
QED

Theorem alias_jmp_plan_holds_live:
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
  inst.inst_outputs = [] /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) /\
  MEM x live /\ plan_holds ps (Var x) ==> plan_holds qs (Var x)
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, is_label_operand_def, emit_input_plan_def,
       planWfTheory.reorder_plan_nil, stack_pop_def] >>
  Cases_on `join_target_ops liveness fn lbl inst` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      irule release_dead_spills_plan_holds >> simp[] >>
      gvs[plan_holds_def] >>
      metis_tac[alias_emit_ops_inventory, pairTheory.SND]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qpat_x_assum `(\(restore_ops,ps1'). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `plan_holds ps1' (Var x)` by metis_tac[restore_spilled_plan_holds] >>
  `plan_holds ps2 (Var x)` by metis_tac[reorder_plan_holds] >>
  strip_tac >> gvs[] >> irule release_dead_spills_plan_holds >> simp[] >>
  gvs[plan_holds_def] >> metis_tac[alias_emit_ops_inventory, pairTheory.SND]
QED

Theorem alias_probe_large_regular_arity:
  inst_wf (mk_inst 0 INVOKE (Label "callee" :: REPLICATE 17 (Lit 0w)) []) /\
  ~codegen_ready_inst (mk_inst 0 INVOKE (Label "callee" :: REPLICATE 17 (Lit 0w)) []) /\
  LENGTH (compute_operands (mk_inst 0 INVOKE (Label "callee" :: REPLICATE 17 (Lit 0w)) [])) = 17 /\
  inst_wf (mk_inst 1 LOG (Lit (17w:256 word) :: REPLICATE 19 (Lit 0w)) []) /\
  ~codegen_ready_inst (mk_inst 1 LOG (Lit (17w:256 word) :: REPLICATE 19 (Lit 0w)) []) /\
  LENGTH (compute_operands (mk_inst 1 LOG (Lit (17w:256 word) :: REPLICATE 19 (Lit 0w)) [])) = 19
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem alias_regular_plan_var_support:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  plan_holds qs (Var x) ==> MEM x live \/ MEM x inst.inst_outputs
Proof
  strip_tac >> drule_all alias_regular_plan_stages >> strip_tac >>
  `plan_holds (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
     (Var x) ==> MEM x live` by
    (strip_tac >> drule_all alias_emit_reorder_pop_var_support >> simp[]) >>
  strip_tac >> spose_not_then assume_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack) = 0` by
    metis_tac[alias_var_mass_zero] >>
  `alias_var_mass x emitted = 0` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs] >>
     `LIST_ELEM_COUNT x inst.inst_outputs = 0` by
       (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >> simp[]) >>
  `alias_var_mass x post <= alias_var_mass x emitted` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     mp_tac (Q.INST [`ps` |-> `emitted`, `to_pop` |-> `MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)`] alias_var_mass_popmany) >>
     simp[]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >>
  `alias_var_mass x qs <> 0` by metis_tac[alias_var_mass_zero] >> decide_tac
QED

Theorem alias_regular_plan_support:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  !x. plan_holds qs (Var x) ==> MEM x live \/ MEM x inst.inst_outputs
Proof
  rpt strip_tac >> irule alias_regular_plan_var_support >>
  fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> metis_tac[]
QED

Theorem alias_regular_plan_var_mass:
  inst.inst_opcode <> JMP /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_mass x qs <= alias_var_mass x ps + LIST_ELEM_COUNT x inst.inst_outputs
Proof
  strip_tac >> drule_all alias_regular_plan_stages >> strip_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
    <= alias_var_mass x ps` by
    (drule_all alias_emit_reorder_pop_mass >> simp[]) >>
  `alias_var_mass x emitted <= alias_var_mass x ps + LIST_ELEM_COUNT x inst.inst_outputs` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs]) >>
  `alias_var_mass x post <= alias_var_mass x emitted` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[alias_var_mass_popmany, pairTheory.SND]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >> decide_tac
QED

Theorem alias_regular_plan_var_budget:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  LIST_ELEM_COUNT x inst.inst_outputs <= 1 /\
  (MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_mass x qs <= 1
Proof
  strip_tac >> drule_all alias_regular_plan_var_mass >>
  disch_then (qspec_then `x` mp_tac) >>
  Cases_on `MEM x inst.inst_outputs`
  >- (`alias_var_mass x ps = 0` by metis_tac[alias_var_mass_zero] >> simp[]) >>
  `LIST_ELEM_COUNT x inst.inst_outputs = 0` by
    (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >> simp[]
QED

Theorem alias_distinct_output_count:
  !xs:string list. !x. ALL_DISTINCT xs ==> LIST_ELEM_COUNT x xs <= 1
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
  >- (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem alias_regular_plan_budget:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  ALL_DISTINCT inst.inst_outputs /\
  (!x. MEM x inst.inst_outputs ==>
    ~plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst)) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_budget [] qs
Proof
  strip_tac >> simp[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> gen_tac >>
  irule alias_regular_plan_var_budget >>
  fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >>
  metis_tac[alias_distinct_output_count]
QED

Theorem alias_regular_plan_var_live_support:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  LIST_ELEM_COUNT x inst.inst_outputs <= 1 /\
  (MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)) /\
  (~is_halting \/ LENGTH inst.inst_outputs > 1) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  plan_holds qs (Var x) ==> MEM x live
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  strip_tac >> spose_not_then assume_tac >>
  `MEM x inst.inst_outputs` by
    (drule_all alias_regular_plan_var_support >> simp[]) >>
  `alias_var_mass x ps = 0` by metis_tac[alias_var_mass_zero] >>
  drule_all alias_regular_plan_stages >> strip_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack) = 0` by
    (drule_all alias_emit_reorder_pop_mass >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `alias_var_mass x residual = 0` >>
  `alias_var_mass x emitted <= 1` by
    (qpat_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs]) >>
  `Var x NOTIN FDOM emitted.ps_spilled` by
    (`!outs p. (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
       p outs).ps_spilled = p.ps_spilled` by (Induct >> simp[]) >>
     `Var x NOTIN FDOM residual.ps_spilled` by
       (qpat_x_assum `alias_var_mass x residual = 0` mp_tac >>
        simp[alias_var_mass_def] >> IF_CASES_TAC >> simp[]) >>
     qpat_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. (SND p).ps_spilled``) >>
     simp[alias_emit_ops_inventory] >> metis_tac[]) >>
  `inst.inst_outputs <> []` by (strip_tac >> fs[]) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[] >> strip_tac >>
  `alias_var_mass x post = 0` by
    (`MEM (Var x) (MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs))` by
       simp[MEM_MAP, MEM_FILTER] >>
     drule_all alias_popmany_plan_mass_zero >> simp[]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >>
  `alias_var_mass x qs <> 0` by metis_tac[alias_var_mass_zero] >> decide_tac
QED

Theorem alias_regular_plan_live_support:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  ALL_DISTINCT inst.inst_outputs /\
  (!x. MEM x inst.inst_outputs ==>
    ~plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst)) /\
  (~is_halting \/ 1 < LENGTH inst.inst_outputs) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  !x. plan_holds qs (Var x) ==> MEM x live
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `alias_var_mass x ps <= 1` by fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >>
  `LIST_ELEM_COUNT x inst.inst_outputs <= 1` by metis_tac[alias_distinct_output_count] >>
  `MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)` by simp[] >>
  `plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)` by simp[] >>
  drule_all (SRULE [arithmeticTheory.GREATER_DEF] alias_regular_plan_var_live_support) >> simp[]
QED

Definition alias_collision_fn_def:
  alias_collision_fn = mk_raw_function "collision"
    [<| bb_label := "E"; bb_instructions :=
       [mk_inst 0 ASSIGN [Lit 7w] ["x"];
        mk_inst 1 ASSIGN [Lit 9w] ["y"];
        mk_inst 2 CALLDATASIZE [] ["c"];
        mk_inst 3 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions := [mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions := [mk_inst 5 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
       [mk_inst 6 PHI [Label "A"; Var "x"; Label "B"; Var "y"] ["p"];
        mk_inst 7 ASSIGN [Var "x"] ["q"];
        mk_inst 8 JMP [Label "K"] []] |>;
     <| bb_label := "K"; bb_instructions :=
       [mk_inst 9 MSTORE [Lit 0w; Var "p"] [];
        mk_inst 10 MSTORE [Lit 32w; Var "q"] [];
        mk_inst 11 STOP [] []] |>]
End

Theorem alias_collision_normalize:
  normalize_operand (dfg_build_function alias_collision_fn) [] (Var "x") = Lit 7w
Proof
  EVAL_TAC
QED

Theorem alias_collision_ready_probe:
  ~codegen_ready_fn alias_collision_fn
Proof
  simp[codegen_ready_fn_def] >> EVAL_TAC
QED

Theorem alias_collision_phi_obstruction:
  ~phi_operands_ready alias_collision_fn
Proof
  EVAL_TAC
QED

Definition alias_none_fn_def:
  alias_none_fn = mk_raw_function "none_probe"
    [<| bb_label := "E"; bb_instructions :=
       [mk_inst 0 ASSIGN [Lit 7w] ["x"];
        mk_inst 1 ASSIGN [Lit 9w] ["y"];
        mk_inst 2 CALLDATASIZE [] ["c"];
        mk_inst 3 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions := [mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions := [mk_inst 5 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
       [mk_inst 7 ASSIGN [Var "x"] ["q"];
        mk_inst 8 JMP [Label "K"] []] |>;
     <| bb_label := "K"; bb_instructions :=
       [mk_inst 10 MSTORE [Lit 32w; Var "q"] [];
        mk_inst 11 STOP [] []] |>]
End

Theorem alias_none_ready:
  codegen_ready_fn alias_none_fn /\
  normalize_operand (dfg_build_function alias_none_fn) [] (Var "x") = Lit 7w
Proof
  EVAL_TAC
QED


Theorem alias_input_vars_no_phis:
  collect_phis instrs = [] ==>
  input_vars_from pred instrs live = live
Proof
  simp[input_vars_from_def]
QED

Theorem alias_entry_demand_collision_probe:
  input_vars_from "b"
    [mk_inst 10 PHI [Label "a"; Var "x"; Label "b"; Var "y"] ["p"];
     mk_inst 11 ASSIGN [Var "x"] ["q"]] ["x"; "y"] = ["y"] /\
  ~MEM "x" (input_vars_from "b"
    [mk_inst 10 PHI [Label "a"; Var "x"; Label "b"; Var "y"] ["p"];
     mk_inst 11 ASSIGN [Var "x"] ["q"]] ["x"; "y"]) /\
  MEM "x" (inst_uses (mk_inst 11 ASSIGN [Var "x"] ["q"]))
Proof
  EVAL_TAC
QED

(* Entry-demand producer audit (C1.20.3).
   alias_entry_demand_collision_probe checks a genuine omission from the
   selected-input list, NOT an omission from a reachable planner state.
   Thus membership of x in ordinary uses does not justify invoking the
   frozen selected-input ownership premise. In this example that premise
   gives heldness/equality of y only. If x is already held, the separate
   frozen equality premise DOES give its entry alias equality.

   Existing interfaces do not supply that missing antecedent:
   - alias_input_vars_from_partition is elimination from membership in
     input_vars_from, not introduction of ordinary survivors.
   - alias_build_phi_maps_absent_uses requires the source-map lookup to be
     NONE (plus well-formed PHIs). Here x has a SOME lookup, so this theorem
     cannot remove the collision.
   - alias_phi_plan_holds_live requires MEM x live AND plan_holds ps (Var x).
     It preserves existing heldness; it cannot establish entry heldness.
   - alias_phi_plan_holds_output requires a singleton output, output liveness
     AND a successful stack_get_phi_depth. It does not produce x in this
     example, where x is an input, not the PHI output p.
   generate_phi_plan itself returns ps unchanged if stack_get_phi_depth is
   NONE. Otherwise it renames a found stack source, duplicating it first
   when that source is live afterwards; spills are not searched as sources.
   Consequently it preserves an already-held ordinary survivor but supplies
   no independent entry-heldness producer for an omitted survivor.

   Required unresolved implication: for every ordinary survivor actually
   needed by the eventual semantic proof but omitted by input_vars_from,
   derive plan_holds ps (Var x) from the frozen lineage/block-plan premises,
   or prove that this survivor need not be demanded to establish any final
   held alias. No unconditional physical PHI demand is implied by this audit.

   NONE audit: lineage_state's entry/step constructors mention planner
   states, CFG and DFS plans only; neither mentions a runtime state or
   vs_prev_bb. lineage_entry names a static predecessor but the frozen
   theorem assumes lineage_state, not its correspondence to vs_prev_bb.
   Therefore prev=NONE must not be identified with function entry. With no
   PHIs alias_input_vars_no_phis computes input_vars_from as identity, but
   the frozen selected-input ownership premise is still vacuous when prev
   is NONE. The same missing heldness-or-unneeded-demand implication must
   cover that case. This audit supplies no target counterexample and does
   not validate the proposed universal live-prefix base case.
*)

Definition alias_probe_phis_def:
  alias_probe_phis =
    [mk_inst 10 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"];
     mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]]
End

Theorem alias_probe_phi_static_edges:
  phi_uses_disjoint alias_probe_phis /\
  input_vars_from "left" alias_probe_phis ["a"; "b"; "c"; "d"; "r"] = ["a"; "c"; "r"] /\
  input_vars_from "right" alias_probe_phis ["a"; "b"; "c"; "d"; "r"] = ["b"; "d"; "r"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_prefix_ownership:
  (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
    ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_stack =
    [Var "r"; Var "c"] /\
  FILTER (\at. MEM at [Var "c"; Var "d"])
    (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
      ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_stack =
    [Var "c"] /\
  (SND (generate_phi_plan (EL 1 alias_probe_phis) ["q"; "r"] F
    (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
      ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))))).ps_stack =
    [Var "r"; Var "q"] /\
  (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
    ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_prefix_live_and_spilled:
  (SND (generate_phi_plan (EL 1 alias_probe_phis) ["p"; "q"; "r"] F
    (SND (generate_phi_plan (HD alias_probe_phis) ["p"; "c"; "r"] F
      ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))))).ps_stack =
    [Var "r"; Var "p"; Var "q"] /\
  (SND (generate_phi_plan (EL 1 alias_probe_phis) ["p"; "q"; "r"] F
    (SND (generate_phi_plan (HD alias_probe_phis) ["p"; "c"; "r"] F
      ((init_plan_state 0) with <| ps_stack := [Var "r"; Var "a"];
        ps_spilled := FEMPTY |+ (Var "c",0) |>))))).ps_stack =
    [Var "r"; Var "p"]
Proof
  EVAL_TAC
QED

(* Input disjointness alone supplies neither output freshness nor static
   edge choice. In loops SSA alone also permits an output on a backedge.
   A proposed freshness proof must additionally use phi_block_ready's
   dead-after-prefix condition and a liveness witness from the backedge;
   that proof remains an obligation, not a consequence of these fixtures. *)
Theorem alias_probe_phi_disjoint_not_fresh:
  phi_uses_disjoint
    [mk_inst 10 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["c"];
     mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]] /\
  MEM (Var "c") (FILTER is_var_operand
    (mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]).inst_operands)
Proof
  EVAL_TAC
QED

(* Proposed remaining-PHI preservation interface: disjoint selected input
   lists A,B, FILTER A stack = [Var a], FILTER B stack = [Var b], no
   incoming spill keys, a dead at this step, output not in A or B and not
   already held. After the step FILTER B stack = [Var b], no B spills,
   and no A held (the latter is alias_phi_singleton_consumed).
   Output freshness needs its own codegen_ready/SSA/liveness boundary.
   Poke preserves the B filter, but optional pop can move the B slot;
   preserve a FILTER singleton, not its absolute depth. The computation
   above exercises that movement with a carried residual r. *)


Theorem plan_holds_cleanup_update[simp]:
  plan_holds
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) at
  <=> plan_holds ps at
Proof
  simp[plan_holds_def]
QED

Theorem plan_holds_inventory_update[simp]:
  plan_holds (ps with <| ps_stack := stk; ps_spilled := spilled |>) at
  <=> MEM at stk \/ at IN FDOM spilled
Proof
  simp[plan_holds_def]
QED

Theorem plan_holds_init_cleanup[simp]:
  ~plan_holds (init_cleanup_plan_state ch growth spill_base lbl_ctr) at
Proof
  simp[plan_holds_def, init_cleanup_plan_state_def, init_plan_state_def]
QED

(* A successful PHI plan does not, by itself, establish demand coverage. *)
Theorem generate_phi_plan_absent_slot:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack =
    NONE ==>
  generate_phi_plan inst next_liveness is_halting ps = ([], ps)
Proof
  simp[generate_phi_plan_def]
QED

(* OFFSET bypasses dead-output filtering. Such names must not be confused
   with nontrivial ASSIGN aliases by a static support invariant. *)
Theorem generate_offset_plan_holds_output:
  inst.inst_operands = [Lit n; Label lbl] /\ inst.inst_outputs = [out] ==>
  plan_holds (SND (generate_offset_plan inst ps)) (Var out)
Proof
  simp[generate_offset_plan_def, plan_holds_def, stackModelTheory.stack_push_def]
QED

(* Reachable JNZ spill/PHI diagnostic. Root names are deliberately distinct. *)
Definition alias_spill_probe_names_def:
  alias_spill_probe_names =
    ["x0"; "x1"; "x2"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
     "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18"; "x19"]
End

Definition alias_spill_probe_fn_def:
  alias_spill_probe_fn = mk_raw_function "alias_spill_probe"
    [<| bb_label := "E"; bb_instructions :=
      MAPi (\i v. mk_inst i CALLDATASIZE [] [v]) alias_spill_probe_names ++
      [mk_inst 20 ADD [Var "x0"; Var "x1"] ["c"];
       mk_inst 21 JNZ [Var "c"; Label "S"; Label "P"] []] |>;
     <| bb_label := "P"; bb_instructions :=
      [mk_inst 22 PHI [Label "E"; Var "x18"] ["p"];
       mk_inst 23 ASSIGN [Var "p"] ["q"]] ++
      MAPi (\i v. mk_inst (24+i) MSTORE [Lit (n2w (32*i)); Var v] [])
        ("q" :: FILTER (\v. v <> "x18") (TL (TL alias_spill_probe_names))) ++
      [mk_inst 43 STOP [] []] |>;
     <| bb_label := "S"; bb_instructions := [mk_inst 44 STOP [] []] |>]
End

Definition alias_spill_probe_live_def:
  alias_spill_probe_live = liveness_analyze alias_spill_probe_fn
End

Theorem alias_spill_probe_rejected:
  ~phis_at_joins (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn /\
  ~codegen_ready_fn alias_spill_probe_fn
Proof
  EVAL_TAC
QED

Definition alias_spill_probe_entry_result_def:
  alias_spill_probe_entry_result = generate_block_plan
    alias_spill_probe_live (dfg_build_function alias_spill_probe_fn)
    (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn
    (HD alias_spill_probe_fn.fn_blocks) (init_cleanup_plan_state NONE [] 0 0)
End

val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY]);

Theorem alias_spill_probe_edge_demand:
  cfg_succs_of (cfg_analyze alias_spill_probe_fn) "E" = ["P"; "S"] /\
  cfg_preds_of (cfg_analyze alias_spill_probe_fn) "P" = ["E"] /\
  MEM "x18" (live_vars_at alias_spill_probe_live "E" 22) /\
  MEM "x18" (input_vars_from "E"
    (EL 1 alias_spill_probe_fn.fn_blocks).bb_instructions
    (live_vars_at alias_spill_probe_live "P" 0))
Proof
  EVAL_TAC
QED

Theorem alias_spill_probe_selected_phi:
  MEM (mk_inst 22 PHI [Label "E"; Var "x18"] ["p"])
    (collect_phis (EL 1 alias_spill_probe_fn.fn_blocks).bb_instructions) /\
  MEM ("E", "x18") (phi_pairs [Label "E"; Var "x18"])
Proof
  EVAL_TAC
QED

(* Keep release opaque until its concrete live-key premise can be checked. *)
fun alias_release_conv tm =
  let
    val (_, args) = strip_comb tm
    val th = SPECL args jp_release_live
    val hyp = fst (dest_imp (concl th))
    val hth = EQT_ELIM
      ((SIMP_CONV (srw_ss())
          [finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FDOM_FEMPTY,
           boolTheory.DISJ_IMP_THM, boolTheory.FORALL_AND_THM] THENC EVAL) hyp)
  in MP th hth end;
val alias_rel_c = ``stackPlanOps$release_dead_spills``;
val () =
  let
    val rules = List.concat (List.concat (map
      (fn (_,xs) => map (fn clauses.RRules ths => ths
                          | clauses.Conversion _ => []) xs)
      (computeLib.listItems (computeLib.the_compset ()))))
    val callers = List.filter (fn th =>
      let val (_,body) = strip_forall (concl th)
          val (_,r) = boolSyntax.dest_eq body
      in can (find_term (aconv alias_rel_c)) r end
      handle HOL_ERR _ => false) rules
  in
    computeLib.del_funs [stackPlanOpsTheory.release_dead_spills_def];
    computeLib.add_convs [(alias_rel_c,2,alias_release_conv)];
    computeLib.add_funs callers
  end;

Definition alias_none_e_def:
  alias_none_e = THE (generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (HD alias_none_fn.fn_blocks) (init_cleanup_plan_state NONE [] 0 0))
End

Definition alias_none_a_def:
  alias_none_a = THE (generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (EL 2 alias_none_fn.fn_blocks) (SND alias_none_e))
End

Theorem alias_none_e_plan:
  generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (HD alias_none_fn.fn_blocks) (init_cleanup_plan_state NONE [] 0 0) =
    SOME alias_none_e
Proof
  EVAL_TAC
QED

Theorem alias_none_a_plan:
  generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (EL 2 alias_none_fn.fn_blocks) (SND alias_none_e) = SOME alias_none_a
Proof
  EVAL_TAC
QED

Theorem alias_none_inventory_probe:
  plan_holds (SND alias_none_a) (Var "x")
Proof
  EVAL_TAC
QED

Theorem alias_none_cfg_edges:
  cfg_succs_of (cfg_analyze alias_none_fn) "E" = ["B"; "A"] /\
  cfg_succs_of (cfg_analyze alias_none_fn) "B" = ["J"]
Proof
  EVAL_TAC
QED

Theorem alias_none_dfs_a:
  dfs_aux_call (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) ["B"] ["E"] (SND alias_none_e)
Proof
  `SND alias_none_e = (SND alias_none_e) with
    <|ps_stack := (SND alias_none_e).ps_stack;
      ps_spilled := (SND alias_none_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >>
  qexists_tac `["A"]` >>
  rewrite_tac[GSYM (cj 1 alias_none_cfg_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`HD alias_none_fn.fn_blocks`, `FST alias_none_e`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[alias_none_e_plan] >> conj_tac >- EVAL_TAC >>
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_none_dfs_j:
  dfs_aux_call (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) ["J"] ["B"; "E"] (SND alias_none_a)
Proof
  `SND alias_none_a = (SND alias_none_a) with
    <|ps_stack := (SND alias_none_a).ps_stack;
      ps_spilled := (SND alias_none_a).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >>
  qexists_tac `[]` >>
  rewrite_tac[GSYM (cj 2 alias_none_cfg_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 2 alias_none_fn.fn_blocks`, `FST alias_none_a`,
    `SND alias_none_e`, `[]`] >>
  simp[alias_none_a_plan, alias_none_dfs_a] >> EVAL_TAC
QED

Theorem alias_none_dfs_states:
  dfs_block_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "E" (init_cleanup_plan_state NONE [] 0 0) /\
  dfs_block_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "B" (SND alias_none_e) /\
  dfs_block_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "J" (SND alias_none_a)
Proof
  rewrite_tac[dfs_block_state_def] >> conj_tac
  >- (qexistsl_tac [`[]`,`[]`] >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC) >>
  conj_tac
  >- (qexistsl_tac [`[]`,`["E"]`] >> simp[alias_none_dfs_a]) >>
  qexistsl_tac [`[]`,`["B"; "E"]`] >> simp[alias_none_dfs_j]
QED

Theorem alias_none_lineage_b:
  lineage_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "B" (SND alias_none_e)
Proof
  `SND alias_none_e = (SND alias_none_e) with
    <|ps_stack := (SND alias_none_e).ps_stack;
      ps_spilled := (SND alias_none_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >>
  simp[alias_none_dfs_states] >>
  qexistsl_tac [`HD alias_none_fn.fn_blocks`, `FST alias_none_e`, `NONE`, `"E"`, `F`,
    `init_cleanup_plan_state NONE [] 0 0`, `init_cleanup_plan_state NONE [] 0 0`,
    `SND alias_none_e`] >>
  simp[alias_none_dfs_states, alias_none_e_plan, alias_none_cfg_edges] >>
  conj_tac >- EVAL_TAC >>
  reverse conj_tac
  >- (irule lineage_state_entry >> EVAL_TAC) >>
  `init_cleanup_plan_state NONE [] 0 0 with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    init_cleanup_plan_state NONE [] 0 0` by
      simp[init_cleanup_plan_state_def] >>
  simp[alias_none_e_plan]
QED

Theorem alias_none_lineage_j:
  lineage_state (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (init_cleanup_plan_state NONE [] 0 0) "J" (SND alias_none_a)
Proof
  `SND alias_none_a = (SND alias_none_a) with
    <|ps_stack := (SND alias_none_a).ps_stack;
      ps_spilled := (SND alias_none_a).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >>
  simp[alias_none_dfs_states] >>
  qexistsl_tac [`EL 2 alias_none_fn.fn_blocks`, `FST alias_none_a`, `NONE`, `"B"`, `F`,
    `SND alias_none_e`, `SND alias_none_e`, `SND alias_none_a`] >>
  simp[alias_none_dfs_states, alias_none_a_plan, alias_none_cfg_edges,
       alias_none_lineage_b] >> EVAL_TAC
QED

Theorem alias_none_selected_input:
  input_vars_from "B" (EL 3 alias_none_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_none_fn) "J" 0) = ["x"] /\
  LENGTH (cfg_preds_of (cfg_analyze alias_none_fn) "J") = 2
Proof
  EVAL_TAC
QED

Definition alias_none_regular_def:
  alias_none_regular = generate_regular_inst_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (mk_inst 7 ASSIGN [Var "x"] ["q"])
    (live_vars_at (liveness_analyze alias_none_fn) "J" 1) F T "J" (SND alias_none_a)
End

Theorem alias_none_regular_inventory:
  plan_holds (SND alias_none_a) (Var "x") /\
  plan_holds (SND alias_none_regular) (Var "q")
Proof
  EVAL_TAC
QED

Definition alias_none_j_result_def:
  alias_none_j_result = generate_block_plan (liveness_analyze alias_none_fn)
    (dfg_build_function alias_none_fn) (cfg_analyze alias_none_fn) alias_none_fn
    (EL 3 alias_none_fn.fn_blocks) (SND alias_none_a)
End

Theorem alias_none_final_inventory:
  IS_SOME alias_none_j_result /\
  plan_holds (SND (THE alias_none_j_result)) (Var "q")
Proof
  EVAL_TAC
QED

Theorem alias_spill_probe_entry_fields:
  IS_SOME alias_spill_probe_entry_result /\
  ~MEM (Var "x18") (SND (THE alias_spill_probe_entry_result)).ps_stack /\
  Var "x18" IN FDOM (SND (THE alias_spill_probe_entry_result)).ps_spilled
Proof
  EVAL_TAC
QED

Definition alias_spill_probe_after_def:
  alias_spill_probe_after = SND (THE alias_spill_probe_entry_result)
End

Theorem alias_spill_probe_entry_plan:
  generate_block_plan alias_spill_probe_live
    (dfg_build_function alias_spill_probe_fn) (cfg_analyze alias_spill_probe_fn)
    alias_spill_probe_fn (HD alias_spill_probe_fn.fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0) =
    SOME (FST (THE alias_spill_probe_entry_result), alias_spill_probe_after)
Proof
  rewrite_tac[GSYM alias_spill_probe_entry_result_def, alias_spill_probe_after_def] >>
  mp_tac alias_spill_probe_entry_fields >>
  Cases_on `alias_spill_probe_entry_result` >> simp[]
QED

Theorem alias_spill_probe_first_edge:
  dfs_block_state alias_spill_probe_live (dfg_build_function alias_spill_probe_fn)
    (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn
    (init_cleanup_plan_state NONE [] 0 0) "P" alias_spill_probe_after
Proof
  simp[dfs_block_state_def] >>
  qexistsl_tac [`[]`, `["E"]`] >> simp[] >>
  `alias_spill_probe_after = alias_spill_probe_after with
    <|ps_stack := alias_spill_probe_after.ps_stack;
      ps_spilled := alias_spill_probe_after.ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule dfs_aux_call_branch >>
  qexists_tac `["S"]` >>
  rewrite_tac[GSYM (cj 1 alias_spill_probe_edge_demand)] >>
  irule dfs_aux_call_succs >>
  simp[] >>
  qexistsl_tac [`HD alias_spill_probe_fn.fn_blocks`,
    `FST (THE alias_spill_probe_entry_result)`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[alias_spill_probe_entry_plan] >>
  conj_tac >- EVAL_TAC >>
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_spill_probe_lineage:
  lineage_state alias_spill_probe_live (dfg_build_function alias_spill_probe_fn)
    (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn
    (init_cleanup_plan_state NONE [] 0 0) "P" alias_spill_probe_after
Proof
  `alias_spill_probe_after = alias_spill_probe_after with
    <|ps_stack := alias_spill_probe_after.ps_stack;
      ps_spilled := alias_spill_probe_after.ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule lineage_state_step >>
  conj_tac >- ACCEPT_TAC alias_spill_probe_first_edge >>
  qexistsl_tac [`HD alias_spill_probe_fn.fn_blocks`,
    `FST (THE alias_spill_probe_entry_result)`, `NONE`, `"E"`, `F`,
    `init_cleanup_plan_state NONE [] 0 0`,
    `init_cleanup_plan_state NONE [] 0 0`, `alias_spill_probe_after`] >>
  `init_cleanup_plan_state NONE [] 0 0 with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    init_cleanup_plan_state NONE [] 0 0` by EVAL_TAC >>
  simp[alias_spill_probe_entry_plan, alias_spill_probe_edge_demand] >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `[]`] >>
      simp[] >> irule dfs_aux_call_entry >> EVAL_TAC) >>
  irule lineage_state_entry >> EVAL_TAC
QED

Definition alias_spill_probe_clean_def:
  alias_spill_probe_clean = SND (clean_stack_plan alias_spill_probe_live
    (cfg_analyze alias_spill_probe_fn) alias_spill_probe_fn
    (EL 1 alias_spill_probe_fn.fn_blocks) alias_spill_probe_after)
End

Theorem alias_spill_probe_clean_and_phi:
  alias_spill_probe_clean = alias_spill_probe_after /\
  generate_phi_plan (mk_inst 22 PHI [Label "E"; Var "x18"] ["p"])
    (live_vars_at alias_spill_probe_live "P" 1) T alias_spill_probe_clean =
    ([], alias_spill_probe_clean) /\
  ~plan_holds alias_spill_probe_clean (Var "p")
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition alias_spill_probe_assign_def:
  alias_spill_probe_assign = generate_regular_inst_plan alias_spill_probe_live
    (dfg_build_function alias_spill_probe_fn) (cfg_analyze alias_spill_probe_fn)
    alias_spill_probe_fn (mk_inst 23 ASSIGN [Var "p"] ["q"])
    (live_vars_at alias_spill_probe_live "P" 2) T F "P" alias_spill_probe_clean
End

Theorem alias_spill_probe_assign_fields:
  plan_holds (SND alias_spill_probe_assign) (Var "q") /\
  normalize_operand (dfg_build_function alias_spill_probe_fn) [] (Var "q") = Var "p"
Proof
  EVAL_TAC >> simp[release_dead_spills_def, alias_release_fold_fields]
QED

(* Absent-source end-to-end audit (C1.21.2.1): reuse E0072, not a
   duplicate fixture. alias_spill_probe_clean_and_phi proves that Var p is
   absent from BOTH stack and spill domain (by plan_holds_def). The checked
   alias_spill_probe_assign_fields nevertheless proves that full
   generate_regular_inst_plan retains Var q. Its arguments are explicitly
   alias_spill_probe_live, the built DFG and analyzed CFG of
   alias_spill_probe_fn, instruction 23 ASSIGN p -> q, analyzed next-live
   index 2, first-instruction flag T, halting flag F, label P, and the
   concrete alias_spill_probe_clean state. This is the full planner call,
   not just its consume/push fragment: it includes input emission, reorder
   and optimistic-swap handling. The successful call is not an availability
   certificate. The regular planner pushes outputs after consuming operands;
   missing physical input does not prevent that construction.

   The fixture has a checked static lineage entry (alias_spill_probe_lineage)
   and checked cleanup/PHI behavior, but no general instruction-prefix
   lineage predicate. Here p is a PHI self-root: runtime PHI definition can
   supply its semantic equality without physical heldness. Therefore this
   example does NOT show an alias failure or a frozen-target counterexample.

   Exact residual producer required for the joint proof: whenever full
   regular planning retains an ASSIGN output whose source was not held,
   under the frozen block-entry/lineage/run premises derive semantic framed
   alias equality of that source at the actual runtime instruction prefix
   (or a sufficient backwards trace to initially held equality or a locally
   executed self-root). The producer must cover nontrivial ASSIGN sources,
   not merely this PHI example, and must track intervening root writes.
   Conditional inventory/phi-heldness lemmas require source heldness and
   cannot establish this residual implication. Static lineage constructors
   alone do not relate the runtime predecessor to a chosen static edge.
*)
val () = computeLib.add_funs [stackPlanOpsTheory.release_dead_spills_def];

(* Small computation fixture: an actual DFG, not an assumed equivalence. *)
Definition alias_probe_fn_def:
  alias_probe_fn = mk_raw_function "alias_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [] ["r"];
       mk_inst 1 ASSIGN [Var "r"] ["a"];
       mk_inst 2 STOP [] []] |>]
End

(* Demand diagnostics use analyzed liveness of this actual function. *)
Definition alias_demand_probe_fn_def:
  alias_demand_probe_fn = mk_raw_function "demand_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [] ["r"];
       mk_inst 1 PARAM [] ["k"];
       mk_inst 2 ADD [Var "r"; Var "r"] ["z"];
       mk_inst 3 ADD [Var "z"; Var "k"] ["result"];
       mk_inst 4 STOP [] []] |>]
End

Theorem alias_demand_probe_entry_preparation:
  ~plan_holds (init_cleanup_plan_state NONE [] 0 0) (Var "r") /\
  ~plan_holds (init_cleanup_plan_state NONE [] 0 0) (Var "k") /\
  MEM "r" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 2) /\
  MEM "k" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 2) /\
  (!x. MEM x ["r"; "k"] ==>
    plan_holds (SND (prepare_params_plan (liveness_analyze alias_demand_probe_fn)
      alias_demand_probe_fn (init_cleanup_plan_state NONE [] 0 0))) (Var x))
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem alias_demand_probe_regular_distinct_live:
  MEM "k" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3) /\
  (!x. MEM x ["z"; "k"] ==>
    plan_holds (SND (generate_regular_inst_plan
      (liveness_analyze alias_demand_probe_fn) (dfg_build_function alias_demand_probe_fn)
      (cfg_analyze alias_demand_probe_fn) alias_demand_probe_fn
      (mk_inst 2 ADD [Var "r"; Var "r"] ["z"])
      (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3)
      T F "entry" ((init_plan_state 0) with ps_stack := [Var "k"; Var "r"]))) (Var x)) /\
  (!x. MEM x ["z"; "k"] ==>
    plan_holds (SND (generate_regular_inst_plan
      (liveness_analyze alias_demand_probe_fn) (dfg_build_function alias_demand_probe_fn)
      (cfg_analyze alias_demand_probe_fn) alias_demand_probe_fn
      (mk_inst 2 ADD [Var "r"; Var "r"] ["z"])
      (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3)
      T F "entry" ((init_plan_state 0) with <| ps_stack := [Var "r"];
        ps_spilled := FEMPTY |+ (Var "k",0) |>))) (Var x))
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

(* The published path predicate permits inter-block exits before the terminator.
   This witnesses only an interface limitation, not analyzed liveness. *)
Definition alias_path_probe_fn_def:
  alias_path_probe_fn = mk_raw_function "path_probe"
    [<| bb_label := "A"; bb_instructions :=
       [mk_inst 0 PARAM [] ["r"];
        mk_inst 1 ASSIGN [Var "r"] ["a"];
        mk_inst 2 JMP [Label "B"] []] |>;
     <| bb_label := "B"; bb_instructions :=
       [mk_inst 3 ADD [Var "a"; Lit 1w] ["b"];
        mk_inst 4 STOP [] []] |>]
End

Theorem alias_path_probe_early_exit:
  cfg_exec_path (cfg_analyze alias_path_probe_fn) [("A",0);("B",0)] /\
  used_before_defined alias_path_probe_fn.fn_blocks "a" [("A",0);("B",0)] /\
  normalize_operand (dfg_build_function alias_path_probe_fn) [] (Var "a") =
    Var "r" /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_path_probe_fn) "A" 0)
Proof
  EVAL_TAC >> qexists_tac `1` >> simp[] >> EVAL_TAC
QED

Theorem alias_probe_normalize:
  normalize_operand (dfg_build_function alias_probe_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_slots:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
    [Var "a"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "p"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_live_and_dead:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["a"; "p"] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"; Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_regular_consumption:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ISZERO [Var "a"] ["z"])
    [] F F "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ISZERO [Var "a"] ["z"])
    [] F F "entry" ((init_plan_state 0) with ps_stack := [Var "a"; Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC >> simp[]
QED

(* Boundary fixtures distinguish transient duplicates from retained ownership. *)
Theorem alias_probe_assign_ownership:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["a"; "z"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "z"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["z"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "z"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["a"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    [] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = []
Proof
  EVAL_TAC >> simp[]
QED

Theorem alias_probe_repeated_operands:
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "a"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ADD [Var "a"; Var "a"] ["z"])
    [] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ADD [Var "a"; Var "a"] ["z"])
    ["a"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem alias_probe_live_then_dead:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 5 ISZERO [Var "a"] ["q"])
    ["z"] F T "entry"
    (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
      ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
      ["a"; "z"] F T "entry"
      ((init_plan_state 0) with ps_stack := [Var "a"]))))).ps_stack = [Var "z"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem alias_probe_spill_restore_ownership:
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0)))).ps_stack =
    [Var "a"; Var "a"] /\
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0)))).ps_spilled = FEMPTY /\
  (SND (emit_one_input ADD ["a"] (Var "a")
    ((init_plan_state 0) with ps_stack := Var "a" :: REPLICATE 16 (Lit 0w)))).ps_stack =
    (Var "a" :: REPLICATE 16 (Lit 0w)) ++ [Var "a"] /\
  (SND (emit_one_input ADD ["a"] (Var "a")
    ((init_plan_state 0) with ps_stack := Var "a" :: REPLICATE 16 (Lit 0w)))).ps_spilled = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

(* Candidate interface (not yet a reachable-state invariant):
   At ordinary boundaries each variable has at most one owner, either one
   stack occurrence or a spill key. Constants/markers may repeat freely.
   Inputs actually read must be covered. Emission needs the transient bound
     count x stack <= count x pending + 1
   and, for spilled x, count x stack <= count x pending; these are the
   occurrence clauses of reorderSim.residual_budget_wf. Its slot/allocator
   clauses are extra obligations, not consequences of coverage.
   emit_input_plan_pending_inventory gives a LOWER bound from coverage;
   emit_input_plan_inventory_accumulation is also a LOWER bound and cannot
   establish the desired upper bound. reorder_one_pending_inventory_wf
   preserves that lower bound only assuming residual_budget_wf and pending
   length <= 16. Thus none of these three is a uniqueness theorem.
   Missing transfer: covered demand + per-variable one-owner + fresh outputs
   + valid spill allocation must yield one-owner after reorder/pop/output,
   with dead nontrivial aliases absent except for untouched branch residuals.
   Support for those residuals is edge/cleanup dependent, not plain liveness.
   OFFSET introduces a fresh root even when dead; PARAM introduces no planner
   operand at dispatch. Halting may retain a dead single output. Restrict live
   support to nontrivial aliases at nonhalting boundaries, not all held names.
   These tests validate the local candidate only, not the lineage induction. *)
Theorem alias_probe_halting_retention:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    [] T T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "z"]
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_probe_clean_def:
  alias_probe_clean inputs stk height promised =
    clean_stack_plan
      <| ds_inst := FEMPTY |++ [(("pred",0),["a"; "b"]); (("edge",0),inputs)];
         ds_boundary := FEMPTY |>
      (ARB with <| cfg_preds := FEMPTY |+ ("edge",["pred"]);
                   cfg_succs := FEMPTY |+ ("pred",["edge"; "other"]) |>)
      (mk_raw_function "clean_probe"
        [<| bb_label := "pred"; bb_instructions := [] |>])
      <| bb_label := "edge"; bb_instructions := [] |>
      ((init_plan_state 0) with <| ps_stack := stk;
        ps_cleanup_height := height; ps_cleanup_promised := promised |> )
End

Theorem alias_probe_clean_slots:
  (SND (alias_probe_clean ["b"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [dead_stack_marker; Var "b"] /\
  (SND (alias_probe_clean ["b"] [Var "a"; Var "b"] NONE F)).ps_stack =
    [Var "b"] /\
  (SND (alias_probe_clean ["a"; "b"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [Var "a"; Var "b"] /\
  (SND (alias_probe_clean [] [Var "a"; Var "b"] NONE T)).ps_stack =
    [dead_stack_marker; dead_stack_marker] /\
  (SND (alias_probe_clean ["a"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_jmp_residual:
  (SND (reorder_plan (dfg_build_function alias_probe_fn) [Var "b"]
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
    [Var "a"; Var "b"] /\
  (SND (reorder_plan (dfg_build_function alias_probe_fn) [Var "r"; Var "a"]
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "r"]))).ps_stack =
    [Var "r"; Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_spilled_phi:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0))))
      .ps_spilled = FEMPTY |+ (Var "a",0) /\
  (release_dead_spills []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0))).ps_spilled = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_probe_loop_fn_def:
  alias_probe_loop_fn = mk_raw_function "loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 1 CALLDATASIZE [] ["r"];
          mk_inst 2 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 3 ASSIGN [Var "r"] ["a"];
          mk_inst 4 ISZERO [Var "a"] ["z"];
          mk_inst 5 JNZ [Var "z"; Label "header"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 6 STOP [] []] |>]
End

Theorem alias_probe_loop_liveness:
  ~MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "header" 0) /\
  MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "body" 1) /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "body" 2) /\
  normalize_operand (dfg_build_function alias_probe_loop_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC >> simp[]
QED

(* Without dominance, liveness alone admits a stale alias at a root write. *)
Definition alias_probe_bad_loop_fn_def:
  alias_probe_bad_loop_fn = mk_raw_function "bad_loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 1 CALLDATASIZE [] ["r"];
          mk_inst 2 ISZERO [Var "a"] ["z"];
          mk_inst 3 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 4 ASSIGN [Var "r"] ["a"];
          mk_inst 5 JMP [Label "header"] []] |>]
End

Theorem alias_probe_bad_loop_liveness:
  MEM "a" (live_vars_at (liveness_analyze alias_probe_bad_loop_fn) "header" 0) /\
  normalize_operand (dfg_build_function alias_probe_bad_loop_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC >> simp[]
QED

(* Restricted-ownership probe requested by C1.21.2.6.5. *)
Definition alias_diamond_fn_def:
  alias_diamond_fn = mk_raw_function "alias_diamond"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 CALLDATASIZE [] ["seed"];
          mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 2 PHI [Label "entry"; Var "seed"; Label "backedge"; Var "z"] ["t"];
          mk_inst 3 CALLDATASIZE [] ["r"];
          mk_inst 4 ADD [Var "t"; Var "r"] ["c"];
          mk_inst 5 JNZ [Var "c"; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
         [mk_inst 6 ASSIGN [Var "r"] ["u"];
          mk_inst 7 ASSIGN [Var "c"] ["u2"];
          mk_inst 8 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions :=
         [mk_inst 9 ASSIGN [Var "r"] ["v"];
          mk_inst 10 ASSIGN [Var "c"] ["v2"];
          mk_inst 11 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
         [mk_inst 12 PHI [Label "left"; Var "u"; Label "right"; Var "v"] ["p"];
          mk_inst 13 PHI [Label "left"; Var "u2"; Label "right"; Var "v2"] ["q"];
          mk_inst 14 ADD [Var "p"; Var "q"] ["w"];
          mk_inst 15 ISZERO [Var "w"] ["z"];
          mk_inst 16 JNZ [Var "z"; Label "backedge"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 17 STOP [] []] |>;
     <| bb_label := "backedge"; bb_instructions :=
         [mk_inst 18 JMP [Label "header"] []] |>]
End

Theorem alias_diamond_entries_ready:
  block_entries_ready (cfg_analyze alias_diamond_fn) alias_diamond_fn
Proof
  EVAL_TAC
QED

Theorem alias_diamond_ready:
  codegen_ready_fn alias_diamond_fn
Proof
  EVAL_TAC
QED

Theorem alias_diamond_no_retpc:
  !x. ~retpc_var alias_diamond_fn x
Proof
  simp[retpc_var_def] >> irule copy_phi_var_no_seed >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem alias_diamond_no_return:
  !inst. MEM inst (fn_insts alias_diamond_fn) ==>
    ~MEM inst.inst_opcode [RET; RETFMP; DRET]
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem alias_diamond_shapes:
  retpc_shape_ok alias_diamond_fn /\ opaque_use_ok alias_diamond_fn
Proof
  simp[retpc_shape_ok_def, opaque_use_ok_def, alias_diamond_no_retpc] >>
  conj_tac
  >- (rpt strip_tac >> drule reachable_fn_insts_nonphi >> simp[] >>
      strip_tac >> drule alias_diamond_no_return >> simp[]) >>
  metis_tac[reachable_retpc_var, alias_diamond_no_retpc]
QED

Definition alias_diamond_plan_def:
  alias_diamond_plan n ps =
    generate_block_plan (liveness_analyze alias_diamond_fn)
      (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn)
      alias_diamond_fn (EL n alias_diamond_fn.fn_blocks) ps
End

Definition alias_diamond_e_def:
  alias_diamond_e = THE (alias_diamond_plan 0 (init_cleanup_plan_state NONE [] 0 0))
End

Theorem alias_diamond_e_fields:
  IS_SOME (alias_diamond_plan 0 (init_cleanup_plan_state NONE [] 0 0)) /\
  (SND alias_diamond_e).ps_stack = [Var "seed"] /\
  (SND alias_diamond_e).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Definition alias_diamond_h_def:
  alias_diamond_h = THE (alias_diamond_plan 1 (SND alias_diamond_e))
End

Theorem alias_diamond_h_fields:
  IS_SOME (alias_diamond_plan 1 (SND alias_diamond_e)) /\
  (SND alias_diamond_h).ps_stack = [Var "r"; Var "c"] /\
  (SND alias_diamond_h).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Theorem alias_diamond_h_state:
  SND alias_diamond_h =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "r"; Var "c"])
Proof
  EVAL_TAC
QED

Definition alias_diamond_l_def:
  alias_diamond_l = THE (alias_diamond_plan 2 (SND alias_diamond_h))
End

Definition alias_diamond_r_def:
  alias_diamond_r = THE (alias_diamond_plan 3 (SND alias_diamond_h))
End

Theorem alias_diamond_branches:
  IS_SOME (alias_diamond_plan 2 (SND alias_diamond_h)) /\
  IS_SOME (alias_diamond_plan 3 (SND alias_diamond_h)) /\
  (SND alias_diamond_l).ps_stack = [Var "u2"; Var "u"] /\
  (SND alias_diamond_r).ps_stack = [Var "v2"; Var "v"] /\
  (SND alias_diamond_l).ps_spilled = FEMPTY /\
  (SND alias_diamond_r).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_l_def, alias_diamond_r_def, alias_diamond_h_state] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem alias_diamond_branch_states:
  SND alias_diamond_l =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "u2"; Var "u"]) /\
  SND alias_diamond_r =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "v2"; Var "v"])
Proof
  rewrite_tac[alias_diamond_l_def, alias_diamond_r_def, alias_diamond_h_state] >>
  conj_tac >> EVAL_TAC
QED

Definition alias_diamond_jl_def:
  alias_diamond_jl = THE (alias_diamond_plan 4 (SND alias_diamond_l))
End

Definition alias_diamond_jr_def:
  alias_diamond_jr = THE (alias_diamond_plan 4 (SND alias_diamond_r))
End

Theorem alias_diamond_joins:
  IS_SOME (alias_diamond_plan 4 (SND alias_diamond_l)) /\
  IS_SOME (alias_diamond_plan 4 (SND alias_diamond_r)) /\
  FST alias_diamond_jl = FST alias_diamond_jr /\
  (SND alias_diamond_jl).ps_stack = [Var "z"] /\
  (SND alias_diamond_jr).ps_stack = [Var "z"] /\
  (SND alias_diamond_jl).ps_spilled = FEMPTY /\
  (SND alias_diamond_jr).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_jl_def, alias_diamond_jr_def, alias_diamond_branch_states] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem alias_diamond_join_state:
  SND alias_diamond_jl =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"]) /\
  SND alias_diamond_jr =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"])
Proof
  rewrite_tac[alias_diamond_jl_def, alias_diamond_jr_def, alias_diamond_branch_states] >>
  conj_tac >> EVAL_TAC
QED

Definition alias_diamond_back_def:
  alias_diamond_back = THE (alias_diamond_plan 6 (SND alias_diamond_jl))
End

Theorem alias_diamond_back_fields:
  IS_SOME (alias_diamond_plan 6 (SND alias_diamond_jl)) /\
  (SND alias_diamond_back).ps_stack = [Var "z"] /\
  (SND alias_diamond_back).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_back_def, alias_diamond_join_state] >> EVAL_TAC
QED

Theorem alias_diamond_edges:
  cfg_succs_of (cfg_analyze alias_diamond_fn) "entry" = ["header"] /\
  cfg_succs_of (cfg_analyze alias_diamond_fn) "header" = ["right"; "left"] /\
  cfg_succs_of (cfg_analyze alias_diamond_fn) "right" = ["join"] /\
  cfg_succs_of (cfg_analyze alias_diamond_fn) "join" = ["exit"; "backedge"] /\
  cfg_succs_of (cfg_analyze alias_diamond_fn) "backedge" = ["header"]
Proof
  EVAL_TAC
QED

Theorem alias_diamond_plans:
  alias_diamond_plan 0 (init_cleanup_plan_state NONE [] 0 0) = SOME alias_diamond_e /\
  alias_diamond_plan 1 (SND alias_diamond_e) = SOME alias_diamond_h /\
  alias_diamond_plan 3 (SND alias_diamond_h) = SOME alias_diamond_r /\
  alias_diamond_plan 4 (SND alias_diamond_r) = SOME alias_diamond_jr
Proof
  rpt conj_tac
  >- (mp_tac alias_diamond_e_fields >>
      Cases_on `alias_diamond_plan 0 (init_cleanup_plan_state NONE [] 0 0)` >>
      simp[alias_diamond_e_def])
  >- (mp_tac alias_diamond_h_fields >>
      Cases_on `alias_diamond_plan 1 (SND alias_diamond_e)` >>
      simp[alias_diamond_h_def])
  >- (mp_tac alias_diamond_branches >>
      Cases_on `alias_diamond_plan 3 (SND alias_diamond_h)` >>
      simp[alias_diamond_r_def]) >>
  mp_tac alias_diamond_joins >>
  Cases_on `alias_diamond_plan 4 (SND alias_diamond_r)` >>
  simp[alias_diamond_jr_def]
QED

Theorem alias_diamond_dfs_h:
  dfs_aux_call (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) ["header"] ["entry"] (SND alias_diamond_e)
Proof
  `SND alias_diamond_e = (SND alias_diamond_e) with
    <|ps_stack := (SND alias_diamond_e).ps_stack;
      ps_spilled := (SND alias_diamond_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  rewrite_tac[GSYM (cj 1 alias_diamond_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 0 alias_diamond_fn.fn_blocks`, `FST alias_diamond_e`,
    `init_cleanup_plan_state NONE [] 0 0`, `[]`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans] >>
  conj_tac >- EVAL_TAC >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem alias_diamond_dfs_r:
  dfs_aux_call (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) ["right"] ["header"; "entry"] (SND alias_diamond_h)
Proof
  `SND alias_diamond_h = (SND alias_diamond_h) with
    <|ps_stack := (SND alias_diamond_h).ps_stack;
      ps_spilled := (SND alias_diamond_h).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `["left"]` >>
  rewrite_tac[GSYM (cj 2 alias_diamond_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 1 alias_diamond_fn.fn_blocks`, `FST alias_diamond_h`,
    `SND alias_diamond_e`, `[]`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_h] >> EVAL_TAC
QED

Theorem alias_diamond_dfs_j:
  dfs_aux_call (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) ["join"] ["right"; "header"; "entry"] (SND alias_diamond_r)
Proof
  `SND alias_diamond_r = (SND alias_diamond_r) with
    <|ps_stack := (SND alias_diamond_r).ps_stack;
      ps_spilled := (SND alias_diamond_r).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  rewrite_tac[GSYM (cj 3 alias_diamond_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 3 alias_diamond_fn.fn_blocks`, `FST alias_diamond_r`,
    `SND alias_diamond_h`, `[]`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_r] >> EVAL_TAC
QED

Theorem alias_diamond_exit_dfs_result:
  generate_fn_plan_aux (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    ["exit"] ["join"; "right"; "header"; "entry"] (SND alias_diamond_jr) =
    SOME ([SOLabel "exit"; SOPop 1; SOEmit "STOP"],
      ["exit"; "join"; "right"; "header"; "entry"], init_cleanup_plan_state NONE [] 0 0)
Proof
  rewrite_tac[alias_diamond_jr_def, alias_diamond_branch_states] >> EVAL_TAC
QED

Theorem alias_diamond_dfs_back:
  dfs_aux_call (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) ["backedge"]
    ["exit"; "join"; "right"; "header"; "entry"] (SND alias_diamond_jr)
Proof
  `SND alias_diamond_jr = (SND alias_diamond_jr) with
    <|ps_stack := (SND alias_diamond_jr).ps_stack;
      ps_spilled := (SND alias_diamond_jr).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  `SND alias_diamond_jr = (SND alias_diamond_jr) with
    <|ps_alloc := (init_cleanup_plan_state NONE [] 0 0).ps_alloc with
        sa_free_slots := (SND alias_diamond_jr).ps_alloc.sa_free_slots;
      ps_label_counter := (init_cleanup_plan_state NONE [] 0 0).ps_label_counter|>` by
    (rewrite_tac[alias_diamond_jr_def, alias_diamond_branch_states] >> EVAL_TAC) >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_sibling >>
  qexistsl_tac [`[SOLabel "exit"; SOPop 1; SOEmit "STOP"]`,
    `"exit"`, `["join"; "right"; "header"; "entry"]`] >>
  simp[alias_diamond_exit_dfs_result] >>
  rewrite_tac[GSYM (cj 4 alias_diamond_edges)] >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 4 alias_diamond_fn.fn_blocks`, `FST alias_diamond_jr`,
    `SND alias_diamond_r`, `[]`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_j] >> EVAL_TAC
QED

Theorem alias_diamond_dfs_states:
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "entry" (init_cleanup_plan_state NONE [] 0 0) /\
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_diamond_e) /\
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "right" (SND alias_diamond_h) /\
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "join" (SND alias_diamond_r) /\
  dfs_block_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" (SND alias_diamond_jr)
Proof
  rewrite_tac[dfs_block_state_def] >> rpt conj_tac
  >- (qexistsl_tac [`[]`, `[]`] >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC)
  >- (qexistsl_tac [`[]`, `["entry"]`] >> simp[alias_diamond_dfs_h])
  >- (qexistsl_tac [`[]`, `["header"; "entry"]`] >> simp[alias_diamond_dfs_r])
  >- (qexistsl_tac [`[]`, `["right"; "header"; "entry"]`] >> simp[alias_diamond_dfs_j]) >>
  qexistsl_tac [`[]`, `["exit"; "join"; "right"; "header"; "entry"]`] >>
  simp[alias_diamond_dfs_back]
QED

Theorem alias_diamond_lineage_header:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" (SND alias_diamond_e)
Proof
  `SND alias_diamond_e = (SND alias_diamond_e) with
    <|ps_stack := (SND alias_diamond_e).ps_stack;
      ps_spilled := (SND alias_diamond_e).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 0 alias_diamond_fn.fn_blocks`, `FST alias_diamond_e`, `NONE`, `"entry"`, `F`,
    `init_cleanup_plan_state NONE [] 0 0`, `init_cleanup_plan_state NONE [] 0 0`,
    `SND alias_diamond_e`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_states,
       alias_diamond_edges] >> conj_tac >- EVAL_TAC >>
  reverse conj_tac >- (irule lineage_state_entry >> EVAL_TAC) >>
  `init_cleanup_plan_state NONE [] 0 0 with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    init_cleanup_plan_state NONE [] 0 0` by simp[init_cleanup_plan_state_def] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans]
QED

Theorem alias_diamond_lineage_right:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "right" (SND alias_diamond_h)
Proof
  `SND alias_diamond_h = (SND alias_diamond_h) with
    <|ps_stack := (SND alias_diamond_h).ps_stack;
      ps_spilled := (SND alias_diamond_h).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 1 alias_diamond_fn.fn_blocks`, `FST alias_diamond_h`, `NONE`, `"header"`, `F`,
    `SND alias_diamond_e`, `SND alias_diamond_e`, `SND alias_diamond_h`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_states,
       alias_diamond_edges, alias_diamond_lineage_header] >> EVAL_TAC
QED

Theorem alias_diamond_lineage_join:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "join" (SND alias_diamond_r)
Proof
  `SND alias_diamond_r = (SND alias_diamond_r) with
    <|ps_stack := (SND alias_diamond_r).ps_stack;
      ps_spilled := (SND alias_diamond_r).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 3 alias_diamond_fn.fn_blocks`, `FST alias_diamond_r`, `NONE`, `"right"`, `F`,
    `SND alias_diamond_h`, `SND alias_diamond_h`, `SND alias_diamond_r`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_states,
       alias_diamond_edges, alias_diamond_lineage_right] >>
  rewrite_tac[alias_diamond_h_state, alias_diamond_r_def] >>
  rewrite_tac[alias_diamond_h_state] >> EVAL_TAC
QED

Theorem alias_diamond_lineage_backedge:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "backedge" (SND alias_diamond_jr)
Proof
  `SND alias_diamond_jr = (SND alias_diamond_jr) with
    <|ps_stack := (SND alias_diamond_jr).ps_stack;
      ps_spilled := (SND alias_diamond_jr).ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 4 alias_diamond_fn.fn_blocks`, `FST alias_diamond_jr`, `NONE`, `"join"`, `F`,
    `SND alias_diamond_r`, `SND alias_diamond_r`, `SND alias_diamond_jr`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_plans, alias_diamond_dfs_states,
       alias_diamond_edges, alias_diamond_lineage_join] >>
  rewrite_tac[alias_diamond_branch_states, alias_diamond_jr_def] >>
  rewrite_tac[alias_diamond_branch_states] >> EVAL_TAC
QED

Theorem alias_diamond_back_plan:
  alias_diamond_plan 6 (SND alias_diamond_jr) =
    SOME (FST alias_diamond_back, SND alias_diamond_jr)
Proof
  rewrite_tac[alias_diamond_back_def, alias_diamond_join_state] >> EVAL_TAC
QED

Definition alias_diamond_loop_entry_def:
  alias_diamond_loop_entry = SND alias_diamond_e with
    <|ps_stack := (SND alias_diamond_jr).ps_stack;
      ps_spilled := (SND alias_diamond_jr).ps_spilled|>
End

Theorem alias_diamond_lineage_loop:
  lineage_state (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn) alias_diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "header" alias_diamond_loop_entry
Proof
  rewrite_tac[alias_diamond_loop_entry_def] >> irule lineage_state_step >>
  simp[alias_diamond_dfs_states] >>
  qexistsl_tac [`EL 6 alias_diamond_fn.fn_blocks`, `FST alias_diamond_back`, `NONE`, `"backedge"`, `F`,
    `SND alias_diamond_jr`, `SND alias_diamond_jr`, `SND alias_diamond_jr`] >>
  simp[GSYM alias_diamond_plan_def, alias_diamond_back_plan, alias_diamond_dfs_states,
       alias_diamond_edges, alias_diamond_lineage_backedge] >>
  rewrite_tac[alias_diamond_join_state, alias_diamond_back_def] >>
  rewrite_tac[alias_diamond_join_state] >> EVAL_TAC
QED

Theorem alias_diamond_loop_fields:
  alias_diamond_loop_entry =
    (init_cleanup_plan_state NONE [] 0 0 with ps_stack := [Var "z"]) /\
  normalize_operand (dfg_build_function alias_diamond_fn) [] (Var "u") = Var "r" /\
  normalize_operand (dfg_build_function alias_diamond_fn) [] (Var "v") = Var "r" /\
  ~plan_holds alias_diamond_loop_entry (Var "u") /\
  ~plan_holds alias_diamond_loop_entry (Var "v")
Proof
  rewrite_tac[alias_diamond_loop_entry_def, alias_diamond_join_state] >>
  rpt conj_tac >> EVAL_TAC
QED

Definition alias_diamond_header_phi_def:
  alias_diamond_header_phi =
    generate_phi_plan (EL 0 (EL 1 alias_diamond_fn.fn_blocks).bb_instructions)
      (live_vars_at (liveness_analyze alias_diamond_fn) "header" 1) F
      alias_diamond_loop_entry
End

Theorem alias_diamond_header_phi_fields:
  (SND alias_diamond_header_phi).ps_stack = [Var "t"] /\
  (SND alias_diamond_header_phi).ps_spilled = FEMPTY
Proof
  rewrite_tac[alias_diamond_header_phi_def, alias_diamond_loop_fields] >> EVAL_TAC
QED

Theorem alias_diamond_header_root_prefix:
  IS_SOME (generate_block_insts_plan (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn)
    alias_diamond_fn "header" F 0 2 0
    (TAKE 2 (EL 1 alias_diamond_fn.fn_blocks).bb_instructions) alias_diamond_loop_entry) /\
  (SND (THE (generate_block_insts_plan (liveness_analyze alias_diamond_fn)
    (dfg_build_function alias_diamond_fn) (cfg_analyze alias_diamond_fn)
    alias_diamond_fn "header" F 0 2 0
    (TAKE 2 (EL 1 alias_diamond_fn.fn_blocks).bb_instructions) alias_diamond_loop_entry))).ps_stack =
    [Var "r"; Var "t"]
Proof
  rewrite_tac[alias_diamond_loop_fields] >> conj_tac >> EVAL_TAC
QED

Theorem alias_diamond_header_replay:
  alias_diamond_plan 1 alias_diamond_loop_entry = SOME alias_diamond_h
Proof
  rewrite_tac[alias_diamond_loop_fields] >> EVAL_TAC
QED

(* C2.1 finite mechanism domain: retain a header-root alias on the
   alternate (exit) edge; independently try copying a consumed PHI source. *)
Definition alias_search_fn_def:
  alias_search_fn retain absent two = alias_diamond_fn with fn_blocks :=
    MAP (\bb.
      if bb.bb_label = "header" /\ retain then
        bb with bb_instructions :=
          TAKE 2 bb.bb_instructions ++
          [mk_inst 20 ASSIGN [Var "r"] ["keep1"]] ++
          (if two then [mk_inst 21 ASSIGN [Var "keep1"] ["keep2"]] else []) ++
          DROP 2 bb.bb_instructions
      else if bb.bb_label = "exit" /\ retain then
        bb with bb_instructions :=
          mk_inst 22 ISZERO [Var (if two then "keep2" else "keep1")] ["sink"] ::
          bb.bb_instructions
      else if bb.bb_label = "join" /\ absent then
        bb with bb_instructions :=
          TAKE 2 bb.bb_instructions ++
          [mk_inst 23 ASSIGN [Var "u"] ["miss1"]] ++
          (if two then [mk_inst 24 ASSIGN [Var "miss1"] ["miss2"]] else []) ++
          DROP 2 bb.bb_instructions
      else bb) alias_diamond_fn.fn_blocks
End

Theorem alias_search_readiness:
  codegen_ready_fn (alias_search_fn F F F) /\
  codegen_ready_fn (alias_search_fn T F F) /\
  codegen_ready_fn (alias_search_fn T F T)
Proof
  rpt conj_tac >> CONV_TAC (RAND_CONV EVAL) >> EVAL_TAC
QED

Theorem alias_search_rejected:
  ~codegen_ready_fn (alias_search_fn F T F) /\
  ~codegen_ready_fn (alias_search_fn F T T) /\
  ~codegen_ready_fn (alias_search_fn T T F) /\
  ~codegen_ready_fn (alias_search_fn T T T)
Proof
  rpt conj_tac >> CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >> EVAL_TAC
QED

Theorem eval_one_phi_without_predecessor:
  s.vs_prev_bb = NONE ==> eval_one_phi s inst = NONE
Proof
  simp[eval_one_phi_def] >> Cases_on `inst.inst_outputs` >> simp[]
QED

(* Used at each jump of the block induction, for the successor's alias
   premise.  The invariant reads only ps_stack and ps_spilled, so the
   lineage entry state of the successor (its DFS state with ps_after's
   stack and spill map, lineage_entry) inherits it from ps_after.  The
   block's code is the one lineage_state_block_plan regenerates from the
   lineage state ps, with the cleanup fields it chooses.

   The ownership premise is the planner's static entry invariant: every
   variable live into the block along the edge taken is on the stack or
   spilled.  Without it a block could copy (ASSIGN) a variable the planner
   doesn't hold, whose value need not be its root's after a loop
   iteration, and push the copy.

   Why it should hold: a variable defined in the block by ASSIGN of an
   owned operand takes that operand's value, which is its root's; any
   other definition is its own root.  A root's value only changes when
   its definition runs again, and by SSA and def_dominates_uses a
   variable derived from it is then no longer live, so the planner has
   dropped it: popped, overwritten by a PHI poke, or left behind at the
   join reorder of a JMP (every loop header is a join).  An INVOKE
   changes only its own outputs among the caller's variables.  Return-PC
   variables all read ra in the frame view, and so do their roots. *)

(* Notes from a statement check (intuition, not a prescribed proof):
   - Where the planner drops names (stackPlanGen): an operand dead after
     its instruction is consumed rather than duplicated; dead outputs are
     popped at the end of generate_regular_inst_plan when the block does
     not halt (PHI outputs likewise); after a JNZ clean_stack_plan pops
     dead names or marks them dead_stack_marker; release_dead_spills
     drops dead spills after each regular instruction.  reorder_one's
     alias step only swaps the names of two slots.  So a name in ps_after
     is a name of ps (stack or spill map) or an output of bb.
   - A name z live out of bb, not defined in bb, whose root is defined in
     bb, is impossible: bb dominates z's definition (def_dominates_uses,
     transitively along the ASSIGN chain), and an entry path that meets
     bb only at its end, followed by liveness_sound's witness path, misses
     z's definition.  A bb entered around a loop is a join (entry block
     has no predecessors), entered only by JMP (block_entries_ready),
     whose reorder leaves only names live into it.
   - The ps premises tie ps to vs only through ownership and the alias
     premise; ps's names beyond those are bounded by a static invariant
     of lineage states (their names are live out of the lineage
     predecessor, and the vars live along that edge are all held), which
     also covers a run with vs_prev_bb = NONE at a non-entry block.  The
     entry block has no live-in variables.
   - dead_stack_marker is Label "", and Lit/Label operands are fixed by
     normalize_operand, so only Var operands matter.  PHI and INVOKE
     outputs are their own roots.  For return-PC variables, copy_phi_var
     and retpc_shape_ok keep every link of the chain a return-PC
     variable, so both sides read ra. *)
Theorem lineage_alias_successor:
  !fuel ctx lo liveness dfg cfg ch growth spill_base lbl_ctr fn lbl bb ps h
   promised block_ops ps_after ra vs vs'.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    retpc_shape_ok fn /\ opaque_use_ok fn /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    vs.vs_current_bb = lbl /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan liveness dfg cfg fn bb
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    (!pred x. vs.vs_prev_bb = SOME pred /\
       MEM x (input_vars_from pred bb.bb_instructions
                (live_vars_at liveness lbl 0)) ==>
       MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    run_block fuel ctx bb vs = OK vs' /\ ~vs'.vs_halted
    ==>
    !at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs') lo at =
      operand_val (frame_view fn ra vs') lo (normalize_operand dfg [] at)
Proof
  cheat
QED
