(* Event-aware boundaries for the existing supply simulation. *)
Theory singleUseExpansionSupplyEvents
Ancestors
  singleUseExpansionSupplySim gasEvents o1PassLift
  venomExecSemantics stateEquiv stateFrame analysisSimDefs venomInst venomState

Theorem sue_eval_operands_related:
  !xs ys. LIST_REL (\op newop. eval_operand newop t = eval_operand op s) xs ys ==>
    eval_operands ys t = eval_operands xs s
Proof
  Induct >> Cases_on `ys` >>
  simp[venomStateTheory.eval_operands_def] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Theorem sue_supply_lookup_functions:
  LIST_REL (\f g. ?t t'.
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) fs gs ==>
  OPTREL (\f g. ?t t'.
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t'))
    (lookup_function name fs) (lookup_function name gs)
Proof
  strip_tac >> irule list_rel_lookup_function >> simp[] >>
  rpt strip_tac >> drule sue_expand_function_supply_identity >> simp[]
QED

Theorem sue_supply_setup_callee:
  sue_state_rel P s u /\
  sue_expand_function_supply t f = (g,t') ==>
  setup_callee g args u = setup_callee f args s
Proof
  strip_tac >> irule setup_callee_execution_frame >>
  drule sue_expand_function_supply_identity >>
  gvs[sue_state_rel_def]
QED

Theorem sue_state_rel_merge_callee:
  sue_state_rel P s u /\ execution_frame c = execution_frame d ==>
  sue_state_rel P (merge_callee_state s c) (merge_callee_state u d)
Proof
  simp[sue_state_rel_def, merge_callee_state_def, execution_frame_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem sue_rewritten_invoke_args:
  inst_wf inst /\ inst.inst_opcode = INVOKE /\
  LIST_REL (\op newop. eval_operand newop u = eval_operand op s)
    inst.inst_operands ops /\
  (!i. i < LENGTH inst.inst_operands ==>
    !lbl. EL i inst.inst_operands = Label lbl ==> EL i ops = Label lbl) ==>
  OPTION_MAP (\(name,args). (name, eval_operands args u))
    (decode_invoke (inst with inst_operands := ops)) =
  OPTION_MAP (\(name,args). (name, eval_operands args s))
    (decode_invoke inst)
Proof
  strip_tac >> gvs[venomWfTheory.inst_wf_def] >>
  `newop = Label lbl` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[decode_invoke_def] >> irule sue_eval_operands_related >> simp[]
QED

Theorem sue_result_rel_frame:
  sue_result_rel P r r' ==>
  lift_result (sue_state_rel P)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t) r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[sue_result_rel_def, lift_result_def, sue_term_rel_def]
QED

Theorem sue_state_rel_bind_outputs:
  !outs vals s u. sue_state_rel P s u ==>
  OPTREL (sue_state_rel P) (bind_outputs outs vals s) (bind_outputs outs vals u)
Proof
  Induct_on `outs` >> Cases_on `vals` >>
  simp[bind_outputs_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`t`, `update_var h' h s`, `update_var h' h u`] mp_tac) >>
  simp[bind_outputs_def] >> impl_tac >-
   (gvs[sue_state_rel_def, venomStateTheory.update_var_def,
        execution_frame_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[]
QED

(* Result consumption uses the caller relation only on continuing states. *)
Theorem sue_invoke_result_frame:
  sue_state_rel P s u /\
  lift_result (sue_state_rel Q)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t) r r' ==>
  lift_result (sue_state_rel P)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t)
    (invoke_result outs s r) (invoke_result outs u r')
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[lift_result_def, invoke_result_def] >>
  rpt strip_tac >> gvs[] >>
  `sue_state_rel P (adopt_return_fmp i (merge_callee_state s v))
                   (adopt_return_fmp i (merge_callee_state u v'))` by
    (Cases_on `i.iret_adopt_fmp` >>
     gvs[sue_state_rel_def, merge_callee_state_def, adopt_return_fmp_def,
         execution_frame_def]) >>
  drule sue_state_rel_bind_outputs >>
  disch_then (qspecl_then [`outs`, `i.iret_values`] mp_tac) >>
  Cases_on `bind_outputs outs i.iret_values (adopt_return_fmp i (merge_callee_state s v))` >>
  Cases_on `bind_outputs outs i.iret_values (adopt_return_fmp i (merge_callee_state u v'))` >>
  simp[lift_result_def]
QED

Theorem sue_assign_events_step:
  a.inst_opcode = ASSIGN ==> gas_events_step fuel ctx owner a t = []
Proof
  simp[gas_events_step_def]
QED

Theorem sue_gas_events_step_noninvoke:
  inst.inst_opcode <> INVOKE ==>
  gas_events_step fuel C owner inst s =
  gas_events_step fuel C' owner (inst with inst_operands := ops) u
Proof
  simp[gas_events_step_def]
QED

Theorem sue_assign_events_prefix:
  !assigns k bb tail t u.
  EVERY (\a. a.inst_opcode = ASSIGN) assigns /\
  DROP k bb.bb_instructions = assigns ++ tail /\
  run_insts fuel ctx assigns t = OK u ==>
  gas_events_block fuel ctx owner bb (t with vs_inst_idx := k) =
  gas_events_block fuel ctx owner bb (u with vs_inst_idx := k + LENGTH assigns)
Proof
  Induct >> rpt gen_tac
  >- simp[run_insts_def] >>
  strip_tac >> fs[] >>
  `k < LENGTH bb.bb_instructions` by
    (Cases_on `LENGTH bb.bb_instructions <= k` >>
     fs[listTheory.DROP_LENGTH_TOO_LONG]) >>
  `EL k bb.bb_instructions = h /\
   DROP (SUC k) bb.bb_instructions = assigns ++ tail` by
    gvs[rich_listTheory.DROP_BY_DROP_SUC] >>
  Cases_on `step_inst fuel ctx h t` >> gvs[run_insts_def] >>
  simp[Once gas_events_block_def, get_instruction_def, sue_assign_events_step,
       analysisSimProofsBaseTheory.step_inst_idx_indep,
       is_terminator_def, instIdxIndepTheory.exec_result_map_def] >>
  first_x_assum (qspec_then `SUC k` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem sue_gas_events_invoke:
  sue_state_rel P s u /\
  LIST_REL (\f g. ?t t'.
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) C.ctx_functions C'.ctx_functions /\
  inst.inst_opcode = INVOKE /\
  OPTION_MAP (\(name,args). (name, eval_operands args u))
    (decode_invoke (inst with inst_operands := ops)) =
  OPTION_MAP (\(name,args). (name, eval_operands args s)) (decode_invoke inst) /\
  (!name f g t t' cs.
    lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t') /\ fn_entry_state f cs ==>
    gas_events_blocks fuel C f cs = gas_events_blocks fuel C' g cs) ==>
  gas_events_step fuel C owner inst s =
  gas_events_step fuel C' owner (inst with inst_operands := ops) u
Proof
  strip_tac >> simp[gas_events_step_def] >>
  Cases_on `decode_invoke inst` >>
  Cases_on `decode_invoke (inst with inst_operands := ops)` >>
  gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule sue_supply_lookup_functions >>
  disch_then (qspec_then `name` mp_tac) >>
  Cases_on `lookup_function name C.ctx_functions` >>
  Cases_on `lookup_function name C'.ctx_functions` >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `eval_operands args' s` >> simp[] >>
  rename1 `eval_operands args' s = SOME values` >>
  `setup_callee x' values u = setup_callee x values s` by
    (irule sue_supply_setup_callee >> metis_tac[]) >>
  simp[] >> Cases_on `setup_callee x values s` >> simp[] >>
  drule setup_callee_fn_entry_state >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem sue_step_invoke_frame:
  sue_state_rel P s u /\
  LIST_REL (\f g. ?t t'.
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) C.ctx_functions C'.ctx_functions /\
  inst.inst_opcode = INVOKE /\
  OPTION_MAP (\(name,args). (name, eval_operands args u))
    (decode_invoke (inst with inst_operands := ops)) =
  OPTION_MAP (\(name,args). (name, eval_operands args s)) (decode_invoke inst) /\
  (!name f g t t' cs.
    lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t') /\ fn_entry_state f cs ==>
    lift_result (sue_state_rel (set (fn_ir_vars f)))
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (run_blocks fuel C f cs) (run_blocks fuel C' g cs)) ==>
  lift_result (sue_state_rel P)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t)
    (step_inst fuel C inst s)
    (step_inst fuel C' (inst with inst_operands := ops) u)
Proof
  strip_tac >> simp[step_inst_def] >>
  Cases_on `decode_invoke inst` >>
  Cases_on `decode_invoke (inst with inst_operands := ops)` >>
  gvs[lift_result_def] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule sue_supply_lookup_functions >>
  disch_then (qspec_then `name` mp_tac) >>
  Cases_on `lookup_function name C.ctx_functions` >>
  Cases_on `lookup_function name C'.ctx_functions` >> simp[lift_result_def] >>
  strip_tac >> gvs[] >>
  Cases_on `eval_operands args' s` >> simp[lift_result_def] >>
  rename1 `eval_operands args' s = SOME values` >>
  `setup_callee x' values u = setup_callee x values s` by
    (irule sue_supply_setup_callee >> metis_tac[]) >>
  simp[] >> Cases_on `setup_callee x values s` >> simp[lift_result_def] >>
  drule setup_callee_fn_entry_state >> strip_tac >>
  irule (SRULE [invoke_result_def, execution_frame_def] sue_invoke_result_frame) >>
  metis_tac[]
QED

Theorem sue_rewritten_step_events:
  sue_state_rel P s u /\
  (!x. MEM (Var x) inst.inst_operands ==> x IN P) /\
  inst_wf inst /\ ~is_alloca_op inst.inst_opcode /\
  inst.inst_opcode <> PARAM /\ inst.inst_opcode <> FMP_PARAM /\
  inst.inst_opcode <> RETPC_PARAM /\ inst.inst_opcode <> PHI /\
  LENGTH ops = LENGTH inst.inst_operands /\
  (inst.inst_opcode = DRET ==>
    parse_dret_shape (inst with inst_operands := ops) = parse_dret_shape inst) /\
  (!i. i < LENGTH inst.inst_operands ==>
    eval_operand (EL i ops) u = eval_operand (EL i inst.inst_operands) u) /\
  (!i. i < LENGTH inst.inst_operands ==>
    !lbl. EL i inst.inst_operands = Label lbl ==> EL i ops = Label lbl) /\
  (inst.inst_opcode = LOG ==> HD ops = HD inst.inst_operands) /\
  LIST_REL (\f g. ?t t'.
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) C.ctx_functions C'.ctx_functions /\
  (!name f g t t' cs.
    lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t') /\ fn_entry_state f cs ==>
    gas_events_blocks fuel C f cs = gas_events_blocks fuel C' g cs /\
    lift_result (sue_state_rel (set (fn_ir_vars f)))
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (run_blocks fuel C f cs) (run_blocks fuel C' g cs)) ==>
  gas_events_step fuel C owner inst s =
    gas_events_step fuel C' owner (inst with inst_operands := ops) u /\
  lift_result (sue_state_rel P)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t)
    (step_inst fuel C inst s)
    (step_inst fuel C' (inst with inst_operands := ops) u)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (`LIST_REL (\op newop. eval_operand newop u = eval_operand op s)
        inst.inst_operands ops` by
        (simp[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
         first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
         `eval_operand (EL n inst.inst_operands) u =
          eval_operand (EL n inst.inst_operands) s` by
           (irule sue_state_rel_eval_operand >> qexists_tac `P` >> simp[] >>
            metis_tac[listTheory.MEM_EL]) >> simp[]) >>
      drule_all sue_rewritten_invoke_args >> strip_tac >>
      conj_tac
      >- (irule sue_gas_events_invoke >> metis_tac[]) >>
      irule sue_step_invoke_frame >> metis_tac[]) >>
  conj_tac >- simp[gas_events_step_def] >>
  `sue_result_rel P (step_inst fuel C inst s)
     (step_inst fuel C (inst with inst_operands := ops) u)` by
    (irule sue_step_inst_rewritten >> simp[]) >>
  drule sue_result_rel_frame >>
  simp[step_inst_non_invoke]
QED

Theorem sue_expand_ops_supply_events:
  ir_supply_inst_ok supply /\
  sue_expand_ops_supply dfg inst supply inst.inst_operands 0 = (assigns,ops,supply') /\
  P SUBSET set supply.irs_used_vars /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN P) /\
  (!a v. MEM a assigns /\ a.inst_operands = [Var v] ==> v IN FDOM s.vs_vars) /\
  sue_state_rel P s t /\ inst_wf inst /\
  ~is_alloca_op inst.inst_opcode /\ ~sue_should_skip inst.inst_opcode /\
  LIST_REL (\f g. ?t t'.
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) C.ctx_functions C'.ctx_functions /\
  (!name f g t t' cs.
    lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t') /\ fn_entry_state f cs ==>
    gas_events_blocks fuel C f cs = gas_events_blocks fuel C' g cs /\
    lift_result (sue_state_rel (set (fn_ir_vars f)))
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (run_blocks fuel C f cs) (run_blocks fuel C' g cs)) ==>
  ?u. run_insts fuel C' assigns t = OK u /\ sue_state_rel P s u /\
      u.vs_inst_idx = t.vs_inst_idx /\
      gas_events_step fuel C owner inst s =
        gas_events_step fuel C' owner (inst with inst_operands := ops) u /\
      lift_result (sue_state_rel P)
        (\s t. execution_frame s = execution_frame t)
        (\s t. execution_frame s = execution_frame t)
        (step_inst fuel C inst s)
        (step_inst fuel C' (inst with inst_operands := ops) u)
Proof
  strip_tac >> drule_all sue_expand_ops_supply_sim >>
  disch_then (qspecl_then [`fuel`, `C'`] strip_assume_tac) >>
  qexists_tac `uu` >> simp[] >>
  drule sue_expand_ops_supply_structure >> strip_tac >>
  `!i. i < LENGTH inst.inst_operands ==>
    eval_operand (EL i ops) uu = eval_operand (EL i inst.inst_operands) uu` by
    (rpt strip_tac >>
     `eval_operand (EL i ops) uu = eval_operand (EL i inst.inst_operands) s` by
       (fs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
     `eval_operand (EL i inst.inst_operands) uu =
      eval_operand (EL i inst.inst_operands) s` by
       (irule sue_state_rel_eval_operand >> qexists_tac `P` >> simp[] >>
        metis_tac[listTheory.MEM_EL]) >> simp[]) >>
  irule (SRULE [execution_frame_def] sue_rewritten_step_events) >>
  gvs[singleUseExpansionDefsTheory.sue_should_skip_def, is_param_opcode_iff] >>
  metis_tac[]
QED

Theorem sue_frame_result_indices[local]:
  lift_result (sue_state_rel P)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t)
    (exec_result_map (\s. s with vs_inst_idx := n) r)
    (exec_result_map (\s. s with vs_inst_idx := m) r') <=>
  lift_result (sue_state_rel P)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t) r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[lift_result_def, instIdxIndepTheory.exec_result_map_def,
       sue_state_rel_idx, execution_frame_def]
QED

Theorem sue_frame_step_indices:
  lift_result (sue_state_rel P)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t)
    (step_inst fuel C inst s) (step_inst fuel C' inst' (t with vs_inst_idx := k)) <=>
  lift_result (sue_state_rel P)
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t)
    (step_inst fuel C inst s) (step_inst fuel C' inst' t)
Proof
  once_rewrite_tac[GSYM (Q.INST [`n` |-> `0`, `m` |-> `0`] sue_frame_result_indices)] >>
  pure_rewrite_tac[sue_step_inst_idx_norm] >> simp[]
QED

Theorem sue_gas_events_step_index:
  gas_events_step fuel C owner inst (s with vs_inst_idx := k) =
  gas_events_step fuel C owner inst s
Proof
  `!f args. setup_callee f args (s with vs_inst_idx := k) = setup_callee f args s` by
    (rpt gen_tac >> irule setup_callee_execution_frame >> simp[execution_frame_def]) >>
  simp[gas_events_step_def, instIdxIndepTheory.eval_ops_inst_idx]
QED

Theorem sue_segment_indexed_events:
  ir_supply_inst_ok supply /\ P SUBSET set supply.irs_used_vars /\
  sue_segments_supply dfg supply bb.bb_instructions = (segs,supply') /\
  i < LENGTH bb.bb_instructions /\ bb' = bb with bb_instructions := FLAT segs /\
  inst = EL i bb.bb_instructions /\ inst_wf inst /\ ~is_alloca_op inst.inst_opcode /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN P) /\
  (~sue_should_skip inst.inst_opcode ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars) /\
  sue_state_rel P s t /\ t.vs_inst_idx = sue_segment_offset segs i /\
  LIST_REL (\f g. ?t t'.
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) C.ctx_functions C'.ctx_functions /\
  (!name f g t t' cs.
    lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t') /\ fn_entry_state f cs ==>
    gas_events_blocks fuel C f cs = gas_events_blocks fuel C' g cs /\
    lift_result (sue_state_rel (set (fn_ir_vars f)))
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (run_blocks fuel C f cs) (run_blocks fuel C' g cs)) ==>
  ?k u inst'.
    exec_block fuel C' bb' t = exec_block fuel C' bb' u /\
    gas_events_block fuel C' owner bb' t = gas_events_block fuel C' owner bb' u /\
    u.vs_inst_idx = k /\ k < LENGTH bb'.bb_instructions /\
    EL k bb'.bb_instructions = inst' /\ inst'.inst_opcode = inst.inst_opcode /\
    SUC k = sue_segment_offset segs (SUC i) /\
    gas_events_step fuel C owner inst s = gas_events_step fuel C' owner inst' u /\
    lift_result (sue_state_rel P)
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (step_inst fuel C inst s) (step_inst fuel C' inst' u)
Proof
  strip_tac >> drule_all sue_segments_supply_index_ready >> strip_tac >>
  `i < LENGTH segs` by metis_tac[sue_segments_supply_length] >>
  drule sue_segment_offset_drop >> strip_tac >>
  drule sue_segment_offset_suc >> strip_tac >>
  Cases_on `sue_should_skip inst.inst_opcode`
  >- suspend "skip" >>
  Cases_on `sue_expand_ops_supply dfg inst si inst.inst_operands 0` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst si inst.inst_operands 0 = (assigns,ops,sj')` >>
  `EL i segs = assigns ++ [inst with inst_operands := ops]` by
    gvs[singleUseExpansionDefsTheory.sue_expand_inst_supply_def] >>
  `!a v. MEM a assigns /\ a.inst_operands = [Var v] ==> v IN FDOM s.vs_vars` by
    (drule sue_expand_ops_supply_copy_sources >>
     simp[listTheory.EVERY_MEM] >> metis_tac[listTheory.CONS_11]) >>
  drule_all sue_expand_ops_supply_events >>
  disch_then (qspec_then `owner` strip_assume_tac) >>
  suspend "expanded"
QED

Resume sue_segment_indexed_events[skip]:
  `EL i segs = [inst]` by
    metis_tac[sue_expand_inst_supply_skip, pairTheory.PAIR_EQ] >>
  `sue_segment_offset segs i < LENGTH (FLAT segs) /\
   EL (sue_segment_offset segs i) (FLAT segs) = inst` by
    (fs[] >> metis_tac[sue_drop_cons_index]) >>
  `inst.inst_opcode <> INVOKE` by
    gvs[singleUseExpansionDefsTheory.sue_should_skip_def, is_param_opcode_iff] >>
  `sue_result_rel P (step_inst fuel C inst s) (step_inst fuel C inst t)` by
    (irule sue_step_inst_preserves >> simp[]) >>
  drule sue_result_rel_frame >> strip_tac >>
  qexistsl [`sue_segment_offset segs i`, `t`, `inst`] >>
  gvs[gas_events_step_def, step_inst_non_invoke]
QED

Resume sue_segment_indexed_events[expanded]:
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    (drule_all sue_expand_ops_supply_prefix >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `DROP (sue_segment_offset segs i) bb'.bb_instructions =
    assigns ++ (inst with inst_operands := ops)::FLAT (DROP (SUC i) segs)` by
    (simp[] >> pure_asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  `t with vs_inst_idx := sue_segment_offset segs i = t` by
    (qpat_x_assum `t.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
  drule_all sue_exec_block_assign_prefix >> strip_tac >>
  drule_all sue_assign_events_prefix >>
  disch_then (qspec_then `owner` assume_tac) >>
  `sue_segment_offset segs i + LENGTH assigns < LENGTH bb'.bb_instructions /\
    EL (sue_segment_offset segs i + LENGTH assigns) bb'.bb_instructions =
      inst with inst_operands := ops` by
    metis_tac[sue_drop_prefix_index] >>
  qexistsl [`sue_segment_offset segs i + LENGTH assigns`,
    `u with vs_inst_idx := sue_segment_offset segs i + LENGTH assigns`,
    `inst with inst_operands := ops`] >>
  simp[sue_gas_events_step_index, sue_frame_step_indices] >>
  gvs[]
QED

Finalise sue_segment_indexed_events

Theorem sue_exec_block_supply_events:
  !i s t.
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_inst_ok supply /\ set (fn_ir_vars fn) SUBSET set supply.irs_used_vars /\
  sue_segments_supply (dfg_build_function fn) supply bb.bb_instructions = (segs,supply') /\
  bb' = bb with bb_instructions := FLAT segs /\
  phi_prefix_length bb.bb_instructions <= i /\ i <= LENGTH bb.bb_instructions /\
  s.vs_inst_idx = i /\ t.vs_inst_idx = sue_segment_offset segs i /\
  sue_boundary_defined fn bb i s /\ sue_state_rel (set (fn_ir_vars fn)) s t /\
  LIST_REL (\f g. ?t t'.
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) C.ctx_functions C'.ctx_functions /\
  (!name f g t t' cs.
    lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t') /\ fn_entry_state f cs ==>
    gas_events_blocks fuel C f cs = gas_events_blocks fuel C' g cs /\
    lift_result (sue_state_rel (set (fn_ir_vars f)))
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (run_blocks fuel C f cs) (run_blocks fuel C' g cs)) ==>
  gas_events_block fuel C owner bb s = gas_events_block fuel C' owner bb' t /\
  lift_result (sue_state_rel (set (fn_ir_vars fn)))
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t)
    (exec_block fuel C bb s) (exec_block fuel C' bb' t)
Proof
  measureInduct_on `LENGTH bb.bb_instructions - i` >> rpt gen_tac >> strip_tac >>
  Cases_on `i = LENGTH bb.bb_instructions`
  >- (`LENGTH segs = LENGTH bb.bb_instructions` by metis_tac[sue_segments_supply_length] >>
      `sue_segment_offset segs i = LENGTH (FLAT segs)` by metis_tac[sue_segment_offset_end] >>
      gvs[] >> simp[Once gas_events_block_def, Once exec_block_def, get_instruction_def] >>
      simp[Once gas_events_block_def, Once exec_block_def, get_instruction_def, lift_result_def]) >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `inst_wf (EL i bb.bb_instructions)` by metis_tac[listTheory.EVERY_EL] >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
       v IN set (fn_ir_vars fn)` by metis_tac[sue_original_operand_covered, listTheory.MEM_EL] >>
  `(EL i bb.bb_instructions).inst_opcode <> PHI` by metis_tac[sue_phi_suffix_nonphi] >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==> v IN FDOM s.vs_vars` by
    metis_tac[sue_boundary_operand_defined] >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (`!bbs. MEM bb bbs ==> MEM (EL i bb.bb_instructions) (fn_insts_blocks bbs)` by
       (Induct >> simp[fn_insts_blocks_def] >> metis_tac[listTheory.MEM_EL]) >>
     simp[fn_insts_def]) >>
  `(EL i bb.bb_instructions).inst_opcode <> ALLOCA` by
    (qpat_x_assum `EVERY (\inst. inst.inst_opcode <> ALLOCA) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> disch_then drule >> simp[]) >>
  `~is_alloca_op (EL i bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `(EL i bb.bb_instructions).inst_opcode <> ALLOCA` mp_tac >>
     Cases_on `(EL i bb.bb_instructions).inst_opcode` >> simp[is_alloca_op_def]) >>
  `?k u inst'.
    exec_block fuel C' bb' t = exec_block fuel C' bb' u /\
    gas_events_block fuel C' owner bb' t = gas_events_block fuel C' owner bb' u /\
    u.vs_inst_idx = k /\ k < LENGTH bb'.bb_instructions /\
    EL k bb'.bb_instructions = inst' /\
    inst'.inst_opcode = (EL i bb.bb_instructions).inst_opcode /\
    SUC k = sue_segment_offset segs (SUC i) /\
    gas_events_step fuel C owner (EL i bb.bb_instructions) s =
      gas_events_step fuel C' owner inst' u /\
    lift_result (sue_state_rel (set (fn_ir_vars fn)))
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (step_inst fuel C (EL i bb.bb_instructions) s) (step_inst fuel C' inst' u)` by
    (irule sue_segment_indexed_events >> simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!name f g t t' cs. _` drule_all >>
         simp[execution_frame_def]) >>
     qexistsl [`bb`, `dfg_build_function fn`, `supply`, `supply'`] >> simp[]) >>
  suspend "segment"
QED

Resume sue_exec_block_supply_events[segment]:
  qpat_x_assum `exec_block fuel C' bb' t = _` SUBST1_TAC >>
  qpat_x_assum `gas_events_block fuel C' owner bb' t = _` SUBST1_TAC >>
  `get_instruction bb s.vs_inst_idx = SOME (EL i bb.bb_instructions)` by
    simp[get_instruction_def] >>
  `get_instruction bb' u.vs_inst_idx = SOME inst'` by gvs[get_instruction_def] >>
  pure_once_rewrite_tac[gas_events_block_def, exec_block_def] >>
  qpat_x_assum `get_instruction bb _ = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `get_instruction bb' _ = _` (fn th => rewrite_tac[th]) >>
  Cases_on `step_inst fuel C (EL i bb.bb_instructions) s` >>
  Cases_on `step_inst fuel C' inst' u` >>
  fs[lift_result_def] >>
  rename1 `sue_state_rel (set (fn_ir_vars fn)) v v'` >>
  Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode`
  >- (`v.vs_halted = v'.vs_halted` by
        (fs[sue_state_rel_def] >>
         qpat_x_assum `execution_frame v = _` mp_tac >>
         simp[execution_frame_def, venom_state_component_equality]) >>
      Cases_on `v'.vs_halted` >> fs[lift_result_def, sue_state_rel_def]) >>
  simp[] >>
  `v.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `sue_boundary_defined fn bb (SUC i) (v with vs_inst_idx := SUC i)` by
    (irule sue_boundary_defined_step >> simp[] >> metis_tac[]) >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`v with vs_inst_idx := SUC i`,
    `v' with vs_inst_idx := sue_segment_offset segs (SUC i)`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Finalise sue_exec_block_supply_events

Theorem sue_run_blocks_supply_events:
  !fuel fn supply fn' supply' st tt.
  EVERY (\f. wf_ssa f /\ fn_inst_wf f /\ wf_function f /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts f)) C.ctx_functions /\
  LIST_REL (\f g. ?t t'. ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) C.ctx_functions C'.ctx_functions /\
  MEM fn C.ctx_functions /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  fn_reachable fn st.vs_current_bb /\ strict_dom_vars_defined fn st /\
  sue_state_rel (set (fn_ir_vars fn)) st tt ==>
  gas_events_blocks fuel C fn st = gas_events_blocks fuel C' fn' tt /\
  lift_result (sue_state_rel (set (fn_ir_vars fn)))
    (\s t. execution_frame s = execution_frame t)
    (\s t. execution_frame s = execution_frame t)
    (run_blocks fuel C fn st) (run_blocks fuel C' fn' tt)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[lift_result_def]) >>
  `wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn)` by
    (qpat_x_assum `EVERY _ C.ctx_functions` mp_tac >>
     simp[listTheory.EVERY_MEM] >> disch_then drule >> simp[]) >>
  `!name f g t t' cs.
    lookup_function name C.ctx_functions = SOME f /\
    ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t') /\ fn_entry_state f cs ==>
    gas_events_blocks fuel C f cs = gas_events_blocks fuel C' g cs /\
    lift_result (sue_state_rel (set (fn_ir_vars f)))
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (run_blocks fuel C f cs) (run_blocks fuel C' g cs)` by
    (rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
     `MEM f C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
     fs[fn_entry_state_def] >>
     `wf_ssa f` by gvs[listTheory.EVERY_MEM] >>
     `strict_dom_vars_defined f cs` by
       metis_tac[sccpCorrectnessProofsTheory.strict_dom_vars_defined_entry] >>
     simp[venomWfTheory.fn_reachable_def] >> metis_tac[]) >>
  `tt.vs_current_bb = st.vs_current_bb` by fs[sue_state_rel_def] >>
  Cases_on `lookup_block st.vs_current_bb fn.fn_blocks`
  >- suspend "missing" >>
  rename1 `lookup_block st.vs_current_bb fn.fn_blocks = SOME bb` >>
  drule_all sue_function_lookup_ready >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = st.vs_current_bb` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
      !v. MEM (Var v) inst.inst_operands ==> v IN set (fn_ir_vars fn)) bb.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> metis_tac[sue_original_operand_covered]) >>
  `sue_result_rel (set (fn_ir_vars fn))
     (eval_phis st bb.bb_instructions) (eval_phis tt (FLAT segs))` by
    (irule sue_expanded_phi_entry >> simp[] >> metis_tac[]) >>
  suspend "phis"
QED

Resume sue_run_blocks_supply_events[missing]:
  `lookup_block st.vs_current_bb fn'.fn_blocks = NONE` by
    (Cases_on `sue_expand_blocks_supply (dfg_build_function fn) supply fn.fn_blocks` >>
     gvs[singleUseExpansionDefsTheory.sue_expand_function_supply_def] >>
     Cases_on `lookup_block st.vs_current_bb q` >> simp[] >>
     drule_all sue_expand_blocks_supply_lookup_back >> simp[]) >>
  pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[lift_result_def]
QED

Resume sue_run_blocks_supply_events[phis]:
  `phi_prefix_length (FLAT segs) = phi_prefix_length bb.bb_instructions` by
    (drule sue_segments_supply_flat >> strip_tac >>
     drule_all sue_expand_insts_supply_phis >> simp[]) >>
  `sue_segment_offset segs (phi_prefix_length bb.bb_instructions) =
    phi_prefix_length bb.bb_instructions` by metis_tac[sue_segments_phi_offset] >>
  `fn'.fn_name = fn.fn_name` by metis_tac[sue_expand_function_supply_identity] >>
  pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >> simp[] >>
  qspecl_then [`st`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  Cases_on `eval_phis tt (FLAT segs)` >>
  gvs[sue_result_rel_def, lift_result_def] >>
  suspend "block"
QED

Resume sue_run_blocks_supply_events[block]:
  rename1 `eval_phis st bb.bb_instructions = OK u` >>
  `sue_boundary_defined fn bb (phi_prefix_length bb.bb_instructions)
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[sue_boundary_defined_phis] >>
  `u.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `gas_events_block fuel C fn.fn_name bb
      (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
    gas_events_block fuel C' fn.fn_name (bb with bb_instructions := FLAT segs)
      (v with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    lift_result (sue_state_rel (set (fn_ir_vars fn)))
      (\s t. execution_frame s = execution_frame t)
      (\s t. execution_frame s = execution_frame t)
      (exec_block fuel C bb (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      (exec_block fuel C' (bb with bb_instructions := FLAT segs)
        (v with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (irule sue_exec_block_supply_events >> simp[venomExecProofsTheory.phi_prefix_length_le] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!name f g t t' cs. _` drule_all >> simp[execution_frame_def]) >>
     metis_tac[]) >>
  Cases_on `exec_block fuel C bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  Cases_on `exec_block fuel C' (bb with bb_instructions := FLAT segs)
    (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[lift_result_def] >> suspend "exit"
QED

Resume sue_run_blocks_supply_events[exit]:
  `v'.vs_halted = v''.vs_halted` by
    (fs[sue_state_rel_def] >>
     qpat_x_assum `execution_frame v' = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  Cases_on `v'.vs_halted`
  >- fs[lift_result_def, sue_state_rel_def] >>
  fs[] >> first_x_assum irule >> simp[] >>
  `fn_reachable fn v'.vs_current_bb /\ strict_dom_vars_defined fn v'`
    suffices_by metis_tac[] >>
  irule sue_exec_block_defined_exit >> simp[] >>
  qexistsl [`bb`, `C`, `fuel`,
    `u with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[venomExecProofsTheory.phi_prefix_length_le]
QED

Finalise sue_run_blocks_supply_events

Theorem sue_function_supply_entry_events:
  EVERY (\f. wf_ssa f /\ fn_inst_wf f /\ wf_function f /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts f)) C.ctx_functions /\
  LIST_REL (\f g. ?t t'. ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t f = (g,t')) C.ctx_functions C'.ctx_functions /\
  MEM fn C.ctx_functions /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  sue_expand_function_supply supply fn = (fn',supply') /\ fn_entry_state fn st ==>
  gas_events_blocks fuel C fn st = gas_events_blocks fuel C' fn' st
Proof
  strip_tac >>
  `wf_ssa fn` by gvs[listTheory.EVERY_MEM] >>
  `strict_dom_vars_defined fn st` by
    metis_tac[sccpCorrectnessProofsTheory.strict_dom_vars_defined_entry, fn_entry_state_def] >>
  `fn_reachable fn st.vs_current_bb` by
    (fs[fn_entry_state_def, venomWfTheory.fn_reachable_def]) >>
  `sue_state_rel (set (fn_ir_vars fn)) st st` by simp[sue_state_rel_def] >>
  drule_all sue_run_blocks_supply_events >> simp[]
QED
