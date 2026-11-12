Theory concretizeLayoutLocalShifts
Ancestors concretizeLayoutLocalValues concretizeLayoutReaderContext
  frameRelocationCleanValueSteps
  frameRelocationLocal frameRelocationGuardedValues frameRelocationTaintOrder
  frameRelocationOpaque frameRelocationGhostCopy frameOriginUpdates
  frameRelocationMemory frameRelocationStoreValues frameRelocationEnvironment frameRelocationReachableSupport
  frameRelocationBinding frameJointDemand frameJointTrace frameJointTransition
  frameResolvedTrace frameJointTaint frameOriginReachable frameOriginHistory
  pointerConfinedDefs memLocDefs
  ptrDiscipline venomExecSemantics venomState finite_map pred_set list

Theorem shift_taint_mono:
  a SUBSET b ==> shift_taint opc k a SUBSET shift_taint opc k b
Proof
  simp[shift_taint_def] >> rpt IF_CASES_TAC >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem shift_operand_nonpointer:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  MEM inst.inst_opcode [SHL; SHR; SAR] /\
  MEM (Var w) inst.inst_operands ==>
  FLOOKUP rv w = NONE /\ ~retpc_var fn w
Proof
  strip_tac >> conj_tac
  >- (spose_not_then assume_tac >>
      `w IN fn_pv P fn` by metis_tac[] >>
      `ptr_use_ok P (fn_pv P fn) inst` by
        (fs[fn_ptr_ok_def] >> metis_tac[]) >>
      fs[ptr_use_ok_def] >>
      qpat_x_assum `!v. MEM (Var v) _ /\ _ ==> _`
        (qspec_then `w` mp_tac) >>
      gvs[MEM] >>
      simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]) >>
  strip_tac >> drule_all disciplined_retpc_operand_use >> gvs[MEM]
QED

Theorem shift_count_clean:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [SHL; SHR; SAR] /\
  inst.inst_operands = [n; a] ==> op_taint tn n = {}
Proof
  strip_tac >> spose_not_then assume_tac >>
  fs[taint_ok_def] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
  fs[MEM] >> metis_tac[]
QED



Theorem masked_pure2_execution[local]:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\
  inst.inst_operands = [n; a] /\ inst.inst_outputs = [v] /\
  (!w. n = Var w ==> clean_scalar Opaque rv tn w) /\
  (!w. a = Var w ==> FLOOKUP rv w = NONE /\ ~Opaque w) /\
  exec_pure2 f inst s = OK post ==>
  ?k x y. eval_operand n s = SOME k /\ eval_operand n t = SOME k /\
    eval_operand a s = SOME x /\ eval_operand a t = SOME y /\
    word_agree_except (op_taint tn a) x y /\
    post = update_var v (f k x) s /\
    exec_pure2 f inst t = OK (update_var v (f k y) t)
Proof
  strip_tac >>
  `eval_operand n s = eval_operand n t` by
    (drule guarded_scalar_operand >> simp[] >> disch_then irule >> simp[]) >>
  `?k x. eval_operand n s = SOME k /\ eval_operand a s = SOME x /\
       post = update_var v (f k x) s` by
    (qpat_x_assum `exec_pure2 _ _ _ = _` mp_tac >>
     simp[exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `?y. eval_operand a t = SOME y /\ word_agree_except (op_taint tn a) x y` by
    (irule guarded_masked_operand >> metis_tac[]) >>
  `eval_operand n t = SOME k` by metis_tac[] >>
  qexistsl_tac [`k`, `x`, `y`] >> simp[exec_pure2_def]
QED

Theorem shift_step_taint:
  MEM inst.inst_opcode [SHL; SHR; SAR] /\
  inst.inst_operands = [n; a] /\ inst.inst_outputs = [v] /\
  eval_operand n s = SOME k ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+ (v,shift_taint inst.inst_opcode (w2n k) (op_taint tn a))
Proof
  strip_tac >>
  `new_site_bytes s (update_var v x s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  gvs[MEM] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality]
QED



Theorem shift_prov_erasure:
  MEM inst.inst_opcode [SHL; SHR; SAR] /\ inst.inst_outputs = [v] ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE)
Proof
  strip_tac >> gvs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def, origin_set_def,
       fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem shift_execution_masked[local]:
  MEM inst.inst_opcode [SHL; SHR; SAR] /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\
  inst.inst_operands = [n; a] /\ inst.inst_outputs = [v] /\
  (!w. n = Var w ==> clean_scalar Opaque rv tn w) /\
  (!w. a = Var w ==> FLOOKUP rv w = NONE /\ ~Opaque w) /\
  step_inst_base inst s = OK post ==>
  ?k x y. eval_operand n s = SOME k /\ eval_operand n t = SOME k /\
    post = update_var v x s /\
    step_inst_base inst t = OK (update_var v y t) /\
    word_agree_except (shift_taint inst.inst_opcode (w2n k) (op_taint tn a)) x y
Proof
  strip_tac >>
  qpat_x_assum `MEM _ [SHL; SHR; SAR]` (strip_assume_tac o SRULE [MEM]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> strip_tac >>
  drule_all masked_pure2_execution >> strip_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  qexists_tac `k` >> simp[] >>
  metis_tac[word_agree_except_shl, word_agree_except_shr, word_agree_except_sar]
QED

Theorem guarded_shift_step[local]:
  MEM inst.inst_opcode [SHL; SHR; SAR] /\
  inst.inst_operands = [n; a] /\ inst.inst_outputs = [v] /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  s.vs_labels = t.vs_labels /\
  (!w. n = Var w ==> clean_scalar Opaque rv tn w) /\
  (!w. a = Var w ==> FLOOKUP rv w = NONE /\ ~Opaque w) /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) /\
  step_inst_base inst s = OK post ==>
  ?y. step_inst_base inst t = OK (update_var v y t) /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE) (step_taint inst s post tn))
      next (\s t. dead_result_rel D (Halt s) (Halt t)) post (update_var v y t) /\
    relocation_taint_le next (step_taint inst s post tn)
      (step_taint inst t (update_var v y t) un) /\
    ?x. post = update_var v x s
Proof
  strip_tac >> drule_all shift_execution_masked >> strip_tac >>
  qexists_tac `y` >> simp[] >>
  `step_taint inst s post tn =
     tn with t_var := tn.t_var |+ (v,shift_taint inst.inst_opcode (w2n k) (op_taint tn a))` by
    (qpat_x_assum `post = _` SUBST1_TAC >>
     irule shift_step_taint >> simp[] >> metis_tac[]) >>
  `step_taint inst t (update_var v y t) un =
     un with t_var := un.t_var |+ (v,shift_taint inst.inst_opcode (w2n k) (op_taint un a))` by
    (irule shift_step_taint >> simp[] >> metis_tac[]) >>
  qpat_x_assum `post = _` SUBST_ALL_TAC >> simp[] >> conj_tac
  >- (irule guarded_masked_write_restrict >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule relocation_masked_write_taint >> conj_tac
      >- (irule shift_taint_mono >>
          Cases_on `a` >> fs[relocation_taint_le_def, op_taint_def]) >>
      qexists_tac `R` >> simp[]) >>
  metis_tac[]
QED

Theorem shift_success_operands[local]:
  MEM inst.inst_opcode [SHL; SHR; SAR] /\ step_inst_base inst s = OK post ==>
  ?n a. inst.inst_operands = [n; a]
Proof
  strip_tac >>
  qpat_x_assum `MEM _ [SHL; SHR; SAR]` (strip_assume_tac o SRULE [MEM]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  Cases_on `inst.inst_operands` >> simp[exec_pure2_def] >>
  Cases_on `t` >> simp[exec_pure2_def] >>
  Cases_on `t'` >> simp[exec_pure2_def]
QED

Theorem concretize_shift_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [SHL; SHR; SAR] /\
  inst.inst_outputs = [v] /\ step_inst_base inst s = OK post /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
     fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `?n a. inst.inst_operands = [n; a]` by metis_tac[shift_success_operands] >>
  `!w. MEM (Var w) inst.inst_operands ==>
       FLOOKUP rv w = NONE /\ ~retpc_var fn w` by
    (rpt strip_tac >> drule_all shift_operand_nonpointer >> simp[]) >>
  `op_taint tn n = {}` by metis_tac[shift_count_clean] >>
  `!w. n = Var w ==> clean_scalar (retpc_var fn) rv tn w` by
    (rpt strip_tac >> fs[clean_scalar_def] >> metis_tac[MEM]) >>
  `!w. a = Var w ==> FLOOKUP rv w = NONE /\ ~retpc_var fn w` by
    (rpt strip_tac >> metis_tac[MEM]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     qpat_x_assum `MEM _ [SHL; SHR; SAR]` (strip_assume_tac o SRULE [MEM]) >>
     simp[joint_writes_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
          range_bytes_def] >> metis_tac[]) >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  drule_all guarded_shift_step >> strip_tac >>
  qexists_tac `update_var v y t` >> simp[] >>
  conj_tac >- (irule shift_prov_erasure >> simp[]) >>
  qpat_x_assum `post = _` SUBST_ALL_TAC >>
  simp[relocation_env_update_var, relocation_reader_context_update_var]
QED
