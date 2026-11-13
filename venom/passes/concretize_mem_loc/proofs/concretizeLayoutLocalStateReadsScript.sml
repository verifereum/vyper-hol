Theory concretizeLayoutLocalStateReads
Ancestors concretizeLayoutStateTransport concretizeLayoutSupplement
  frameRelocationCleanValueSteps
  concretizeLayoutLocalShifts concretizeLayoutLocalExtcodeSize
  ptrDiscipline venomExecSemantics venomState frameRelocationEnvironment
  concretizeLayoutReaderContext frameRelocationGuardedValues
  frameRelocationLocal frameRelocationTaintOrder frameOriginUpdates
  frameRelocationMemory frameOriginHistory
  codegenRel finite_map pred_set list
  concretizeLayoutOperandCleanliness frameRelocationCleanOperands
  frameRelocationReachableSupport frameJointTrace frameJointTransition
  frameResolvedTrace frameJointTaint frameOriginReachable
  pointerConfinedDefs memLocDefs frameRelocationBinding frameJointDemand

Theorem state_read_execution[local]:
  MEM inst.inst_opcode [SLOAD; TLOAD] /\
  inst.inst_operands = [arg] /\ inst.inst_outputs = [v] /\
  concretize_supplement D tn s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  eval_operand arg s = eval_operand arg t /\
  step_inst_base inst s = OK post ==>
  ?k x y. eval_operand arg s = SOME k /\
    post = update_var v x s /\
    step_inst_base inst t = OK (update_var v y t) /\
    word_agree_except
      (key_taint (if inst.inst_opcode = SLOAD then tn.t_stor else tn.t_trans) k) x y
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_read1_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_read1_def] >>
  metis_tac[concretize_supplement_sload, concretize_supplement_tload]
QED

Theorem state_read_ghosts[local]:
  MEM inst.inst_opcode [SLOAD; TLOAD] /\
  inst.inst_operands = [arg] /\ inst.inst_outputs = [v] /\
  eval_operand arg s = SOME k ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
  step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+
      (v,key_taint (if inst.inst_opcode = SLOAD then tn.t_stor else tn.t_trans) k)
Proof
  strip_tac >> (conj_tac
  >- (gvs[MEM] >>
      simp[step_prov_def, out_prov_def, set_prov_def, origin_set_def,
           fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
      gen_tac >> IF_CASES_TAC >> simp[])) >>
  `new_site_bytes s (update_var v x s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  gvs[MEM] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality]
QED

Theorem state_read_taint_order[local]:
  MEM inst.inst_opcode [SLOAD; TLOAD] /\
  inst.inst_operands = [arg] /\ inst.inst_outputs = [v] /\
  eval_operand arg s = SOME k /\ eval_operand arg t = SOME k /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  relocation_taint_le next (step_taint inst s (update_var v x s) tn)
    (step_taint inst t (update_var v y t) un)
Proof
  strip_tac >>
  `key_taint (if inst.inst_opcode = SLOAD then un.t_stor else un.t_trans) k
   SUBSET key_taint (if inst.inst_opcode = SLOAD then tn.t_stor else tn.t_trans) k` by
    (fs[relocation_taint_le_def, MEM, key_taint_def, SUBSET_DEF] >> metis_tac[]) >>
  `step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+
      (v,key_taint (if inst.inst_opcode = SLOAD then tn.t_stor else tn.t_trans) k)` by
    metis_tac[cj 2 state_read_ghosts] >>
  `step_taint inst t (update_var v y t) un =
    un with t_var := un.t_var |+
      (v,key_taint (if inst.inst_opcode = SLOAD then un.t_stor else un.t_trans) k)` by
    metis_tac[cj 2 state_read_ghosts] >>
  simp[] >> irule relocation_masked_write_taint >>
  simp[] >> qexists_tac `R` >> simp[]
QED

Theorem guarded_state_read_step:
  MEM inst.inst_opcode [SLOAD; TLOAD] /\
  inst.inst_operands = [arg] /\ inst.inst_outputs = [v] /\
  (!w. arg = Var w ==> clean_scalar Opaque rv tn w) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) /\
  step_inst_base inst s = OK post ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE) (step_taint inst s post tn))
      next concretize_local_obs post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_taint_le next (step_taint inst s post tn) (step_taint inst t tpost un) /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_env post tpost /\ relocation_reader_context post tpost /\
    (?x y. post = update_var v x s /\ tpost = update_var v y t)
Proof
  strip_tac >>
  `eval_operand arg s = eval_operand arg t` by
    (drule guarded_scalar_operand >>
     disch_then irule >> fs[relocation_env_def]) >>
  `s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address` by
    fs[relocation_env_def] >>
  drule_all state_read_execution >> strip_tac >>
  qexists_tac `update_var v y t` >> simp[] >>
  `step_taint inst s post tn = tn with t_var := tn.t_var |+
    (v,key_taint (if inst.inst_opcode = SLOAD then tn.t_stor else tn.t_trans) k)` by
    (qpat_x_assum `post = _` SUBST_ALL_TAC >>
     irule (cj 2 state_read_ghosts) >> simp[]) >>
  `step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE)` by
    metis_tac[cj 1 state_read_ghosts] >>
  conj_tac
  >- (gvs[] >>
      fs[lambdify (lambdify concretize_local_obs_def)] >>
      irule guarded_masked_write_restrict >> simp[] >>
      qexists_tac `R` >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qpat_x_assum `post = _` SUBST_ALL_TAC >>
    irule state_read_taint_order >> simp[] >>
    conj_tac >- metis_tac[] >> qexists_tac `R` >> simp[]) >>
  conj_tac
  >- (gvs[] >> irule concretize_supplement_fields >>
      qexistsl_tac [`s`,`t`,`tn`] >> simp[update_var_def]) >>
  gvs[] >> metis_tac[relocation_env_update_var, relocation_reader_context_update_var]
QED

Theorem concretize_state_read_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  MEM inst.inst_opcode [SLOAD; TLOAD] /\ inst.inst_operands = [arg] /\
  inst.inst_outputs = [v] /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  step_inst_base inst s = OK post /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    concretize_local_obs s t /\ concretize_supplement D tn s t /\
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
      concretize_local_obs post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_env post tpost /\ relocation_reader_context post tpost /\
    (?x y. post = update_var v x s /\ tpost = update_var v y t)
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
  `!x. arg = Var x ==> clean_scalar (retpc_var fn) rv tn x` by
    (rpt strip_tac >>
     `MEM (Var x) inst.inst_operands` by simp[] >>
     `~is_pointer_preserving_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
      ~MEM inst.inst_opcode [EQ; LT; GT; ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
      mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by
       (gvs[MEM] >> simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]) >>
     drule_all nonpointer_operand_clean >> simp[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def] >> gvs[MEM] >>
     simp[source_memory_write_ranges_def] >> metis_tac[]) >>
  irule guarded_state_read_step >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `joint_relocation_demand lo (concretize_positions C') q0 es qs c` >> simp[]
QED
