Theory concretizeLayoutLocalStateWrites
Ancestors concretizeLayoutStateTransport concretizeLayoutLocalStateReads
  venomExecSemantics venomState ptrDiscipline frameRelocationStoreValues
  frameRelocationEnvironment frameRelocationTaintOrder concretizeLayoutReaderContext
  frameRelocationCleanOperands
  frameRelocationMemory frameOriginHistory frameOriginUpdates frameRelocationCopyTaint
  codegenRel frameRelocationLocal frameRelocationValues
  frameRelocationGuardedValues frameRelocationGhostCopy frameRelocationDemand
  finite_map pred_set list
  frameRelocationReachableSupport frameJointTrace frameJointTransition
  frameResolvedTrace frameJointTaint frameOriginReachable frameRelocationOpaque
  pointerConfinedDefs memLocDefs frameRelocationBinding frameJointDemand venomWf o1PassContract

Theorem state_write_execution[local]:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  inst.inst_operands = [arg; value] /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  eval_operand arg s = eval_operand arg t /\
  IS_SOME (eval_operand value t) /\
  step_inst_base inst s = OK post ==>
  ?k x y. eval_operand arg s = SOME k /\ eval_operand arg t = SOME k /\
    eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
    post = (if inst.inst_opcode = SSTORE then sstore k x s else tstore k x s) /\
    step_inst_base inst t = OK
      (if inst.inst_opcode = SSTORE then sstore k y t else tstore k y t)
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_write2_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `eval_operand value t` >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  gvs[exec_write2_def, eval_operands_def]
QED

Theorem state_write_ghosts[local]:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  inst.inst_operands = [arg; value] /\ inst.inst_outputs = [] /\
  eval_operand arg s = SOME k ==>
  step_prov PG (SND o_f rv) inst post = SND o_f rv /\
  step_taint inst s
    (if inst.inst_opcode = SSTORE then sstore k x s else tstore k x s) tn =
    if inst.inst_opcode = SSTORE then
      tn with t_stor := key_update tn.t_stor k (op_taint tn value)
    else tn with t_trans := key_update tn.t_trans k (op_taint tn value)
Proof
  strip_tac >> (conj_tac
  >- (gvs[MEM] >> simp[step_prov_def, set_prov_def, fmap_eq_flookup, FLOOKUP_DRESTRICT])) >>
  `new_site_bytes s (sstore k x s) = {} /\
   new_site_bytes s (tstore k x s) = {}` by
    (conj_tac >> irule new_site_bytes_unchanged >> simp[sstore_def, tstore_def]) >>
  gvs[MEM] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality,
       fmap_eq_flookup, FLOOKUP_DRESTRICT]
QED

Theorem state_write_taint_order[local]:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  inst.inst_operands = [arg; value] /\ inst.inst_outputs = [] /\
  eval_operand arg s = SOME k /\ eval_operand arg t = SOME k /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  relocation_taint_le next
    (step_taint inst s
      (if inst.inst_opcode = SSTORE then sstore k x s else tstore k x s) tn)
    (step_taint inst t
      (if inst.inst_opcode = SSTORE then sstore k y t else tstore k y t) un)
Proof
  strip_tac >>
  `step_taint inst s
     (if inst.inst_opcode = SSTORE then sstore k x s else tstore k x s) tn =
     if inst.inst_opcode = SSTORE then
       tn with t_stor := key_update tn.t_stor k (op_taint tn value)
     else tn with t_trans := key_update tn.t_trans k (op_taint tn value)` by
    (irule (cj 2 state_write_ghosts) >> simp[]) >>
  `step_taint inst t
     (if inst.inst_opcode = SSTORE then sstore k y t else tstore k y t) un =
     if inst.inst_opcode = SSTORE then
       un with t_stor := key_update un.t_stor k (op_taint un value)
     else un with t_trans := key_update un.t_trans k (op_taint un value)` by
    (irule (cj 2 state_write_ghosts) >> simp[]) >>
  `op_taint un value SUBSET op_taint tn value` by
    (Cases_on `value` >> fs[op_taint_def, relocation_taint_le_def]) >>
  gvs[MEM, relocation_taint_le_def, demand_taint_def, key_update_def, SUBSET_DEF] >>
  fs[op_taint_def] >> metis_tac[]
QED

Theorem state_write_local_transport[local]:
  MEM opc [SSTORE; TSTORE] /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R concretize_local_obs s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  (!a b. next a b ==> R a b) ==>
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv
      (if opc = SSTORE then tn with t_stor := key_update tn.t_stor k m
       else tn with t_trans := key_update tn.t_trans k m))
    next concretize_local_obs
    (if opc = SSTORE then sstore k x s else tstore k x s)
    (if opc = SSTORE then sstore k y t else tstore k y t)
Proof
  strip_tac >>
  `concretize_local_obs s t` by metis_tac[local_rel_observation] >>
  `concretize_local_obs (sstore k x s) (sstore k y t) /\
   concretize_local_obs (tstore k x s) (tstore k y t)` by
    metis_tac[concretize_local_obs_sstore, concretize_local_obs_tstore] >>
  gvs[MEM, local_rel_def, local_values_def, variable_domains_def,
      variables_agree_on_def, lookup_var_def, sstore_def, tstore_def,
      guarded_bytes_def, copy_bytes_def, op_taint_def, demand_agree_def] >>
  metis_tac[]
QED

Theorem guarded_state_write_step:
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  inst.inst_operands = [arg; value] /\ inst.inst_outputs = [] /\
  (!w. arg = Var w ==> clean_scalar Opaque rv tn w) /\
  (!w. value = Var w ==> ~Opaque w /\ FLOOKUP rv w = NONE) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) /\
  step_inst_base inst s = OK post ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F) (guarded_ptr Opaque L rv)
      (guarded_bytes Opaque rv (step_taint inst s post tn))
      next concretize_local_obs post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f rv /\
    relocation_taint_le next (step_taint inst s post tn) (step_taint inst t tpost un) /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >>
  `eval_operand arg s = eval_operand arg t` by
    (drule guarded_scalar_operand >> disch_then irule >> fs[relocation_env_def]) >>
  `?k x. eval_operand arg s = SOME k /\ eval_operand value s = SOME x` by
    (gvs[MEM] >> qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
     simp[exec_write2_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  `?y. eval_operand value t = SOME y /\ word_agree_except (op_taint tn value) x y` by
    (drule frameRelocationStoreValuesTheory.guarded_masked_operand >>
     disch_then irule >> fs[relocation_env_def]) >>
  `s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
   s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address` by fs[relocation_env_def] >>
  `IS_SOME (eval_operand value t)` by simp[] >>
  drule_all state_write_execution >> strip_tac >>
  `step_taint inst s
     (if inst.inst_opcode = SSTORE then sstore k x s else tstore k x s) tn =
     if inst.inst_opcode = SSTORE then
       tn with t_stor := key_update tn.t_stor k (op_taint tn value)
     else tn with t_trans := key_update tn.t_trans k (op_taint tn value)` by
    (irule (cj 2 state_write_ghosts) >> simp[] >> metis_tac[optionTheory.SOME_11]) >>
  `local_rel (\u. F) (guarded_ptr Opaque L rv)
      (guarded_bytes Opaque rv
        (if inst.inst_opcode = SSTORE then tn with t_stor := key_update tn.t_stor k (op_taint tn value)
         else tn with t_trans := key_update tn.t_trans k (op_taint tn value)))
      next concretize_local_obs
      (if inst.inst_opcode = SSTORE then sstore k x s else tstore k x s)
      (if inst.inst_opcode = SSTORE then sstore k y t else tstore k y t)` by
    (drule_all state_write_local_transport >> disch_then irule >> simp[]) >>
  `relocation_taint_le next
     (step_taint inst s (if inst.inst_opcode = SSTORE then sstore k x s else tstore k x s) tn)
     (step_taint inst t (if inst.inst_opcode = SSTORE then sstore k y t else tstore k y t) un)` by
    (drule state_write_taint_order >> disch_then irule >> simp[] >>
     conj_tac >- metis_tac[optionTheory.SOME_11] >> qexists_tac `R` >> simp[]) >>
  `step_prov PG (SND o_f rv) inst post = SND o_f rv` by
    metis_tac[cj 1 state_write_ghosts] >>
  gvs[] >>
  (conj_tac >- metis_tac[concretize_supplement_sstore, concretize_supplement_tstore]) >>
  fs[relocation_env_def, relocation_reader_context_def, sstore_def, tstore_def]
QED

Theorem concretize_state_write_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
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
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f rv /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[o1PassContractTheory.o1_fn_shape_def, fn_inst_wf_def,
        venomInstTheory.fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `?arg value. inst.inst_operands = [arg; value] /\ inst.inst_outputs = []` by
    (gvs[MEM, inst_wf_def] >>
     Cases_on `inst.inst_operands` >> gvs[] >>
     rename1 `a::rest` >> Cases_on `rest` >> gvs[] >>
     rename1 `b::tail` >> Cases_on `tail` >> gvs[]) >>
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
  `!w. MEM (Var w) inst.inst_operands ==> ~retpc_var fn w` by
    (rpt strip_tac >> drule_all disciplined_retpc_operand_use >>
     gvs[MEM]) >>
  `!w. MEM (Var w) inst.inst_operands ==> FLOOKUP rv w = NONE` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `w IN fn_pv P fn` by metis_tac[] >>
     `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
     gvs[MEM, ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  `!w. arg = Var w ==> clean_scalar (retpc_var fn) rv tn w` by
    (rpt strip_tac >> simp[clean_scalar_def] >>
     `MEM (Var w) inst.inst_operands` by simp[] >>
     `~retpc_var fn w /\ FLOOKUP rv w = NONE` by metis_tac[] >>
     simp[] >> fs[taint_ok_def] >>
     spose_not_then assume_tac >>
     first_x_assum (qspec_then `Var w` mp_tac) >> gvs[MEM]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def] >> gvs[MEM] >>
     simp[source_memory_write_ranges_def] >> metis_tac[]) >>
  irule guarded_state_write_step >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `joint_relocation_demand lo (concretize_positions C') q0 es qs c` >>
  simp[] >> metis_tac[]
QED
