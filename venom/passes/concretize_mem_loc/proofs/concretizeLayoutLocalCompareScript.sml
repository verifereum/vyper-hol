Theory concretizeLayoutLocalCompare
Ancestors concretizeLayoutPointerRanges frameRelocationCompareAccess
  frameRelocationCompareSteps frameActivationSeparation frameResolvedTrace
  frameActivationLifetime frameActivationCache frameJointTransition finite_map list
  frameActivationLookup frameRawEndpoints concretizeLayoutPositions
  concretizeLayoutLocalAffine frameRelocationCleanOperands frameRelocationScalarSteps
  frameRelocationEnvironment concretizeLayoutReaderContext frameRelocationReachableSupport
  frameRelocationBinding frameJointDemand frameJointTrace frameJointTaint
  frameOriginReachable frameOriginHistory frameRelocationLocal frameRelocationDemand
  frameRelocationGuardedValues frameOriginUpdates venomExecSemantics venomState
  venomInst ptrDiscipline frameRelocationOpaque pointerConfinedDefs memLocDefs
  codegenRel frameRelocationCleanValueSteps

Theorem resolved_positive_site_tokens[local]:
  joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  vs0.vs_allocas = FEMPTY /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  FLOOKUP rv u = SOME ((tu,au),(b,sz)) /\
  FLOOKUP rv w = SOME ((tw,aw),(b,sz)) /\ 0 < sz ==>
  (tu,au) = (tw,aw)
Proof
  strip_tac >>
  `?ku owneru. ku < LENGTH (birth::ids) /\ EL ku (birth::ids) = tu /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk-ku) owneru au (b,sz)` by metis_tac[resolved_current_owner] >>
  `?kw ownerw. kw < LENGTH (birth::ids) /\ EL kw (birth::ids) = tw /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk-kw) ownerw aw (b,sz)` by metis_tac[resolved_current_owner] >>
  `LENGTH stk-ku = LENGTH stk-kw /\ owneru = ownerw /\ au = aw` by
    (`b <= b /\ b < b+sz` by decide_tac >>
     metis_tac[joint_activation_cache_byte_unique]) >>
  `LENGTH ids = LENGTH stk` by fs[lifetime_ok_def, activation_depth_def] >>
  `ku = kw` by (fs[] >> decide_tac) >> gvs[]
QED

Theorem concretize_comparison_geometry:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\
  joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  access_ok lo G fn inst s /\
  (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
  inst.inst_operands = [Var u; Var w] /\
  (FLOOKUP rv u <> NONE \/ FLOOKUP rv w <> NONE) ==>
  ?token aid b sz x z.
    FLOOKUP rv u = SOME ((token,aid),(b,sz)) /\
    FLOOKUP rv w = SOME ((token,aid),(b,sz)) /\
    lookup_var u s = SOME x /\ lookup_var w s = SOME z /\
    b <= w2n x /\ w2n x <= b+sz /\
    b <= w2n z /\ w2n z <= b+sz /\
    b+sz < dimword (:256) /\
    activation_lookup (0:num) (concretize_positions C') (birth::ids)
      (fn::MAP (\f. f.cf_fn) stk) (token,aid) + sz < dimword (:256)
Proof
  strip_tac >> (
  drule resolved_config_current >> simp[] >> strip_tac >>
  drule resolved_compare_access >> disch_then drule >>
  disch_then (qspecl_then [`w`, `u`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  PairCases_on `tu` >> PairCases_on `tw` >>
  `((tu0,tu1):num # num) = (tw0,tw1)` by
    (irule resolved_positive_site_tokens >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >> gvs[] >>
  `?d owner.
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      d owner tu1 (b,sz) /\
    activation_lookup (0:num) (concretize_positions C') (birth::ids)
      (fn::MAP (\f. f.cf_fn) stk) (tu0,tu1) = concretize_positions C' owner tu1` by
    metis_tac[resolved_activation_lookup] >>
  `b+sz < dimword (:256)` by
    (drule_all joint_activation_cache_strict >> simp[]) >>
  drule_all concretize_positions_activation_numeric >> strip_tac >>
  simp[arithmeticTheory.ADD_COMM])
QED

Theorem disciplined_compare_vars[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
  MEM (Var w) inst.inst_operands /\ w IN fn_pv P fn ==>
  ?u v. inst.inst_operands = [Var u; Var v]
Proof
  strip_tac >> (
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
  simp[ptr_use_ok_def] >> strip_tac >>
  first_x_assum (qspec_then `w` mp_tac) >>
  gvs[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  metis_tac[])
QED

Theorem concretize_compare_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
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
  strip_tac >> (
  `scalar_binary_opcode inst.inst_opcode` by simp[scalar_binary_opcode_def] >>
  `joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h)` by
    (drule_all joint_trace_edge_at >> strip_tac >> gvs[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s /\ access_ok lo G fn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `?a b z. inst.inst_operands = [a;b] /\ post = update_var v z s` by
    (drule_all scalar_binary_dispatch >> strip_tac >>
     `exec_pure2 f inst s = OK post` by metis_tac[] >>
     gvs[exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `!w. MEM (Var w) inst.inst_operands ==> ~retpc_var fn w` by
    (rpt strip_tac >> drule_all disciplined_retpc_operand_use >> gvs[]) >>
  `!s t x y. dead_result_rel D (Halt s) (Halt t) ==>
     dead_result_rel D (Halt (update_var v x s)) (Halt (update_var v y t))` by
    simp[dead_result_rel_def, update_var_def] >>
  `?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost` by
    (Cases_on `!w. MEM (Var w) inst.inst_operands ==> FLOOKUP rv w = NONE`
     >- (
  `!w. MEM (Var w) inst.inst_operands ==> clean_scalar (retpc_var fn) rv tn w` by
    (rpt strip_tac >>
     `~MEM inst.inst_opcode [ASSIGN; PHI; RET; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE]` by simp[] >>
     `FLOOKUP rv w = NONE` by metis_tac[] >>
     drule_all disciplined_clean_scalar >> simp[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_scalar_binary_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >> simp[] >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- (simp[relocation_env_def, dead_result_rel_def, update_var_def] >>
     fs[relocation_env_def] >> rpt strip_tac >>
     qpat_x_assum `!w. MEM (Var w) _ ==> clean_scalar _ _ _ _` irule >> simp[])) >>
  strip_tac >> goal_assum (drule_at Any) >> simp[])
     >> (
  `?w. MEM (Var w) inst.inst_operands /\ FLOOKUP rv w <> NONE` by metis_tac[] >>
  `w IN fn_pv P fn` by metis_tac[] >>
  `?u k. inst.inst_operands = [Var u; Var k]` by
    (irule disciplined_compare_vars >> simp[] >>
     qexistsl_tac [`P`, `fn`, `w`] >> gvs[]) >>
  `FLOOKUP rv u <> NONE \/ FLOOKUP rv k <> NONE` by (fs[] >> metis_tac[]) >>
  drule_at (Pat `ctx_pass_stage _ _ _ _ _`) concretize_comparison_geometry >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `lifetime_ok _ _ _`)) >>
  disch_then (qspecl_then [`k`, `vs0`, `u`, `lo`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_pointer_compare_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  simp[] >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[])) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def] >> metis_tac[]) >>
  `?y. tpost = update_var v y t` by
    (drule scalar_binary_dispatch >> strip_tac >>
     `exec_pure2 f inst t = OK tpost` by metis_tac[] >>
     gvs[exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `step_taint inst s post tn = tn with t_var := tn.t_var |+ (v,{})` by
    (gvs[] >> irule scalar_binary_taint >> simp[]) >>
  `step_taint inst t tpost un = un with t_var := un.t_var |+ (v,{})` by
    (gvs[] >> irule scalar_binary_taint >> simp[]) >>
  `step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE)` by
    (irule compare_prov_erasure >> simp[]) >>
  qexists_tac `tpost` >> gvs[] >>
  conj_tac
  >- (fs[local_rel_def] >> irule demand_agree_restrict >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule relocation_clean_write_taint >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (irule relocation_env_update_var >> simp[]) >>
  irule relocation_reader_context_update_var >> simp[])
QED

val _ = export_theory();
