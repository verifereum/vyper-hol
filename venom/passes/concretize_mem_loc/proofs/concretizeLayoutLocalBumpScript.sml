Theory concretizeLayoutLocalBump
Ancestors concretizeLayoutLocalOffset concretizeLayoutLocalValues concretizeLayoutReaderContext
  frameRelocationEnvironment frameRelocationCleanValueSteps frameRelocationMemory
  frameRelocationCleanOperands frameRelocationReachableSupport frameRelocationGuardedValues
  concretizeLayoutOperandCleanliness concretizeLayoutLoadProduction
  pointerConfinedDefs memLocDefs frameRelocationBinding frameJointDemand
  frameJointTrace frameJointTransition frameResolvedTrace frameJointTaint
  frameOriginReachable frameOriginHistory frameOriginUpdates
  frameRelocationGhostCopy frameRelocationLocal frameRelocationDemand frameRelocationTaintOrder frameRelocationCopyTaint
  ptrDiscipline venomExecSemantics venomState codegenRel finite_map pred_set list

Theorem bump_execution[local]:
  inst.inst_opcode = BUMP /\ inst.inst_outputs = [v;w] /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst_base inst s = OK post ==>
  ?base sz. post = update_var w (word_add base sz) (update_var v base s) /\
    step_inst_base inst t = OK (update_var w (word_add base sz) (update_var v base t))
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t'` >> simp[] >> Cases_on `t''` >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `eval_operand h t = eval_operand h s /\
   eval_operand h' t = eval_operand h' s` by metis_tac[MEM] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> metis_tac[]
QED

Theorem bump_ghosts[local]:
  inst.inst_opcode = BUMP /\ inst.inst_outputs = [v;w] ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v;w] NONE) /\
  step_taint inst s (update_var w y (update_var v x s)) tn =
    tn with t_var := DRESTRICT tn.t_var (COMPL {v;w})
Proof
  strip_tac >> (conj_tac
  >- (simp[step_prov_def, out_prov_def, set_prov_def,
           origin_set_def, fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
      gen_tac >> IF_CASES_TAC >> simp[])) >>
  `new_site_bytes s (update_var w y (update_var v x s)) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality] >>
  rpt CASE_TAC >> simp[]
QED

Theorem guarded_two_clean_writes[local]:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  (!a b. next a b ==> R a b) ==>
  local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v;w] NONE))
    (guarded_bytes Opaque (origin_set rv [v;w] NONE)
      (tn with t_var := DRESTRICT tn.t_var (COMPL {v;w}))) next
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var w y (update_var v x s)) (update_var w y (update_var v x t))
Proof
  strip_tac >>
  `local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
    (guarded_bytes Opaque (origin_set rv [v] NONE)
      (tn with t_var := tn.t_var |+ (v,{}))) R
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var v x s) (update_var v x t)` by
    (irule guarded_clean_write_restrict >> goal_assum (drule_at Any) >> simp[]) >>
  `local_rel (\u. F)
    (guarded_ptr Opaque L (origin_set (origin_set rv [v] NONE) [w] NONE))
    (guarded_bytes Opaque (origin_set (origin_set rv [v] NONE) [w] NONE)
      ((tn with t_var := tn.t_var |+ (v,{})) with t_var :=
        ((tn with t_var := tn.t_var |+ (v,{})).t_var |+ (w,{})))) next
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var w y (update_var v x s)) (update_var w y (update_var v x t))` by
    (irule guarded_clean_write_restrict >>
     goal_assum (drule_at Any) >> simp[]) >>
  `origin_set (origin_set rv [v] NONE) [w] NONE = origin_set rv [v;w] NONE` by
    (simp[fmap_eq_flookup, origin_set_lookup] >> metis_tac[]) >>
  `(guarded_bytes Opaque (origin_set rv [v;w] NONE)
    ((tn with t_var := tn.t_var |+ (v,{})) with t_var :=
        ((tn with t_var := tn.t_var |+ (v,{})).t_var |+ (w,{}))) : string -> bytes32 -> bytes32 -> bool) =
   guarded_bytes Opaque (origin_set rv [v;w] NONE)
    (tn with t_var := DRESTRICT tn.t_var (COMPL {v;w}))` by
    (simp[FUN_EQ_THM, guarded_bytes_def, copy_bytes_def, op_taint_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     rpt gen_tac >> Cases_on `x' = v` >> Cases_on `x' = w` >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem two_clear_taint[local]:
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  relocation_taint_le next
    (tn with t_var := DRESTRICT tn.t_var (COMPL {v;w}))
    (un with t_var := DRESTRICT un.t_var (COMPL {v;w}))
Proof
  simp[relocation_taint_le_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  strip_tac >> conj_tac
  >- (fs[demand_taint_def] >> metis_tac[]) >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem concretize_bump_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = BUMP /\
  inst.inst_outputs = [v;w] /\ step_inst_base inst s = OK post /\
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
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v;w] NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv [v;w] NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v;w] NONE) /\
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
  `!u. MEM (Var u) inst.inst_operands ==> clean_scalar (retpc_var fn) rv tn u` by
    (rpt strip_tac >>
     `~is_pointer_preserving_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
      ~MEM inst.inst_opcode [EQ; LT; GT; ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
      mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by
       simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
     drule_all nonpointer_operand_clean >> simp[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def, range_bytes_def] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_scalar_operand >>
     disch_then (qspec_then `op` mp_tac) >>
     gvs[relocation_env_def] >> metis_tac[]) >>
  drule_all bump_execution >> strip_tac >>
  rename1 `post = update_var w (word_add bval sz) (update_var v bval s)` >>
  qexists_tac `update_var w (word_add bval sz) (update_var v bval t)` >> simp[] >>
  `step_taint inst s post tn = tn with t_var := DRESTRICT tn.t_var (COMPL {v;w})` by
    (gvs[] >> metis_tac[bump_ghosts]) >>
  `step_taint inst t (update_var w (word_add bval sz) (update_var v bval t)) un =
    un with t_var := DRESTRICT un.t_var (COMPL {v;w})` by metis_tac[bump_ghosts] >>
  simp[bump_ghosts] >> conj_tac
  >- (gvs[] >> irule guarded_two_clean_writes >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule two_clear_taint >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> conj_tac
  >- (irule relocation_env_update_var >> irule relocation_env_update_var >> simp[]) >>
  irule relocation_reader_context_update_var >> irule relocation_reader_context_update_var >> simp[]
QED

val _ = if null (hyp concretize_bump_local_complete) then ()
        else raise Fail "BUMP export has hypotheses";
val _ = export_theory();
