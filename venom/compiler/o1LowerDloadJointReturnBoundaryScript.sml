(* Internal return assembly: current callee effects, restored caller locals. *)
Theory o1LowerDloadJointReturnBoundary
Ancestors
  o1LowerDloadJointReturn o1LowerDloadJointRestore o1LowerDloadJointPop
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadShared
  o1LowerDloadMapEvolution o1LowerDloadEnvironment o1LowerDloadOpaque
  ptrDiscipline venomExecSemantics venomState contextCodegenRel
  finite_map list pred_set

Theorem ld_joint_boundary_return:
  ld_joint_boundary vs C C' lo D (f::stk) PG G tn fn rinst s t
    n a (ofr::U) B HP H sites X (caller'::ts) /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn rinst s /\ rinst.inst_opcode = RET /\
  step_inst fuel C rinst s = IntRet ir s_end /\
  bind_outputs f.cf_inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state f.cf_state s_end)) = SOME s1 /\
  active_inst f.cf_fn next (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
  active_inst f.cf_fn f.cf_inst f.cf_state /\ f.cf_inst.inst_opcode = INVOKE /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) f.cf_fn.fn_blocks) /\
  s.vs_call_ctx.cc_address = f.cf_state.vs_call_ctx.cc_address ==>
  ?jr t1 fn'. step_inst fuel C' rinst t = IntRet jr t /\
    jr.iret_values = ir.iret_values /\ jr.iret_adopt_fmp = NONE /\
    ir.iret_adopt_fmp = NONE /\
    lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fn' /\
    active_inst fn' f.cf_inst caller' /\
    bind_outputs f.cf_inst.inst_outputs jr.iret_values
      (adopt_return_fmp jr (merge_callee_state caller' t)) = SOME t1 /\
    ld_joint_boundary vs C C' lo D stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t1 with vs_inst_idx := SUC caller'.vs_inst_idx)
      n ofr.of_owner U (DRESTRICT B {id | FST id <> a}) ofr.of_params
      (DRESTRICT ofr.of_prov (COMPL (set f.cf_inst.inst_outputs)))
      (DRESTRICT sites {id | FST id <> a})
      (DRESTRICT X {id | FST id <> a}) ts
Proof
  strip_tac >> drule_all ld_joint_ret_step >> strip_tac >>
  gvs[adopt_return_fmp_def] >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  `occurrence_saved_ok B (ofr::U) (f::stk) /\
   ~MEM a (MAP (\u. u.of_owner) (ofr::U))` by
    fs[occurrence_annotation_ok_def] >>
  drule_all ld_joint_saved_drop_owner >>
  simp[ld_joint_saved_def] >> strip_tac >>
  drule_all ld_joint_frame_return_next >>
  disch_then (qspec_then `t` strip_assume_tac) >>
  qexistsl_tac [`t1`, `fn''`] >> simp[adopt_return_fmp_def] >>
  simp[ld_joint_boundary_def] >> rpt conj_tac
  >- suspend "source"
  >- suspend "annotation"
  >- suspend "erasure"
  >- suspend "geometry"
  >- suspend "frame"
  >- suspend "memory"
  >- suspend "shared"
  >> suspend "returndata"
QED

Resume ld_joint_boundary_return[source]:
  irule (last (CONJUNCTS occ_frame_reachable_rules)) >>
  fs[adopt_return_fmp_def] >>
  goal_assum (drule_at (Pat `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`fuel`, `ir`, `s`] >> fs[]
QED

Resume ld_joint_boundary_return[annotation]:
  drule occurrence_annotation_return >>
  simp[adopt_return_fmp_def] >>
  disch_then irule >> qexistsl_tac [`ir`, `s`, `ir.iret_values`] >>
  fs[]
QED

Resume ld_joint_boundary_return[erasure]:
  irule ld_joint_erasure_restrict >> simp[]
QED

Resume ld_joint_boundary_return[geometry]:
  irule ld_joint_geometry_drop_owner >> fs[]
QED

Resume ld_joint_boundary_return[frame]:
  goal_assum drule
QED

Resume ld_joint_boundary_return[memory]:
  qpat_assum `bind_outputs _ _ _ = SOME s1`
    (assume_tac o MATCH_MP ld_bind_outputs_vars_only) >>
  qpat_assum `bind_outputs _ _ _ = SOME t1`
    (assume_tac o MATCH_MP ld_bind_outputs_vars_only) >>
  qpat_x_assum `s1 = _`
    (mp_tac o AP_TERM ``\u:venom_state. u.vs_memory``) >>
  simp[merge_callee_state_def] >> strip_tac >>
  qpat_x_assum `t1 = _`
    (mp_tac o AP_TERM ``\u:venom_state. u.vs_memory``) >>
  simp[merge_callee_state_def] >> strip_tac >>
  simp[] >> irule ld_memory_agree_restrict >> simp[]
QED

Resume ld_joint_boundary_return[shared]:
  `ld_shared_agree D s.vs_call_ctx.cc_address tn
     (merge_callee_state f.cf_state s) (merge_callee_state caller' t)` by
    (irule ld_shared_agree_merge >> simp[]) >>
  drule_all ld_shared_agree_bind_outputs >> strip_tac >>
  qpat_assum `bind_outputs _ _ _ = SOME s1`
    (mp_tac o AP_TERM ``\u:venom_state. u.vs_call_ctx`` o
      MATCH_MP ld_bind_outputs_vars_only) >>
  simp[merge_callee_state_def] >> strip_tac >>
  qpat_x_assum `s.vs_call_ctx.cc_address = _`
    (fn th => fs[th, ld_shared_agree_def])
QED

Resume ld_joint_boundary_return[returndata]:
  qpat_assum `bind_outputs _ _ _ = SOME s1`
    (mp_tac o AP_TERM ``\u:venom_state. u.vs_returndata`` o
      MATCH_MP ld_bind_outputs_vars_only) >>
  simp[merge_callee_state_def] >> strip_tac >>
  qpat_assum `bind_outputs _ _ _ = SOME t1`
    (mp_tac o AP_TERM ``\u:venom_state. u.vs_returndata`` o
      MATCH_MP ld_bind_outputs_vars_only) >>
  simp[merge_callee_state_def]
QED

Finalise ld_joint_boundary_return
