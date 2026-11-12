Theory concretizeLayoutCallerResume
Ancestors concretizeLayoutCallResult concretizeLayoutPhaseOrigin
  frameRelocationGuardedValues frameRelocationTaintOrder frameRelocationCopyTaint
  frameRelocationReachableSupport frameRelocationBinding frameJointDemand
  frameRelocationDemand frameJointTrace codegenRel
  venomExecSemantics venomState venomInstProofs1 ptrDiscipline
  finite_map pred_set list

(* This is a call-entry snapshot, not a hypothesis about the resumed state. *)
Definition layout_saved_caller_def:
  layout_saved_caller D lo C' q0 es qs g caller caller' <=>
    ~g.lop_pending /\
    layout_ordinary_state D lo C' q0 es qs g caller caller'
End

Theorem layout_return_parameters:
  parameter_roots Rel caller.vs_params caller'.vs_params /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME post /\
  bind_outputs outs' ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' callee')) = SOME post' ==>
  parameter_roots Rel post.vs_params post'.vs_params
Proof
  strip_tac >>
  qspec_then `\s. s.vs_params` mp_tac bind_outputs_preserves >>
  simp[update_var_def] >> strip_tac >>
  `post.vs_params = (adopt_return_fmp ret (merge_callee_state caller callee)).vs_params` by
    metis_tac[] >>
  `post'.vs_params = (adopt_return_fmp ret' (merge_callee_state caller' callee')).vs_params` by
    metis_tac[] >>
  Cases_on `ret.iret_adopt_fmp` >> Cases_on `ret'.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem layout_return_taint_order:
  relocation_taint_le R tn un /\
  relocation_taint_le R0 caller_tn caller_un /\
  demand_taint next tn.t_mem un.t_mem ==>
  relocation_taint_le next
    (tn with t_var := DRESTRICT caller_tn.t_var (COMPL (set outs)))
    (un with t_var := DRESTRICT caller_un.t_var (COMPL (set outs)))
Proof
  simp[relocation_taint_le_def, demand_taint_def, op_taint_def,
       FLOOKUP_DRESTRICT] >> strip_tac >> conj_tac
  >- metis_tac[] >>
  gen_tac >> Cases_on `MEM v outs` >> simp[] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

Theorem layout_ret_endpoint_taint_demand:
  layout_ret_endpoint D lo vs0 C C' q0 es qs q g s t ret ret' /\
  vs0.vs_allocas = FEMPTY /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginResume fuel fn inst s ret s post) /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  inst.inst_opcode = RET ==>
  demand_taint
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC g.lop_cursor))
    tn.t_mem g.lop_target_taint.t_mem
Proof
  simp[layout_ret_endpoint_def] >> rpt strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    metis_tac[layout_ordinary_ready] >>
  gvs[layout_ordinary_trace_def, layout_ordinary_state_def,
      relocation_taint_le_def, demand_taint_def] >>
  rpt strip_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  irule joint_relocation_demand_retained >>
  goal_assum (drule_at Any) >>
  simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def,
       range_bytes_def] >> metis_tac[]
QED

Theorem layout_saved_caller_parameters:
  layout_saved_caller D lo C' q0 es qs a caller caller' /\
  a.lop_config = JointConfig stk PG G tn fn inst caller oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post /\
  bind_outputs outs' ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' ==>
  parameter_roots (\i x y. clean_resolved_root
    (activation_lookup (0:num) (concretize_positions C')
      (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
    (resolved_parameter_entry rp i) x y) post.vs_params post'.vs_params
Proof
  strip_tac >> irule layout_return_parameters >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  gvs[layout_saved_caller_def, layout_ordinary_state_def]
QED

Theorem layout_saved_caller_values:
  layout_saved_caller D lo C' q0 es qs a caller caller' /\
  a.lop_config = JointConfig stk PG G caller_tn fn call caller oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  layout_ret_endpoint D lo vs0 C C' q0 es qs q b sc tc ret ret' /\
  vs0.vs_allocas = FEMPTY /\ b.lop_cursor < LENGTH es /\
  EL b.lop_cursor es = SOME (OriginResume fuel callee inst sc ret sc post) /\
  b.lop_config = JointConfig cstk cPG cG tn callee inst sc coms com chs ch /\
  inst.inst_opcode = RET /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post /\
  bind_outputs outs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' ==>
  local_rel (\v. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
      (DRESTRICT rv (COMPL (set outs))))
    (guarded_bytes (retpc_var fn) (DRESTRICT rv (COMPL (set outs)))
      (tn with t_var := DRESTRICT caller_tn.t_var (COMPL (set outs))))
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC b.lop_cursor))
    concretize_local_obs post post'
Proof
  strip_tac >>
  `local_rel (\v. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv caller_tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs a.lop_cursor)
    concretize_local_obs caller caller'` by
      gvs[layout_saved_caller_def, layout_ordinary_state_def] >>
  `variable_domains caller caller' /\
   local_values (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
     (guarded_bytes (retpc_var fn) rv caller_tn) caller caller' /\
   concretize_local_obs caller caller'` by
      fs[frameRelocationLocalTheory.local_rel_def] >>
  drule_all layout_ret_endpoint_restore >> strip_tac >>
  `post'' = post'` by metis_tac[optionTheory.SOME_11] >> gvs[]
QED

Theorem layout_saved_caller_state:
  layout_saved_caller D lo C' q0 es qs a caller caller' /\
  a.lop_config = JointConfig stk PG G caller_tn fn call caller oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  layout_ret_endpoint D lo vs0 C C' q0 es qs q b sc tc ret ret' /\
  vs0.vs_allocas = FEMPTY /\ b.lop_cursor < LENGTH es /\
  EL b.lop_cursor es = SOME (OriginResume fuel callee inst sc ret sc post) /\
  b.lop_config = JointConfig cstk cPG cG tn callee inst sc coms com chs ch /\
  inst.inst_opcode = RET /\ caller.vs_call_ctx.cc_address = sc.vs_call_ctx.cc_address /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post /\
  bind_outputs outs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' ==>
  layout_ordinary_state D lo C' q0 es qs
    (a with <| lop_pending := F; lop_cursor := SUC b.lop_cursor;
       lop_config := JointConfig stk PG' G'
         (tn with t_var := DRESTRICT caller_tn.t_var (COMPL (set outs)))
         fn next post oms' om' hs' h';
       lop_anns := (rp,DRESTRICT rv (COMPL (set outs)))::anns;
       lop_target_taint := b.lop_target_taint with
         t_var := DRESTRICT a.lop_target_taint.t_var (COMPL (set outs)) |>)
    post post'
Proof
  strip_tac >>
  drule_all layout_saved_caller_values >> strip_tac >>
  drule_all layout_saved_caller_parameters >> strip_tac >>
  `relocation_env caller caller' /\ relocation_reader_context caller caller'` by
    gvs[layout_saved_caller_def, layout_ordinary_state_def] >>
  drule_all layout_ret_endpoint_restore_supplement >> strip_tac >>
  drule_all layout_ret_endpoint_taint_demand >> strip_tac >>
  `ret.iret_adopt_fmp = NONE /\ ret'.iret_adopt_fmp = NONE` by
    fs[layout_ret_endpoint_def] >>
  `post = (merge_callee_state caller sc) with vs_vars := post.vs_vars /\
   post' = (merge_callee_state caller' tc) with vs_vars := post'.vs_vars` by
    metis_tac[layout_return_bind_fields] >>
  simp[layout_ordinary_state_def, layout_phase_normalize_def] >>
  conj_tac
  >- (irule layout_return_taint_order >>
      goal_assum (drule_at Any) >>
      conj_tac
      >- (gvs[layout_ret_endpoint_def, layout_ordinary_entry_def,
              layout_ordinary_state_def] >> metis_tac[]) >>
      gvs[layout_saved_caller_def, layout_ordinary_state_def] >> metis_tac[]) >>
  qpat_x_assum `layout_saved_caller _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_saved_caller_def, layout_ordinary_state_def] >> strip_tac >>
  qpat_assum `post = _` (once_rewrite_tac o single) >>
  qpat_assum `post' = _` (once_rewrite_tac o single) >>
  simp[merge_callee_state_def]
QED

val _ = export_theory();
