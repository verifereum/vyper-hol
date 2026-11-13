Theory lowerDloadPtrReturn
Ancestors lowerDloadPtrJointNext lowerDloadPtrBlockEntry lowerDloadPtrAlloc lowerDloadPtrCall lowerDloadPtrInvoke lowerDloadPtrAggregate lowerDloadPtrRel
  lowerDloadPtrPhi ptrDiscipline venomExecSemantics venomState venomInst
  memLocDefs pointerConfinedDefs finite_map list rich_list pred_set

Theorem dload_ret_operand_clean:
  i.inst_opcode = RET /\ ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  taint_ok fn tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
    mem_read_ops_def, mem_write_ops_def, taint_ok_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem eval_operands_front_backwards:
  !ops ys.
    ops <> [] /\ eval_operands ops t = SOME ys /\
    (!op. MEM op (FRONT ops) ==> eval_operand op s = eval_operand op t) /\
    (!op. MEM op ops ==> (eval_operand op s = NONE <=> eval_operand op t = NONE)) ==>
    ?xs. eval_operands ops s = SOME xs /\ xs <> [] /\ FRONT xs = FRONT ys
Proof
  Induct_on `ops` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ops`
  >- (gvs[eval_operands_def, AllCaseEqs()] >>
      Cases_on `eval_operand h s` >> gvs[] >>
      qexists_tac `[x]` >> simp[]) >>
  gvs[eval_operands_def, AllCaseEqs(), FRONT_DEF]
QED

Theorem dload_ret_backwards:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = RET /\ ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  taint_ok fn tn i s /\
  (!a. MEM (Var a) (FRONT i.inst_operands) ==> a IN V) /\
  (!a. MEM (Var a) i.inst_operands ==>
    (lookup_var a s = NONE <=> lookup_var a t = NONE)) /\
  step_inst fuel Ct i t = IntRet rt t_end ==>
  ?rs s_end. step_inst fuel Cs i s = IntRet rs s_end /\
    rs.iret_values = rt.iret_values /\ rs.iret_adopt_fmp = NONE /\
    rt.iret_adopt_fmp = NONE /\ s_end = s /\ t_end = t
Proof
  rpt strip_tac >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `s.vs_labels = t.vs_labels` by
    metis_tac[dload_boundary_environment, dload_equal_environment_code] >>
  `!op. MEM op i.inst_operands ==>
     (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule eval_operand_definedness >> metis_tac[]) >>
  `i.inst_operands <> []` by
    (strip_tac >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operands_def]) >>
  `!op. MEM op (FRONT i.inst_operands) ==>
     eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `MEM op i.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
     drule_all dload_ret_operand_clean >> strip_tac >>
     irule scalar_operand_equal >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule_all eval_operands_front_backwards >> strip_tac >>
  qexists_tac `<|iret_values := FRONT xs; iret_adopt_fmp := NONE|>` >>
  Cases_on `xs` >> gvs[]
QED

Theorem dload_fold_outputs_vars:
  !pairs G H tv uv s t.
    dload_vars_match fs V G H (tn with t_var := tv) (un with t_var := uv) s t ==>
    dload_vars_match fs V
      (DRESTRICT G (COMPL (set (MAP FST pairs))))
      (DRESTRICT H (COMPL (set (MAP FST pairs))))
      (tn with t_var := DRESTRICT tv (COMPL (set (MAP FST pairs))))
      (un with t_var := DRESTRICT uv (COMPL (set (MAP FST pairs))))
      (FOLDL (\st (v,x). update_var v x st) s pairs)
      (FOLDL (\st (v,x). update_var v x st) t pairs)
Proof
  Induct >- simp[DRESTRICT_UNIV] >> simp[] >> gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  first_x_assum (qspecl_then
    [`set_prov G [h0] NONE`, `set_prov H [h0] NONE`,
     `set_var_taint tv [h0] {}`, `set_var_taint uv [h0] {}`,
     `update_var h0 h1 s`, `update_var h0 h1 t`] mp_tac) >>
  impl_tac
  >- (irule dload_vars_match_write >>
      simp[dload_value_word_def, word_agree_except_def]) >>
  simp[set_prov_def, set_var_taint_def, dload_vars_match_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  disch_tac >> gen_tac >> disch_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  Cases_on `MEM h0 (MAP FST pairs)` >> Cases_on `v = h0` >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem dload_bind_outputs_vars:
  dload_vars_match fs V G H (tn with t_var := tv) (un with t_var := uv) s t /\
  bind_outputs outs vals t = SOME t' ==>
  ?s'. bind_outputs outs vals s = SOME s' /\
    dload_vars_match fs V
      (DRESTRICT G (COMPL (set outs))) (DRESTRICT H (COMPL (set outs)))
      (tn with t_var := DRESTRICT tv (COMPL (set outs)))
      (un with t_var := DRESTRICT uv (COMPL (set outs))) s' t'
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  drule dload_fold_outputs_vars >>
  disch_then (qspec_then `ZIP (outs,vals)` mp_tac) >>
  simp[MAP_ZIP]
QED

Theorem dload_memory_return_merge:
  dload_memory_match lo (e::fs) tn un s t ==>
  dload_memory_match lo fs tn un
    (merge_callee_state c s) (merge_callee_state d t)
Proof
  simp[dload_memory_match_def, merge_callee_state_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`SUC owner`,`id`,`b`,`c'`,`n`,`k`] mp_tac) >>
  gvs[dload_live_site_def]
QED

Theorem dload_return_merge_boundary:
  dload_boundary_core lo (e::f::fs) V (Vc::Ws) PG PH G H tn un s t (c::cs) (d::ds) /\
  dload_equal_environment c.cf_state d.cf_state /\
  c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  (!k. k < LENGTH (c::cs) ==> dload_live_layout lo
    (EL k (c::cs)).cf_state.vs_alloca_next
    (EL k (d::ds)).cf_state.vs_alloca_next (DROP (SUC k) (e::f::fs))) ==>
  dload_boundary_core lo (f::fs) Vc Ws c.cf_params d.cf_params c.cf_prov d.cf_prov
    (tn with t_var := c.cf_tvar) (un with t_var := d.cf_tvar)
    (merge_callee_state c.cf_state s) (merge_callee_state d.cf_state t) cs ds
Proof
  strip_tac >>
  `dload_saved_metadata (f::fs) Vc c d` by
    (drule dload_boundary_saved >> disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `dload_memory_match lo (f::fs) tn un
     (merge_callee_state c.cf_state s) (merge_callee_state d.cf_state t)` by
    (irule dload_memory_return_merge >> metis_tac[dload_boundary_memory]) >>
  `dload_shared_store tn un
     (merge_callee_state c.cf_state s) (merge_callee_state d.cf_state t)` by
    (irule dload_shared_store_merge >> metis_tac[dload_boundary_shared_store]) >>
  `dload_equal_environment
     (merge_callee_state c.cf_state s) (merge_callee_state d.cf_state t)` by
    (irule dload_equal_environment_merge >> metis_tac[dload_boundary_environment]) >>
  `dload_table_stack (f::fs)
     (merge_callee_state c.cf_state s :: MAP (\c. c.cf_state) cs)
     (merge_callee_state d.cf_state t :: MAP (\d. d.cf_state) ds)` by
    (irule dload_table_return_pop >> metis_tac[dload_boundary_tables, MAP]) >>
  `dload_live_layout lo
    (merge_callee_state c.cf_state s).vs_alloca_next
    (merge_callee_state d.cf_state t).vs_alloca_next (f::fs)` by
    (irule dload_saved_layout_restore >>
     qexistsl [`cs`,`ds`] >> gvs[dload_boundary_core_def]) >>
  `dload_vars_match (f::fs) Vc c.cf_prov d.cf_prov
    (tn with t_var := c.cf_tvar) (un with t_var := d.cf_tvar)
    (merge_callee_state c.cf_state s) (merge_callee_state d.cf_state t)` by
    (gvs[dload_saved_metadata_def, dload_vars_match_def, op_taint_def,
         lookup_var_def, merge_callee_state_def] >> metis_tac[]) >>
  `dload_memory_match lo (f::fs)
    (tn with t_var := c.cf_tvar) (un with t_var := d.cf_tvar)
    (merge_callee_state c.cf_state s) (merge_callee_state d.cf_state t)` by
    (gvs[dload_memory_match_def] >> metis_tac[]) >>
  `dload_shared_store (tn with t_var := c.cf_tvar) (un with t_var := d.cf_tvar)
    (merge_callee_state c.cf_state s) (merge_callee_state d.cf_state t)` by
    gvs[dload_shared_store_def] >>
  gvs[dload_boundary_core_def, dload_saved_metadata_def,
      dload_merge_local_metadata] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!k. k < SUC _ ==> dload_vars_match _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `SUC k` mp_tac) >> simp[]
QED

Theorem dload_fold_outputs_frame:
  !pairs s.
    FOLDL (\st (v,x). update_var v x st) s pairs =
    s with vs_vars := (FOLDL (\st (v,x). update_var v x st) s pairs).vs_vars
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >> gen_tac >>
  first_x_assum (qspec_then `update_var h0 h1 s` mp_tac) >>
  simp[update_var_def, venom_state_component_equality]
QED

Theorem dload_bind_outputs_frame:
  bind_outputs outs vals s = SOME u ==> u = s with vs_vars := u.vs_vars
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  MATCH_ACCEPT_TAC dload_fold_outputs_frame
QED

Theorem dload_boundary_bind_outputs:
  dload_boundary_core lo fs V Ws PG PH G H
    (tn with t_var := tv) (un with t_var := uv) s t cs ds /\
  bind_outputs outs vals t = SOME t' ==>
  ?s'. bind_outputs outs vals s = SOME s' /\
    dload_boundary_core lo fs V Ws PG PH
      (DRESTRICT G (COMPL (set outs))) (DRESTRICT H (COMPL (set outs)))
      (tn with t_var := DRESTRICT tv (COMPL (set outs)))
      (un with t_var := DRESTRICT uv (COMPL (set outs))) s' t' cs ds
Proof
  strip_tac >>
  `dload_vars_match fs V G H (tn with t_var := tv) (un with t_var := uv) s t` by
    metis_tac[dload_boundary_vars] >>
  drule_all dload_bind_outputs_vars >> strip_tac >> qexists_tac `s'` >> simp[] >>
  qpat_assum `bind_outputs _ _ s = _` (mp_tac o MATCH_MP dload_bind_outputs_frame) >>
  disch_then (fn th => assume_tac th >> SUBST1_TAC th) >>
  qpat_assum `bind_outputs _ _ t = _` (mp_tac o MATCH_MP dload_bind_outputs_frame) >>
  disch_then (fn th => assume_tac th >> SUBST1_TAC th) >>
  irule (SRULE [] (Q.INST [`si` |-> `s.vs_inst_idx`, `ti` |-> `t.vs_inst_idx`,
    `tn` |-> `tn with t_var := tv`, `un` |-> `un with t_var := uv`]
    (Q.INST [`tv` |-> `tv_new`, `uv` |-> `uv_new`]
      dload_boundary_core_var_index_update))) >>
  simp[] >> metis_tac[]
QED

Theorem dload_return_pop_boundary:
  dload_boundary_core lo (e::f::fs) V (Vc::Ws) PG PH G H tn un s t (c::cs) (d::ds) /\
  dload_equal_environment c.cf_state d.cf_state /\
  c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  (!k. k < LENGTH (c::cs) ==> dload_live_layout lo
    (EL k (c::cs)).cf_state.vs_alloca_next
    (EL k (d::ds)).cf_state.vs_alloca_next (DROP (SUC k) (e::f::fs))) /\
  c.cf_inst.inst_outputs = d.cf_inst.inst_outputs /\
  bind_outputs d.cf_inst.inst_outputs vals (merge_callee_state d.cf_state t) = SOME t' ==>
  ?s'. bind_outputs c.cf_inst.inst_outputs vals (merge_callee_state c.cf_state s) = SOME s' /\
    dload_boundary_core lo (f::fs) Vc Ws c.cf_params d.cf_params
      (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (DRESTRICT d.cf_prov (COMPL (set d.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs)))
      (un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs))) s' t' cs ds
Proof
  strip_tac >> drule_all dload_return_merge_boundary >> strip_tac >>
  drule dload_boundary_bind_outputs >> simp[] >>
  disch_then drule >> gvs[]
QED

Theorem dload_fold_outputs_definedness:
  !pairs s t.
    (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
    !v. v IN U ==>
      (lookup_var v (FOLDL (\st (a,x). update_var a x st) s pairs) = NONE <=>
       lookup_var v (FOLDL (\st (a,x). update_var a x st) t pairs) = NONE)
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> strip_tac >> simp[] >>
  first_x_assum (qspecl_then [`update_var h0 h1 s`,`update_var h0 h1 t`] mp_tac) >>
  impl_tac >- (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
               metis_tac[lookup_var_def]) >> simp[]
QED

Theorem dload_bind_outputs_definedness:
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  bind_outputs outs vals s = SOME s' /\ bind_outputs outs vals t = SOME t' ==>
  !v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  rpt strip_tac >> irule dload_fold_outputs_definedness >> qexists_tac `U` >> simp[]
QED

Theorem dload_return_control_reachable:
  frame_reachable vs0 C (c::cs) PG G tn fn ri s /\ active_inst fn ri s /\
  step_inst fuel C ri s = IntRet ret s /\ ret.iret_adopt_fmp = NONE /\
  bind_outputs c.cf_inst.inst_outputs ret.iret_values (merge_callee_state c.cf_state s) = SOME s' /\
  bind_outputs d.cf_inst.inst_outputs vals (merge_callee_state d.cf_state t) = SOME t' /\
  dload_control_match q c.cf_fn d.cf_fn c.cf_state d.cf_state c.cf_inst [c.cf_inst] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) d.cf_fn.fn_blocks) /\
  active_inst d.cf_fn j (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) ==>
  ?i emitted.
    dload_control_match q c.cf_fn d.cf_fn
      (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) i emitted 0 /\
    j = HD emitted /\
    frame_reachable vs0 C cs c.cf_params
      (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs)))
      c.cf_fn i (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  `s'.vs_current_bb = c.cf_state.vs_current_bb /\
   s'.vs_prev_bb = c.cf_state.vs_prev_bb /\
   s'.vs_inst_idx = c.cf_state.vs_inst_idx /\
   t'.vs_current_bb = d.cf_state.vs_current_bb /\
   t'.vs_prev_bb = d.cf_state.vs_prev_bb /\
   t'.vs_inst_idx = d.cf_state.vs_inst_idx` by
    (imp_res_tac dload_bind_outputs_frame >>
     gvs[venom_state_component_equality, merge_callee_state_def]) >>
  drule_all dload_control_singleton_next_fields >> strip_tac >>
  `active_inst c.cf_fn i' (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)` by
    metis_tac[dload_control_match_boundary] >>
  qexistsl [`i'`,`emitted'`] >> simp[] >>
  irule frame_reachable_ret >>
  qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `step_inst _ _ _ _ = _` (irule_at Any) >>
  simp[adopt_return_fmp_def]
QED

Theorem dload_actual_return:
  dload_boundary_core lo (e::f::fs) V (Vc::Ws) PG PH G H tn un s t (c::cs) (d::ds) /\
  frame_reachable vs0 C (c::cs) PG G tn fn ri s /\ active_inst fn ri s /\
  ri.inst_opcode = RET /\ ptr_use_ok P pv ri /\ FDOM G SUBSET pv /\ taint_ok fn tn ri s /\
  (!a. MEM (Var a) (FRONT ri.inst_operands) ==> a IN V) /\
  (!a. MEM (Var a) ri.inst_operands ==> (lookup_var a s = NONE <=> lookup_var a t = NONE)) /\
  step_inst fuel Ct ri t = IntRet rt t /\
  dload_equal_environment c.cf_state d.cf_state /\
  c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  (!k. k < LENGTH (c::cs) ==> dload_live_layout lo
    (EL k (c::cs)).cf_state.vs_alloca_next
    (EL k (d::ds)).cf_state.vs_alloca_next (DROP (SUC k) (e::f::fs))) /\
  c.cf_inst = d.cf_inst /\
  dload_control_match q c.cf_fn d.cf_fn c.cf_state d.cf_state c.cf_inst [c.cf_inst] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) d.cf_fn.fn_blocks) /\
  (!a. a IN U ==> (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
  bind_outputs d.cf_inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state d.cf_state t)) = SOME t' /\
  active_inst d.cf_fn j (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) ==>
  ?rs s' i emitted.
    step_inst fuel C ri s = IntRet rs s /\ rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    bind_outputs c.cf_inst.inst_outputs rs.iret_values
      (adopt_return_fmp rs (merge_callee_state c.cf_state s)) = SOME s' /\
    dload_boundary_core lo (f::fs) Vc Ws c.cf_params d.cf_params
      (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (DRESTRICT d.cf_prov (COMPL (set d.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs)))
      (un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs)))
      (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) cs ds /\
    dload_control_match q c.cf_fn d.cf_fn
      (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) i emitted 0 /\ j = HD emitted /\
    frame_reachable vs0 C cs c.cf_params
      (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs)))
      c.cf_fn i (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx) /\
    (!a. a IN U ==> (lookup_var a (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx) = NONE <=>
                     lookup_var a (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) = NONE)) /\
    (!k. k < LENGTH cs ==> dload_live_layout lo
      (EL k cs).cf_state.vs_alloca_next (EL k ds).cf_state.vs_alloca_next
      (DROP (SUC k) (f::fs)))
Proof
  strip_tac >>
  drule_all dload_ret_backwards >> disch_then (qspec_then `C` strip_assume_tac) >>
  gvs[adopt_return_fmp_def] >>
  drule dload_return_pop_boundary >> simp[] >> disch_then drule >> strip_tac >>
  drule dload_return_control_reachable >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `!vals t2 t3 q2 j2 d2. _` drule_all >> strip_tac >>
  qexistsl [`i`,`emitted`] >> simp[adopt_return_fmp_def] >>
  conj_tac >- (irule dload_boundary_core_index_update >> simp[]) >>
  conj_tac
  >- (`!a. a IN U ==> (lookup_var a (merge_callee_state c.cf_state s) = NONE <=>
                       lookup_var a (merge_callee_state d.cf_state t) = NONE)` by
        gvs[lookup_var_def, merge_callee_state_def] >>
      `!a. a IN U ==> (lookup_var a s' = NONE <=> lookup_var a t' = NONE)` by
        metis_tac[dload_bind_outputs_definedness] >>
      gvs[lookup_var_def]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!k. k < SUC _ ==> dload_live_layout _ _ _ _`
    (qspec_then `SUC k` mp_tac) >> simp[]
QED
