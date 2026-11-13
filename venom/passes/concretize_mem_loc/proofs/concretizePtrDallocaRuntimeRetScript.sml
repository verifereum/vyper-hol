Theory concretizePtrDallocaRuntimeRet
Ancestors
  concretizePtrDallocaGhostInterface dftGasInvCallPartner lowerDloadPtrReturn
  venomExecSemantics venomState venomInst ptrDiscipline finite_map pred_set list

Theorem ptr_dalloca_runtime_restrict:
  ptr_dalloca_ghost_vars G V s Gt Vt t /\
  (!v site. FLOOKUP Gt v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  (!v. v IN A ==> lookup_var v s1 = lookup_var v s /\
                   lookup_var v t1 = lookup_var v t) ==>
  ptr_dalloca_ghost_vars (DRESTRICT G A) (DRESTRICT V A) s1
    (DRESTRICT Gt A) (DRESTRICT Vt A) t1 /\
  (!v site. FLOOKUP (DRESTRICT Gt A) v = SOME site ==>
     FLOOKUP (DRESTRICT TG A) v = NONE) /\
  (!v site. FLOOKUP (DRESTRICT TG A) v = NONE /\
     FLOOKUP (DRESTRICT G A) v = SOME site ==>
     FLOOKUP (DRESTRICT Gt A) v = SOME site)
Proof
  simp[ptr_dalloca_ghost_vars_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  strip_tac >> rpt conj_tac >> rpt gen_tac >>
  Cases_on `v IN A` >> gvs[] >> metis_tac[]
QED

Theorem ptr_dalloca_return_lookup:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state s e)) =
    SOME s1 /\ ~MEM v outs ==>
  lookup_var v (s1 with vs_inst_idx := n) = lookup_var v s
Proof
  strip_tac >> drule_all inv_bind_outputs_lookup_outside >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[lookup_var_def, adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem ptr_dalloca_return_params:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state s e)) =
    SOME s1 ==> s1.vs_params = s.vs_params
Proof
  strip_tac >> drule dload_bind_outputs_frame >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem ptr_dalloca_runtime_ret:
  ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
    ft.cf_prov ft.cf_tvar ft.cf_state /\
  (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
     FLOOKUP ft.cf_prov v = SOME site) /\
  f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state e)) = SOME s1 /\
  bind_outputs ft.cf_inst.inst_outputs rett.iret_values
    (adopt_return_fmp rett (merge_callee_state ft.cf_state et)) = SOME t1 ==>
  ptr_dalloca_ghost_vars
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    (DRESTRICT ft.cf_prov (COMPL (set ft.cf_inst.inst_outputs)))
    (DRESTRICT ft.cf_tvar (COMPL (set ft.cf_inst.inst_outputs)))
    (t1 with vs_inst_idx := SUC ft.cf_state.vs_inst_idx) /\
  (!v site.
    FLOOKUP (DRESTRICT ft.cf_prov (COMPL (set ft.cf_inst.inst_outputs))) v =
      SOME site ==>
    FLOOKUP (DRESTRICT TG (COMPL (set f.cf_inst.inst_outputs))) v = NONE) /\
  (!v site.
    FLOOKUP (DRESTRICT TG (COMPL (set f.cf_inst.inst_outputs))) v = NONE /\
    FLOOKUP (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs))) v =
      SOME site ==>
    FLOOKUP (DRESTRICT ft.cf_prov (COMPL (set ft.cf_inst.inst_outputs))) v =
      SOME site)
Proof
  strip_tac >> gvs[] >> irule ptr_dalloca_runtime_restrict >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`f.cf_state`, `ft.cf_state`] >> simp[] >> rpt strip_tac >>
  irule ptr_dalloca_return_lookup >> simp[] >> metis_tac[]
QED

Theorem ptr_dalloca_runtime_ret_params:
  LENGTH PT = LENGTH f.cf_params /\
  LENGTH f.cf_params = LENGTH ft.cf_params /\
  LENGTH f.cf_state.vs_params = LENGTH f.cf_params /\
  LENGTH ft.cf_state.vs_params = LENGTH ft.cf_params /\
  (!k site. k < LENGTH f.cf_params ==>
    (EL k ft.cf_params = SOME site ==>
      EL k f.cf_params = SOME site /\ EL k PT = NONE /\
      EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
    (EL k PT = NONE /\ EL k f.cf_params = SOME site ==>
      EL k ft.cf_params = SOME site)) /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state e)) = SOME s1 /\
  bind_outputs ft.cf_inst.inst_outputs rett.iret_values
    (adopt_return_fmp rett (merge_callee_state ft.cf_state et)) = SOME t1 ==>
  LENGTH PT = LENGTH f.cf_params /\
  LENGTH f.cf_params = LENGTH ft.cf_params /\
  LENGTH (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx).vs_params =
    LENGTH f.cf_params /\
  LENGTH (t1 with vs_inst_idx := SUC ft.cf_state.vs_inst_idx).vs_params =
    LENGTH ft.cf_params /\
  (!k site. k < LENGTH f.cf_params ==>
    (EL k ft.cf_params = SOME site ==>
      EL k f.cf_params = SOME site /\ EL k PT = NONE /\
      EL k (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx).vs_params =
      EL k (t1 with vs_inst_idx := SUC ft.cf_state.vs_inst_idx).vs_params) /\
    (EL k PT = NONE /\ EL k f.cf_params = SOME site ==>
      EL k ft.cf_params = SOME site))
Proof
  strip_tac >>
  `s1.vs_params = f.cf_state.vs_params` by
    metis_tac[ptr_dalloca_return_params] >>
  `t1.vs_params = ft.cf_state.vs_params` by
    metis_tac[ptr_dalloca_return_params] >>
  simp[]
QED
