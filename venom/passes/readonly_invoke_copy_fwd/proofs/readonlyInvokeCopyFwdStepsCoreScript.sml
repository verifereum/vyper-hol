Theory readonlyInvokeCopyFwdStepsCore
Ancestors
  readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdMemory
  readonlyInvokeCopyFwdEffects readonlyInvokeCopyFwdRel
  taintAgree ptrDiscipline venomState venomExecSemantics
  internalReturnCopyFwdSim finite_map words list pred_set

(* Only ghost entry indices are recomputed here.  The inherited relocation
   map, actual saved callers, current copies and suspended copies stay fixed. *)
Theorem ricf_cert_bind:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_value_agree sites p m x y /\
  u = update_var out x s /\ v = update_var out y t /\
  H = set_prov G0 [out] p /\
  un = tn0 with t_var := set_var_taint tn0.t_var [out] m /\
  Hentry = (if u.vs_prev_bb = NONE then H else entry_prov fn u H) /\
  unentry = (if u.vs_prev_bb = NONE then un else entry_taint_vars fn u un) ==>
  ricf_cert_core D ids stk PG Hentry unentry fn
    sites maps targets H un cur curs u v
Proof
  strip_tac >> gvs[] >>
  fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
  simp[ricf_live_boundary_core_def, ircf_dead_def, update_var_def,
       ricf_complete_params_def] >>
  rpt conj_tac
  >- (drule_all ricf_frame_agree_update_var >>
      simp[update_var_def, ircf_dead_def, ricf_complete_params_def])
  >- gvs[ricf_live_stack_agree_def, merge_callee_state_def, update_var_def]
  >- (gvs[ircf_cross_def, update_var_def] >> metis_tac[]) 
  >> gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def, update_var_def]
  >> metis_tac[]
QED
