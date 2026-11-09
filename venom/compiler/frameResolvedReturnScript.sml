Theory frameResolvedReturn
Ancestors frameResolvedTrace frameJointTransition frameOriginCache venomExecSemantics finite_map list pred_set

(* Expose the exact saved annotation, not an unrelated existential witness. *)
Theorem resolved_config_return_exact:
  joint_transition C p (SOME (OriginResume fuel fn inst s ret send post)) q' /\
  resolved_config_ok p (fresh::birth::ids) (callee_ann::(rp,rv)::anns) /\
  p = JointConfig (f::stk) PG G tn fn inst s
    (caller_om::oms) om (caller_h::hs) h ==>
  resolved_config_ok q' (birth::ids)
    ((rp,DRESTRICT rv (COMPL (set f.cf_inst.inst_outputs)))::anns)
Proof
  rewrite_tac[joint_transition_return] >> rpt strip_tac >> gvs[] >>
  gvs[resolved_config_ok_def, resolved_stack_ok_def] >>
  `post.vs_allocas = f.cf_state.vs_allocas` by
    (drule return_bind_cache >> simp[]) >>
  simp[] >> metis_tac[resolved_frame_restrict]
QED

val _ = export_theory();
