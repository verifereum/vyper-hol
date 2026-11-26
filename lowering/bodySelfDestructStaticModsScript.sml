(* Linked static SelfDestruct outcome: a static-context write aborts without
   manufacturing a normal post.  The caller supplies the already-composed
   path from the successful operand landing to the deterministic abort. *)
Theory bodySelfDestructStaticMods
Ancestors
  gasOutcomeFullMods gasOutcomeFullPostMods gasExemptCertMods
  selfdestructHalt vyperInterpreter vyperState vyperAST
  bodyFullPostsMods bodySimFull gasShadow compileEnv
Theorem selfdestruct_static_outcome_mods:
  !DF lo explicit ctx func PG mods cx st0
    source es s G tn Q R res ee r G' tn'.
    ~s.vs_halted /\
    (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
    exit_result r /\
    create_size_exit_ok ctx res r /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (r,G',tn') /\
       R H res (ee with gas_obs := []) (G',tn') r) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      source (es,s,G,tn) Q R
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_mods_exit >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G'`,`ee`,`r`,`res`,`tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> strip_tac >>
  first_x_assum (qspec_then `H` mp_tac) >> simp[]
QED
