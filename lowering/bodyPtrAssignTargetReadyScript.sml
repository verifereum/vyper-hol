(* Supported assignment targets supply the local-liveness side condition
   of the existing pointer target simulation. *)
Theory bodyPtrAssignTargetReady
Ancestors
  bodyPtrPopSeamTargetSim supportedTargetLocalLive bodyPtrPopTargetDefs
  bodyPtrPreds bodySim targetPlaceSim supportedStmts supportedTargets

Theorem legacy_assignment_target_live[local]:
  supported_target tops bindings t /\ target_root t = NameTarget id ==>
  local_target_live cx id t
Proof
  Cases_on `t` >>
  simp[supported_target_def, target_root_def, local_target_live_def] >>
  Cases_on `b` >> simp[target_root_def]
QED

Theorem body_assign_target_ready_ptr:
  !t tops bindings ctx cenv cx env es d PG func e.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    body_base_target_ptr_ok cx t /\ target_pre cenv cx env t es ==>
    target_sim_ptr d ctx PG func cenv cx env t es
Proof
  rpt gen_tac >> strip_tac >>
  `!id. target_root t = NameTarget id ==> local_target_live cx id t` by
    (`supported_target tops bindings t \/
      ?info. supported_target_info tops bindings t = SOME info` by
       (fs[supported_stmt_def, supported_assignment_def] >>
        Cases_on `supported_target_info tops bindings t` >> gvs[AllCaseEqs()])
     >- metis_tac[legacy_assignment_target_live] >>
     metis_tac[supported_target_local_live]) >>
  match_mp_tac (Q.SPECL [`t`,`tops`,`ctx`,`cenv`,`cx`,`env`,`es`,`d`,`PG`,`func`]
    body_target_sim_ptr) >> simp[]
QED
