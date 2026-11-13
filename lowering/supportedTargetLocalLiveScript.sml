Theory supportedTargetLocalLive
Ancestors
  bodyPtrPopTargetDefs bodySimAugPlaceLive bodySimAugPlaceScopes
  supportedTargets vyperInterpreter vyperState

Theorem supported_target_local_live:
  !t tops bindings info cx id.
    supported_target_info tops bindings t = SOME info ==>
    local_target_live cx id t
Proof
  `(!e:expr. T) /\
   !t tops bindings info cx id.
     supported_target_info tops bindings t = SOME info ==>
     local_target_live cx id t` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[local_target_live_def] >> rpt strip_tac >>
  gvs[supported_target_info_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  imp_res_tac aug_place_supported_expr_scopes >>
  drule_all aug_place_base_memory_live >> strip_tac >>
  gvs[]
QED
