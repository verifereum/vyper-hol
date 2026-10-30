(* Local assignment places have a memory root, independently of effects
   incurred while evaluating their subscript expressions. *)
Theory vyperReadOnlyTargets
Ancestors
  vyperMachineFrame vyperCallOutcomeFrame vyperState vyperInterpreter vyperTypeContract
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem machine_frame_sequence:
  state_rel_frame machine_frame f /\ state_rel_frame machine_frame g ==>
  state_rel_frame machine_frame (ignore_bind f g)
Proof
  strip_tac >> simp[ignore_bind_def] >>
  match_mp_tac machine_frame_bind >> simp[]
QED

Theorem extend_place_memory_local:
  extend_place cx (PlaceR (MemoryPlace id path)) sb st = (INL r,st') ==>
  ?path'. r = PlaceR (MemoryPlace id path')
Proof
  simp[extend_place_def, bind_def, ignore_bind_def, extend_memory_place_def,
       return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem eval_base_place_local:
  !bt cx st r st'.
    ~toplevel_target bt /\
    eval_base_place cx bt st = (INL r,st') ==>
    ?id path. r = PlaceR (MemoryPlace id path)
Proof
  completeInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt strip_tac >>
  gvs[toplevel_target_def, Once evaluate_def, bind_def, get_scopes_def,
      type_check_def, assert_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  rename1 `eval_base_place cx inner _ = (INL pv,_)` >>
  first_x_assum (qspec_then `base_assignment_target_size inner` mp_tac) >>
  simp[] >> disch_then (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  drule extend_place_memory_local >> metis_tac[]
QED

Theorem eval_target_place_local:
  ~toplevel_target bt /\
  eval_target_place cx bt st = (INL p,st') ==>
  ?id path. p = MemoryPlace id path
Proof
  strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule_all eval_base_place_local >> strip_tac >>
  gvs[get_place_def, return_def]
QED

Theorem checked_eval_target_place_local:
  write_mutability_ok mods View bt /\
  eval_target_place cx bt st = (INL p,st') ==>
  ?id path. p = MemoryPlace id path
Proof
  strip_tac >> irule eval_target_place_local >>
  goal_assum (drule_at Any) >>
  gvs[write_mutability_ok_def, call_mutability_ok_def]
QED
