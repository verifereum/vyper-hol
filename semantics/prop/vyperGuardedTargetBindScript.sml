Theory vyperGuardedTargetBind
Ancestors
  vyperCallOutcomeFrame vyperInterpreter vyperState

(* The continuation preserves the observation when it holds before and
   after target evaluation. *)
Theorem state_rel_frame_eval_target_bind:
  state_rel_frame (\s t. P s ==> P t) (eval_target_place cx target) /\
  (!s pl t. eval_target_place cx target s = (INL pl,t) /\ P s /\ P t ==>
            state_rel_frame (\s t. P s ==> P t) (next pl)) ==>
  state_rel_frame (\s t. P s ==> P t) (bind (eval_target_place cx target) next)
Proof
  simp[state_rel_frame_result, bind_def] >> rpt strip_tac >>
  Cases_on `eval_target_place cx target s` >>
  rename1 `eval_target_place cx target s = (answer,mid)` >>
  Cases_on `answer` >> gvs[] >>
  qpat_assum `!st res st'. eval_target_place cx target st = _ ==> _`
    (drule_then drule) >> strip_tac
  >- (qpat_x_assum `!s pl t. eval_target_place _ _ _ = _ /\ _ ==> _`
        drule >> simp[] >> disch_then (drule_all_then ACCEPT_TAC)) >>
  first_assum ACCEPT_TAC
QED
