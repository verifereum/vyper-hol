Theory frameRelocationScalarSteps
Ancestors frameRelocationGuardedValues frameRelocationGhostCopy
  frameRelocationLocal frameRelocationValues frameOriginUpdates
  venomExecSemantics ptrDiscipline finite_map

Theorem guarded_equal_write:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  (!a b x. Obs a b ==> Obs (update_var v x a) (update_var v x b)) ==>
  local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
    (guarded_bytes Opaque (origin_set rv [v] NONE)
      (tn with t_var := tn.t_var |+ (v,{}))) R Obs
    (update_var v z s) (update_var v z t)
Proof
  strip_tac >> irule local_rel_update_observation_invariant >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
       origin_set_lookup, op_taint_def, FLOOKUP_UPDATE, word_agree_except_def] >>
  qexistsl_tac [`guarded_bytes Opaque rv tn`, `\u. F`, `guarded_ptr Opaque L rv`] >>
  simp[guarded_ptr_other, guarded_bytes_other] >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
       origin_set_lookup, op_taint_def, FLOOKUP_UPDATE, word_agree_except_def]
QED

Theorem guarded_purebinary:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [v] /\
  s.vs_labels = t.vs_labels /\
  (!w. a = Var w \/ b = Var w ==> clean_scalar Opaque rv tn w) /\
  (!s t v x. Obs s t ==> Obs (update_var v x s) (update_var v x t)) /\
  exec_pure2 f inst s = OK s' ==>
  ?x y. eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
    eval_operand a t = SOME x /\ eval_operand b t = SOME y /\
    s' = update_var v (f x y) s /\
    exec_pure2 f inst t = OK (update_var v (f x y) t) /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE)
        (tn with t_var := tn.t_var |+ (v,{}))) R Obs
      s' (update_var v (f x y) t)
Proof
  strip_tac >>
  `eval_operand a s = eval_operand a t` by
    (irule guarded_scalar_operand >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand b s = eval_operand b t` by
    (irule guarded_scalar_operand >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  irule guarded_equal_write >> goal_assum (drule_at Any) >> simp[]
QED
