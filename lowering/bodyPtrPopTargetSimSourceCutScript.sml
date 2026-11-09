Theory bodyPtrPopTargetSimSourceCut
Ancestors
  bodyPtrPopTargetFactor vyperInterpreter vyperState

Theorem target_subscript_source_cut_ptr:
  eval_base_place cx bt es0 = (INL pv,em) /\
  vyperState$bind (eval_expr cx e) (read_result cx) em = (INL v,ef) /\
  extend_place cx pv (ValueSubscript v) ef = (rr,ee) ==>
  eval_base_place cx (SubscriptTarget bt e) es0 = (rr,ee)
Proof
  strip_tac >>
  qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all pop_target_subscript_cut >> simp[]
QED
