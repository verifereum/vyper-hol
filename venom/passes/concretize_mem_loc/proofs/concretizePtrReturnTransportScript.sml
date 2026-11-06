Theory concretizePtrReturnTransport
Ancestors
  concretizePtrOpaqueRetpc concretizePtrValueTransport
  ptrDiscipline venomExecSemantics venomState list rich_list option

Theorem ptr_mixed_scalar_operands_equal:
  !ops. ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE /\
    op_taint tn op = {}) ops ==>
  eval_operands ops s = eval_operands ops t
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s = eval_operand h t` by
    (drule_all ptr_mixed_vars_eval >>
     Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >>
     simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  first_x_assum drule >> simp[]
QED

Theorem ptr_mixed_return_front:
  !ops. ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE /\
    op_taint tn op = {}) ops /\
  eval_operands (ops ++ [last]) t = SOME ys ==>
  ?xs. eval_operands (ops ++ [last]) s = SOME xs /\
    xs <> [] /\ ys <> [] /\ FRONT xs = FRONT ys
Proof
  gen_tac >> qid_spec_tac `ys` >> qid_spec_tac `ops` >>
  Induct >> simp[eval_operands_def, AllCaseEqs()] >> rpt strip_tac
  >- (drule_all ptr_mixed_vars_eval_presence >>
      disch_then (qspec_then `last` mp_tac) >>
      Cases_on `eval_operand last s` >> gvs[] >> qexists_tac `[x]` >> simp[]) >>
  `eval_operand h s = eval_operand h t` by
    (drule_all ptr_mixed_vars_eval >>
     Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >>
     simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `v::xs` >> gvs[] >>
  Cases_on `xs` >> Cases_on `vs` >> gvs[]
QED
