Theory concretizeLayoutArgumentRoots
Ancestors concretizeLayoutParameterRoots frameRelocationGuardedValues
  frameRelocationLocal frameRelocationValues frameRelocationOpaque venomState list

Definition argument_value_def:
  argument_value Opaque L rv tn op x y <=>
    case op of
      Var v => guarded_ptr Opaque L rv v x y /\
               guarded_bytes Opaque rv tn v x y
    | _ => x = y
End

Theorem argument_operand_value:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) Rmem Obs s t /\
  s.vs_labels = t.vs_labels /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ argument_value Opaque L rv tn op x y
Proof
  Cases_on `op` >> simp[eval_operand_def, argument_value_def] >>
  rpt strip_tac >>
  fs[local_rel_def, variable_domains_def, local_values_def] >>
  metis_tac[optionTheory.option_CASES, optionTheory.NOT_SOME_NONE]
QED

Theorem argument_roots_evaluation:
  !ops args.
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) Rmem Obs s t /\
  s.vs_labels = t.vs_labels /\ eval_operands ops s = SOME args ==>
  ?args'. eval_operands ops t = SOME args' /\ LENGTH args = LENGTH ops /\
    parameter_roots (\i x y. argument_value Opaque L rv tn (EL i ops) x y)
      args args'
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >> strip_tac
  >- simp[parameter_roots_def] >>
  gvs[AllCaseEqs()] >>
  drule_all argument_operand_value >> strip_tac >>
  qexists_tac `y::args'` >>
  simp[eval_operands_def, parameter_roots_def] >>
  fs[parameter_roots_def] >>
  Cases >> simp[]
QED

Theorem argument_roots_setup:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) Rmem Obs s t /\
  s.vs_labels = t.vs_labels /\ eval_operands ops s = SOME args /\
  setup_callee fn args s = SOME sc /\ ~NULL gn.fn_blocks ==>
  ?args' tc. eval_operands ops t = SOME args' /\
    setup_callee gn args' t = SOME tc /\
    parameter_roots (\i x y. argument_value Opaque L rv tn (EL i ops) x y)
      sc.vs_params tc.vs_params
Proof
  rpt strip_tac >> drule_all argument_roots_evaluation >> strip_tac >>
  drule_all parameter_roots_setup_callee >> strip_tac >> metis_tac[]
QED

Theorem argument_value_nonopaque:
  ~Opaque v /\ argument_value Opaque L rv tn (Var v) x y ==>
  copy_ptr L rv v x y /\ copy_bytes rv tn v x y
Proof
  simp[argument_value_def, guarded_ptr_def, guarded_bytes_def]
QED

Theorem argument_value_clean_scalar:
  clean_scalar Opaque rv tn v /\
  argument_value Opaque L rv tn (Var v) x y ==> x = y
Proof
  simp[argument_value_def, clean_scalar_def, guarded_bytes_def,
       frameRelocationGhostCopyTheory.copy_bytes_def] >>
  metis_tac[word_agree_except_empty]
QED
