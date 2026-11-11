Theory lowerDloadCallParameters
Ancestors
  lowerDloadCallBoundaryTest lowerDloadSourceInterface lowerDloadPairedBoundary
  lowerDloadOperand lowerDloadDefs ptrDiscipline venomExecSemantics
  venomInst venomState list rich_list pred_set

Theorem ld_owned_clean_selection[local]:
  ld_owned_value E ps pt {} Mt x y ==>
  ld_owned_value E ps pt {} {} x y /\ ld_owned_selection E ps pt
Proof
  Cases_on `ps` >> simp[ld_owned_value_def, ld_mask_word_def,
    ld_owned_selection_def] >>
  PairCases_on `x'` >> simp[ld_owned_value_def, ld_owned_selection_def] >>
  metis_tac[]
QED

Theorem ld_clean_call_list[local]:
  !ops xs ys.
  eval_operands ops s = SOME xs /\ eval_operands ops t = SOME ys /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  LIST_REL (\(op,x) y. ld_owned_value E (ld_op_prov AG op)
    (ld_op_prov BH op) (op_taint tn op) (op_taint un op) x y)
    (ZIP (ops,xs)) ys ==>
  LENGTH ops = LENGTH xs /\ LENGTH ops = LENGTH ys /\
  (!q. q < LENGTH xs ==>
    ld_owned_value E (EL q (MAP (ld_op_prov AG) ops))
      (EL q (MAP (ld_op_prov BH) ops)) {} {} (EL q xs) (EL q ys)) /\
  LIST_REL (ld_owned_selection E)
    (MAP (ld_op_prov AG) ops) (MAP (ld_op_prov BH) ops)
Proof
  Induct >> simp[eval_operands_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all ld_owned_clean_selection >> strip_tac >>
  Cases_on `q` >> simp[]
QED

Theorem ld_call_parameters_backward:
  lower_dload_function_supply a source = (callee,b) /\
  opaque_use_ok caller /\ MEM ci (fn_insts caller) /\
  ci.inst_opcode = INVOKE /\ decode_invoke ci = SOME (nm,ops) /\
  taint_ok caller tn ci s /\
  ld_owned_vars {v | MEM v (fn_ir_vars caller) /\ ~retpc_var caller v}
    E AG BH tn un s t /\
  eval_operands ops t = SOME args /\
  setup_callee callee args t = SOME cs ==>
  ?sargs ss.
    eval_operands ops s = SOME sargs /\
    setup_callee source sargs s = SOME ss /\
    ss.vs_params = sargs /\ cs.vs_params = args /\
    LENGTH (MAP (ld_op_prov AG) ops) = LENGTH ss.vs_params /\
    LENGTH (MAP (ld_op_prov BH) ops) = LENGTH cs.vs_params /\
    LENGTH ss.vs_params = LENGTH cs.vs_params /\
    (!q. q < LENGTH ss.vs_params ==>
      ld_owned_value E (EL q (MAP (ld_op_prov AG) ops))
        (EL q (MAP (ld_op_prov BH) ops)) {} {}
        (EL q ss.vs_params) (EL q cs.vs_params)) /\
    LIST_REL (ld_owned_selection E)
      (MAP (ld_op_prov AG) ops) (MAP (ld_op_prov BH) ops)
Proof
  strip_tac >>
  `ci.inst_operands = Label nm::ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `!v. MEM (Var v) ops ==>
    v IN {v | MEM v (fn_ir_vars caller) /\ ~retpc_var caller v}` by
    (rpt strip_tac >> irule ld_original_nonopaque_operand_support >>
     simp[] >> qexists_tac `ci` >> simp[]) >>
  `!op. MEM op ops ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  drule_all ld_call_setup_backward >>
  disch_then (qspecl_then [`un`, `tn`, `{}`] strip_assume_tac) >>
  qexistsl_tac [`sargs`, `ss`] >> simp[] >>
  drule_all ld_clean_call_list >> simp[]
QED
