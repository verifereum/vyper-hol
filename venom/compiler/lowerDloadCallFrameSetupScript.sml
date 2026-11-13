Theory lowerDloadCallFrameSetup
Ancestors
  lowerDloadCallParameters lowerDloadCoverageInvariant lowerDloadSharedState
  lowerDloadFrameCertificate lowerDloadPairedBoundary lowerDloadOwnership
  lowerDloadDefs ptrDiscipline venomExecSemantics venomState finite_map list pred_set

Theorem ld_frame_data_setup:
  setup_callee source xs s = SOME ss /\
  setup_callee callee ys t = SOME cs /\
  ld_shared_state tn un s t /\ s.vs_labels = t.vs_labels /\
  LIST_REL (ld_owned_selection E) AP BP ==>
  ld_frame_data V U E FEMPTY FEMPTY AP BP FEMPTY FEMPTY
    (tn with t_var := FEMPTY) (un with t_var := FEMPTY) ss cs
Proof
  simp[setup_callee_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  gvs[ld_frame_data_def, ld_frame_embedding_def, ld_erase_def,
      ld_owned_selection_def, ld_owned_vars_def, lookup_var_def,
      ld_shared_state_def]
QED

Theorem ld_call_frame_setup_backward:
  lower_dload_function_supply a source = (callee,b) /\
  opaque_use_ok caller /\ MEM ci (fn_insts caller) /\
  ci.inst_opcode = INVOKE /\ decode_invoke ci = SOME (nm,ops) /\
  taint_ok caller tn ci s /\
  ld_owned_vars {v | MEM v (fn_ir_vars caller) /\ ~retpc_var caller v}
    E AG BH tn un s t /\
  eval_operands ops t = SOME args /\
  setup_callee callee args t = SOME cs /\ ld_shared_state tn un s t ==>
  ?sargs ss.
    eval_operands ops s = SOME sargs /\
    setup_callee source sargs s = SOME ss /\
    ld_frame_data Vchild Uchild E FEMPTY FEMPTY
      (MAP (ld_op_prov AG) ops) (MAP (ld_op_prov BH) ops) FEMPTY FEMPTY
      (tn with t_var := FEMPTY) (un with t_var := FEMPTY) ss cs /\
    LENGTH (MAP (ld_op_prov AG) ops) = LENGTH ss.vs_params /\
    LENGTH (MAP (ld_op_prov BH) ops) = LENGTH cs.vs_params /\
    LENGTH ss.vs_params = LENGTH cs.vs_params /\
    (!q. q < LENGTH ss.vs_params ==>
      ld_owned_value E (EL q (MAP (ld_op_prov AG) ops))
        (EL q (MAP (ld_op_prov BH) ops)) {} {}
        (EL q ss.vs_params) (EL q cs.vs_params))
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[ld_owned_vars_def] >>
  drule_all ld_call_parameters_backward >> strip_tac >>
  qexistsl_tac [`sargs`, `ss`] >> simp[] >>
  metis_tac[ld_frame_data_setup]
QED
