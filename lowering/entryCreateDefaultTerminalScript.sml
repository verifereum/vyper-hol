(* Classify the terminal edge of the same scoped initializer execution. *)
Theory entryCreateDefaultTerminal
Ancestors
  entryCreateCompletedCut createSizePrefixReplay groupedRejectTerminal
  fragGasOrigin fragGasPath fragFuel fragExec venomExecSemantics
  venomInst venomState compileEnv relation list
Libs
  groupedRejectCutLib

Theorem scoped_default_terminal_revert:
  exit_result r /\ create_operand_full_scope sa sb explicit ctx fn t marks r /\
  (!u bb i. ^row22_stopped ctx fn sb t u /\ ~at_point sb u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==> ^row22_opcode_ok i) ==>
  ?z. r = Abort Revert_abort z /\ z.vs_returndata = []
Proof
  BETA_TAC >> strip_tac >>
  `?left u last. create_expr_prefix sa sb explicit ctx fn t left u /\
    ~at_point sb u /\ gas_origin_edge T explicit ctx fn u last r` by
    (qpat_x_assum `create_operand_full_scope _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `r` >> fs[exit_result_def, create_operand_full_scope_def, at_point_def] >>
     metis_tac[]) >>
  `^row22_stopped ctx fn sb t u` by
    (BETA_TAC >> drule create_expr_prefix_rtc_project >> disch_then irule >>
     simp[create_prefix_step_def, at_point_def, PULL_EXISTS] >>
     metis_tac[gas_origin_edge_erase]) >>
  drule_then (assume_tac o CONJUNCT1) gas_origin_edge_erase >>
  qpat_assum `gas_path_edge ctx fn u _ r`
    (strip_assume_tac o REWRITE_RULE [gas_path_edge_def]) >>
  qpat_assum `!w bb i. _ ==> ~MEM i.inst_opcode _`
    (drule_all_then assume_tac) >>
  irule entry_exit_edge_empty_revert >>
  qpat_assum `gas_path_edge ctx fn u _ r` (irule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> fs[]
QED
