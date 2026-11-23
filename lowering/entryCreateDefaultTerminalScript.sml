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
  `RTC (\p q. ~at_point sb p /\ ?n. gas_path_edge ctx fn p n (OK q)) t u` by
    (drule create_expr_prefix_rtc_project >> disch_then irule >>
     simp[create_prefix_step_def, at_point_def, PULL_EXISTS] >>
     metis_tac[gas_origin_edge_erase]) >>
  drule_then (assume_tac o CONJUNCT1) gas_origin_edge_erase >>
  `?bb i. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb u.vs_inst_idx = SOME i` by
    (qpat_assum `gas_path_edge ctx fn u _ r`
       (strip_assume_tac o REWRITE_RULE [gas_path_edge_def]) >>
     metis_tac[]) >>
  qpat_x_assum `!w bb i. _ ==> ~MEM i.inst_opcode _`
    (qspecl_then [`u`,`bb`,`i`] mp_tac) >>
  asm_rewrite_tac[] >> disch_tac >>
  irule entry_exit_edge_empty_revert >>
  qpat_assum `get_instruction bb u.vs_inst_idx = SOME i` (irule_at Any) >>
  qpat_assum `gas_path_edge ctx fn u _ r` (irule_at Any) >> fs[]
QED
