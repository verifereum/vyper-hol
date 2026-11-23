Theory entryCreateConvertBytes
Ancestors
  bodyFullConvertBytesJoint bodyFullConvertCastOrigin exprSimConvertBytes
  entryCreateAdminSequence entryCreateScopedBind entryCreateScopedForce
  entryCreateNativeFirstExit entryCreateRegionLift entryCreatePendingScope
  entryCreateIntervalLayout entryCreatePathScope entryCreateCompletedCut
  entryCreateFocusSpec entryCreateCompositeFocus createSizeCutCode createSizeCutRegion
  fragGasOriginPtr fragGasOrigin fragGasSeqAbort fragExec instIdxIndep
  exprLoweringProps abiBufferAllocationCode gasEvents venomInstProps venomInst
  createSizePrefixReplay createMarkedPath
  venomExecSemantics venomState list rich_list arithmetic

Theorem convert_straight_origin_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS /\
  gas_origin_edge T E C fn s marks r ==>
  marks = [] /\ (~s.vs_halted) /\
  ((?u. step_inst_base i s = OK u /\ ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
        r = OK (u with vs_inst_idx := SUC s.vs_inst_idx)) \/
   (exit_result (step_inst_base i s) /\ r = step_inst_base i s))
Proof
  simp[gas_origin_edge_def] >> strip_tac >>
  gvs[step_inst_non_invoke, gas_events_step_def] >>
  metis_tac[step_preserves_control_flow, step_inst_non_invoke]
QED

(* Consume only the installed code preceding the abort. The path gives the
   memory-checked final edge; the sequence run rules out an earlier exit PC. *)
Theorem convert_abort_scope_from_code[local]:
  !code s bb raw u marks.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = Abort Revert_abort raw /\
    gas_origin_path T E C fn s marks (Abort Revert_abort u) ==>
    create_operand_full_scope a b E C fn s marks (Abort Revert_abort u)
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by (fs[] >> decide_tac) >>
  qpat_x_assum `gas_origin_path T _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_origin_path_cases]) >> gvs[]
  >- suspend "step" >> suspend "terminal"
QED

Resume convert_abort_scope_from_code[step]:
  drule_all convert_straight_origin_edge >> strip_tac >> gvs[] >>
  TRY (qpat_x_assum `OK _ = step_inst_base _ _` (assume_tac o SYM) >>
       gvs[exit_result_def]) >>
  rename1 `step_inst_base h s = OK z` >>
  qabbrev_tac `t = z with vs_inst_idx := SUC s.vs_inst_idx` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  `run_inst_seq code t = Abort Revert_abort (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
    fs[Abbr `t`, run_inst_seq_def, run_inst_seq_inst_idx, exec_result_map_def] >>
  `create_operand_full_scope a b E C fn t right (Abort Revert_abort u)` by
    (qpat_x_assum `!s bb raw u marks. _` irule >>
     simp[Abbr `t`, ADD_CLAUSES] >> metis_tac[]) >>
  `gas_origin_edge F E C fn s [] (OK t)` by
    (qpat_assum `gas_origin_edge T E C fn s [] (OK t)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss [gas_origin_edge_def] >> metis_tac[]) >>
  `create_expr_prefix a b E C fn s [] t` by
    (simp[create_expr_prefix_marked] >> irule relationTheory.RTC_SINGLE >>
     simp[create_marked_edge_def,create_prefix_step_def] >> metis_tac[]) >>
  qpat_x_assum `create_operand_full_scope a b E C fn t _ _` mp_tac >>
  simp[create_operand_full_scope_def] >>
  metis_tac[create_expr_prefix_append, APPEND_NIL]
QED

Resume convert_abort_scope_from_code[terminal]:
  simp[create_operand_full_scope_def] >>
  qexistsl_tac [`[]`,`s`,`marks`] >> simp[create_expr_prefix_marked]
QED

Finalise convert_abort_scope_from_code
