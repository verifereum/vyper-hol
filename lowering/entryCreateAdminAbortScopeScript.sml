(* A failing administrative sequence confines the selected terminal path. *)
Theory entryCreateAdminAbortScope
Ancestors
  entryCreateFocusSpec entryCreatePathScope entryCreateCompletedCut
  createSizePrefixReplay createMarkedPath fragExec fragGasOrigin
  exprLoweringProps venomExecSemantics venomInstProps venomState venomInst
  instIdxIndep list arithmetic relation

Theorem admin_abort_successor[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  gas_origin_edge T E C f s left (OK t) ==>
  ?v. step_inst_base i s = OK v /\ t = v with vs_inst_idx := SUC s.vs_inst_idx /\
      v.vs_current_bb = s.vs_current_bb /\ ~v.vs_halted
Proof
  rw[gas_origin_edge_def] >> gvs[step_inst_non_invoke, exit_result_def] >>
  FIRST
    [qpat_x_assum `OK _ = step_inst_base _ _` (assume_tac o SYM) >>
       gvs[exit_result_def],
     qmatch_asmsub_rename_tac `step_inst_base i s = OK v` >>
       `step_inst 0 C i s = OK v` by simp[step_inst_non_invoke] >>
       drule_all step_preserves_control_flow >> simp[]]
QED

Theorem admin_abort_selected_step[local]:
  s.vs_inst_idx < LENGTH b.cs_current_insts /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
  gas_origin_edge T E C f s left (OK t) ==>
  create_expr_prefix a b E C f s left t
Proof
  strip_tac >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
  `gas_origin_edge F E C f s left (OK t)` by
    (qpat_x_assum `gas_origin_edge T _ _ _ _ _ _` mp_tac >>
     simp[gas_origin_edge_def] >> metis_tac[]) >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  simp[create_marked_edge_def, create_prefix_step_def] >> metis_tac[]
QED

Theorem admin_abort_selected_cons[local]:
  create_expr_prefix a b E C f s left t /\
  create_operand_full_scope a b E C f t right (Abort Revert_abort q) ==>
  create_operand_full_scope a b E C f s (left ++ right) (Abort Revert_abort q)
Proof
  simp[create_operand_full_scope_def] >> strip_tac >>
  drule_all create_expr_prefix_append >> metis_tac[APPEND_ASSOC]
QED

Theorem admin_sequence_abort_run[local]:
  !code s raw bb marks q.
    ~s.vs_halted /\ lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    (!j. j < LENGTH code ==>
         get_instruction bb (s.vs_inst_idx + j) = SOME (EL j code)) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = Abort Revert_abort raw /\
    gas_origin_path T E C f s marks (Abort Revert_abort q) ==>
    create_operand_full_scope a b E C f s marks (Abort Revert_abort q)
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> fs[EVERY_DEF] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (qpat_assum `!j. _ ==> get_instruction bb _ = _`
       (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [])) >> simp[]) >>
  `s.vs_inst_idx < LENGTH b.cs_current_insts` by decide_tac >>
  qpat_x_assum `gas_origin_path _ _ _ _ _ _ _` mp_tac >>
  simp[Once gas_origin_path_cases, exit_result_def] >> strip_tac
  >- (rename1 `gas_origin_edge T E C f s left (OK t)` >>
      drule_all admin_abort_successor >> strip_tac >>
      `create_expr_prefix a b E C f s left t` by
        (irule admin_abort_selected_step >> metis_tac[]) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      `run_inst_seq code t = Abort Revert_abort
          (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
        fs[run_inst_seq_def, run_inst_seq_inst_idx, exec_result_map_def] >>
      `create_operand_full_scope a b E C f t right (Abort Revert_abort q)` by
        (first_x_assum irule >> simp[ADD_CLAUSES] >>
         rpt strip_tac >>
         qpat_assum `!j. _ ==> get_instruction bb _ = _`
           (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [ADD_CLAUSES])) >>
         simp[ADD_CLAUSES]) >>
      metis_tac[admin_abort_selected_cons]) >>
  simp[create_operand_full_scope_def] >>
  qexistsl_tac [`[]`, `s`, `marks`] >> simp[] >> decide_tac
QED

Theorem create_admin_sequence_abort_scope:
  fn_has_code a b f /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b) /\
  create_operand_at a s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts a b) s = Abort Revert_abort raw /\
  gas_origin_path T E C f s marks (Abort Revert_abort q) ==>
  create_operand_full_scope a b E C f s marks (Abort Revert_abort q)
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  fs[create_operand_at_def] >>
  irule admin_sequence_abort_run >>
  first_assum (irule_at Any) >> qexistsl_tac [`raw`, `emitted_insts a b`, `bb`] >>
  simp[ADD_COMM] >> fs[EVERY_MEM]
QED
