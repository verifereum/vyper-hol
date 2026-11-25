(* Scope the physical post-request cursor, independently of its ghost frame. *)
Theory entryCreateRawCallReturnGeometry
Ancestors
  entryCreateAdminSequence entryCreateIfExpAdmin entryCreatePathScope
  entryCreateFocusSpec entryCreateCompletedCut abiEncoderProps
  exprSimRawCallCalldata emitHelperProps fragExec compileEnv
  createSizePrefixReplay createMarkedPath relation
  venomExecProofs venomExecSemantics venomState venomInst arithmetic list

Theorem raw_call_finish_jump_prefix:
  emit_inst JNZ [status;Label good;Label bad] [] sj = ((),sn) /\
  fn_has_code sj sn f /\ create_operand_at sj s /\ ~s.vs_halted /\
  eval_operand status s = SOME (if success then 1w else 0w) /\
  sj.cs_next_id IN frag_ids a b /\ ~create_operand_at b s ==>
  create_expr_prefix a b E C f s []
    (jump_to (if success then good else bad) s)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sj.cs_next_id JNZ [status;Label good;Label bad] [])` by
    (fs[create_operand_at_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  `step_inst_base (mk_inst sj.cs_next_id JNZ [status;Label good;Label bad] []) s =
    OK (jump_to (if success then good else bad) s)` by
    (Cases_on `success` >> fs[] >> drule step_jnz_behavior >> simp[mk_inst_def]) >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >> simp[create_marked_edge_def] >>
  irule ifexp_jump_edge >> simp[] >>
  qexists_tac `mk_inst sj.cs_next_id JNZ [status;Label good;Label bad] []` >>
  simp[create_operand_fetch_def] >> metis_tac[]
QED

Theorem raw_call_finish_return_scope:
  fn_has_code m b f /\ b.cs_current_bb = m.cs_current_bb /\
  b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts m b) /\
  create_expr_prefix a b E C f s [] j /\
  create_operand_at m j /\ ~j.vs_halted /\
  run_inst_seq (emitted_insts m b) j = OK t /\
  a.cs_next_id <= m.cs_next_id /\
  EVERY (\i. m.cs_next_id <= i.inst_id) (emitted_insts m b) ==>
  create_operand_full_scope a b E C f s []
    (OK (t with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_id IN frag_ids m b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts m b)` by fs[EVERY_MEM,frag_ids_def] >>
  drule_all create_admin_sequence_scope >>
  disch_then (qspecl_then [`E`,`C`]
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [create_operand_full_scope_def,exec_result_case_def])) >>
  `create_expr_prefix a b E C f j [] (t with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (irule create_expr_prefix_mono >> first_assum (irule_at Any) >>
     rw[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qpat_x_assum `b.cs_current_insts = _` kall_tac >>
  `create_expr_prefix a b E C f s [] (t with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (fs[create_expr_prefix_marked] >> irule RTC_TRANS >>
     qexists_tac `(j,[]:bool list)` >> asm_rewrite_tac[]) >>
  simp_tac bool_ss [create_operand_full_scope_def,exec_result_case_def] >>
  BETA_TAC >> asm_rewrite_tac[]
QED
