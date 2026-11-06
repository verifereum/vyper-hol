(* Runtime control edges for the storage-copy loop.  The jump edge stops
   before ambient exit PHIs, retaining the actual endpoint and ghosts. *)
Theory storageCopyControlPtr
Ancestors
  payloadLoadStorePtr fragGasSeqPtr fragGasPathPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomExecProofs venomInst venomState codegenRel
  contextCodegenRel gasCount fragExec finite_map list arithmetic pred_set words

Theorem copy_loop_jump_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `ptr_safe_step D 0 0 ctx fn PG G tn inst s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def] >>
     gvs[source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[step_inst_non_invoke, jump_to_def] >> metis_tac[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists `0:num` >>
     gvs[step_inst_non_invoke, gas_count_step_def, is_terminator_def] >>
     metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, ADD_CLAUSES]
QED

Theorem copy_loop_eq_step:
  lookup_var cv s = SOME (n2w k) /\ k <= n /\ n < dimword(:256) ==>
  step_inst_base (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) s =
    OK (update_var tv (bool_to_word (k = n)) s)
Proof
  strip_tac >> `k < dimword(:256)` by decide_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, wordsTheory.n2w_11]
QED

Theorem copy_loop_eq_ghost:
  step_prov PG G (mk_inst id EQ [Var cv; Lit n] [tv]) (update_var tv w s) =
    DRESTRICT G (COMPL {tv}) /\
  step_taint (mk_inst id EQ [Var cv; Lit n] [tv]) s (update_var tv w s) tn =
    tn with t_var := tn.t_var |+ (tv,{})
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       step_taint_def, set_var_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def, new_site_bytes_def,
       update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss, out_taint_def,
       eval_operand_def, taint_component_equality] >>
  Cases_on `lookup_var cv s` >> simp[]
QED

Theorem copy_loop_eq_check:
  op_taint tn (Var cv) = {} /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id EQ [Var cv; Lit n] [tv]) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id EQ [Var cv; Lit n] [tv]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  rpt strip_tac >> Cases_on `op = Var cv` >> gvs[op_taint_def] >>
  Cases_on `op = Lit n` >> gvs[op_taint_def]
QED

Theorem copy_loop_eq_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) /\
  lookup_var cv s = SOME (n2w k) /\ k <= n /\ n < dimword(:256) /\
  op_taint tn (Var cv) = {} /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (OK ((update_var tv (bool_to_word (k = n)) s)
           with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  drule_all copy_loop_eq_step >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) s` by
    (irule copy_loop_eq_check >> simp[update_var_def] >> metis_tac[]) >>
  `~is_terminator (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]).inst_opcode /\
   (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  first_x_assum (qspecl_then [`tv`, `id`] assume_tac) >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >>
  simp[GSYM mk_inst_def, copy_loop_eq_ghost] >> strip_tac >>
  `~(update_var tv (bool_to_word (k = n)) s with
      vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
  metis_tac[gas_path_ptr_rules, ADD_CLAUSES]
QED

Theorem copy_loop_branch_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [Var tv; Label exit_lbl; Label body_lbl] []) /\
  lookup_var tv s = SOME (bool_to_word done) /\
  op_taint tn (Var tv) = {} /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if done then exit_lbl else body_lbl) s))
Proof
  strip_tac >> irule copy_loop_jump_path_ptr >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[op_taint_def]) >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, bool_to_word_def] >> Cases_on `done` >> simp[]
QED

Theorem copy_loop_header_path_ptr:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id EQ [Var cv; Lit (n2w n)] [tv];
     mk_inst (id+1) JNZ [Var tv; Label exit_lbl; Label body_lbl] []] /\
  lookup_var cv s = SOME (n2w k) /\ k <= n /\ n < dimword(:256) /\
  op_taint tn (Var cv) = {} /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (OK (jump_to (if k = n then exit_lbl else body_lbl)
           (update_var tv (bool_to_word (k = n)) s)))
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [Var cv; Lit (n2w n)] [tv])` by
    simp[get_instruction_def] >>
  drule_all copy_loop_eq_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {tv}))
    (tn with t_var := tn.t_var |+ (tv,{}))
    (update_var tv (bool_to_word (k = n)) s with vs_inst_idx := 1) 0
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (OK (jump_to (if k = n then exit_lbl else body_lbl)
      (update_var tv (bool_to_word (k = n)) s with vs_inst_idx := 1)))` by
    (irule copy_loop_branch_path_ptr >>
     simp[update_var_def, get_instruction_def, lookup_var_def,
          FLOOKUP_UPDATE, op_taint_def, jump_to_def] >>
     qexistsl [`id+1`, `tv`] >> simp[]) >>
  gvs[jump_to_def] >> metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED
