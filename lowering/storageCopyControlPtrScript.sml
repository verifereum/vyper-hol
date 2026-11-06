(* Counted control edges for checked storage-copy loops. *)
Theory storageCopyControlPtr
Ancestors
  fragGasSeqPtr fragGasPathPtr ptrSafeRun ptrDiscipline gasCount venomInst venomState
  venomExecSemantics venomExecProofs venomInstProofs exprLoweringProps codegenRel contextCodegenRel

Theorem storage_copy_jump_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `ptr_safe_step D 0 0 ctx func PG G tn
     (mk_inst id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem storage_copy_branch_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op; Label lt; Label lf] []) /\
  eval_operand op s = SOME (if test then 1w else 0w) /\
  op_taint tn op = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (jump_to (if test then lt else lf) s))
Proof
  strip_tac >> drule step_jnz_behavior >>
  disch_then (qspecl_then [`lt`, `lf`, `id`] assume_tac) >>
  `ptr_safe_step D 0 0 ctx func PG G tn
     (mk_inst id JNZ [op; Label lt; Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jnz_behavior, jump_to_def] >>
     Cases_on `test` >> gvs[op_taint_def] >>
     gen_tac >> Cases_on `op' = op` >> gvs[] >>
     Cases_on `op' = Label lt` >> gvs[] >>
     Cases_on `op' = Label lf` >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0 G tn
     (OK (jump_to (if test then lt else lf) s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jnz_behavior, is_terminator_def] >>
     Cases_on `test` >> gvs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to (if test then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

(* Clean literal initialization and equality tests overwrite stale scratch
   provenance as well as stale scratch taint. *)
Theorem storage_copy_scalar_check:
  (opc = ASSIGN /\ (?v. ops = [Lit v]) \/
   opc = EQ /\ (?v k. ops = [Var v; Lit k])) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK s' /\
  s'.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem storage_copy_scalar_ghost:
  (opc = ASSIGN /\ (?v. ops = [Lit v]) \/
   opc = EQ /\ (?v k. ops = [Var v; Lit k])) /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id opc ops [out]) s' = DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s s' tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, finite_mapTheory.FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mk_inst_def, op_prov_def, op_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, out_taint_def,
       first_prov_def, eval_operand_def] >>
  Cases_on `lookup_var v s` >> simp[]
QED

Theorem storage_copy_scalar_path_ptr:
  (opc = ASSIGN /\ (?v. ops = [Lit v]) \/
   opc = EQ /\ (?v k. ops = [Var v; Lit k])) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  u.vs_requests = s.vs_requests /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule storage_copy_scalar_check >> simp[] >> metis_tac[]) >>
  `step_prov PG G (mk_inst id opc ops [out]) u = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s u tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule storage_copy_scalar_ghost >> simp[] >> metis_tac[]) >>
  `step_inst 0 ctx (mk_inst id opc ops [out]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~u.vs_halted` by
    (drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem storage_copy_counter_steps:
  lookup_var cv s = SOME (n2w k) /\
  k <= n /\ n < dimword(:256) ==>
  step_inst_base (mk_inst id ASSIGN [Lit 0w] [cv]) s =
    OK (update_var cv 0w s) /\
  step_inst_base (mk_inst id EQ [Var cv; Lit (n2w n)] [test]) s =
    OK (update_var test (bool_to_word (k = n)) s)
Proof
  strip_tac >>
  `k < dimword(:256)` by decide_tac >>
  conj_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
                  instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, eval_operand_def,
       wordsTheory.n2w_11, arithmeticTheory.LESS_MOD, bool_to_word_def]
QED

Theorem storage_copy_init_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [cv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst jid JMP [Label hdr] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (OK (jump_to hdr (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx)))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [Lit 0w] [cv]) s =
     OK (update_var cv 0w s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure1_def, eval_operand_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
     (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
     (OK (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule storage_copy_scalar_path_ptr >>
     simp[update_var_def] >>
     qexistsl_tac [`id`, `ASSIGN`, `[Lit 0w]`] >>
     simp[op_taint_def] >> gvs[update_var_def]) >>
  `gas_path_ptr D 0 ctx fn PG
     (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
     (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx) 0
     (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
     (OK (jump_to hdr (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx)))` by
    (irule storage_copy_jump_path_ptr >> simp[update_var_def] >> metis_tac[]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem storage_copy_header_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [Var cv; Lit (n2w n)] [test]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var test; Label exit; Label body_lbl] []) /\
  lookup_var cv s = SOME (n2w k) /\ k <= n /\ n < dimword(:256) /\
  op_taint tn (Var cv) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {test})) (tn with t_var := tn.t_var |+ (test,{}))
    (OK (jump_to (if k = n then exit else body_lbl)
      (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx)))
Proof
  strip_tac >>
  drule_all storage_copy_counter_steps >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {test})) (tn with t_var := tn.t_var |+ (test,{}))
    (OK (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule storage_copy_scalar_path_ptr >> simp[update_var_def] >>
     qexistsl_tac [`id`, `EQ`, `[Var cv; Lit (n2w n)]`] >>
     simp[op_taint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
     gvs[op_taint_def, update_var_def] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG
    (DRESTRICT G (COMPL {test})) (tn with t_var := tn.t_var |+ (test,{}))
    (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx) 0
    (DRESTRICT G (COMPL {test})) (tn with t_var := tn.t_var |+ (test,{}))
    (OK (jump_to (if k = n then exit else body_lbl)
      (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx)))` by
    (irule storage_copy_branch_path_ptr >>
     simp[update_var_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, op_taint_def, bool_to_word_def] >>
     qexistsl_tac [`jid`, `Var test`] >>
     simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `k = n` >> simp[bool_to_word_def]) >>
  drule_all gas_path_ptr_then >> simp[]
QED
