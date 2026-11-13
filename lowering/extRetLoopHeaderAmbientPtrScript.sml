Theory extRetLoopHeaderAmbientPtr
Ancestors
  abiEncoderArrayHeader typedCopyLoopHeaderPtr typedCopyPtr ptrDiscipline
  extRetAbiArrayBackedgePtr fragExec fragGasSeqPtr fragGasPathPtr bodyPtrDefs ptrSafeRun
  venomExecSemantics venomExecProofs venomInst venomState emitHelperProps
  codegenRel contextCodegenRel compileEnv loweringShapeRules stmtFragPtr gasCount
  words finite_map pred_set arithmetic wordLoadStorePtr bodyPtrCtrlCases

Theorem loop_header_lt_check[local]:
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id LT [left;right] [out]) s = OK u /\
  u.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id LT [left;right] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  conj_tac >- (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem loop_header_prefix_ambient_ptr[local]:
  ptr_covers G tn ip s 32 /\ lookup_var ip s = SOME p /\
  ~ctx_has_dalloca ctx /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  count_op <> Var iv /\ op_taint tn count_op = {} /\ op_prov G count_op = NONE /\
  eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w j /\ j <= n /\ n < dimword(:256) ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 3 (abi_encode_array_header_insts id (Var ip) count_op iv cmp done body_lbl exit_lbl))
      s Gf tnf /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    op_taint tnf (Var done) = {} /\
    (!v. v <> iv /\ v <> cmp /\ v <> done ==>
      FLOOKUP Gf v = FLOOKUP G v /\ op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  qabbrev_tac `a = mk_inst id MLOAD [Var ip] [iv]` >>
  qabbrev_tac `b = mk_inst (id+1) LT [Var iv;count_op] [cmp]` >>
  qabbrev_tac `c = mk_inst (id+2) ISZERO [Var cmp] [done]` >>
  qabbrev_tac `u = update_var iv (n2w j) s` >>
  qabbrev_tac `v = update_var cmp (bool_to_word (j<n)) u` >>
  qabbrev_tac `w = update_var done (bool_to_word (~(j<n))) v` >>
  qabbrev_tac `g1 = step_prov PG G a u` >>
  qabbrev_tac `t1 = step_taint a s u tn` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {cmp})` >>
  qabbrev_tac `t2 = t1 with t_var := t1.t_var |+ (cmp,{})` >>
  qabbrev_tac `g3 = DRESTRICT g2 (COMPL {done})` >>
  qabbrev_tac `t3 = t2 with t_var := t2.t_var |+ (done,{})` >>
  `eval_operand count_op u = SOME (n2w n)` by
    (Cases_on `count_op` >> gvs[Abbr `u`, eval_operand_def, lookup_var_update_var]) >>
  `j < dimword(:256)` by decide_tac >>
  `step_inst_base a s = OK u /\
   step_inst_base b (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (v with vs_inst_idx := SUC s.vs_inst_idx) /\
   step_inst_base c (v with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
     OK (w with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    (simp[Abbr `a`, Abbr `b`, Abbr `c`, Abbr `u`, Abbr `v`, Abbr `w`] >>
     simp[Once step_inst_base_def, mk_inst_def, exec_read1_def, eval_operand_def] >>
     simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
          eval_operand_def, lookup_var_update_var, w2n_n2w] >>
     simp[Once step_inst_base_def, mk_inst_def, exec_pure1_def,
          eval_operand_def, lookup_var_update_var] >>
     Cases_on `j<n` >> simp[bool_to_word_def, update_var_def]) >>
  `op_taint t1 (Var iv) = {} /\ t1.t_mem = tn.t_mem /\
   t1.t_stor = tn.t_stor /\ t1.t_trans = tn.t_trans` by
    (simp[Abbr `t1`, Abbr `a`, Abbr `u`] >>
     `eval_operand (Var ip) s = SOME p` by simp[eval_operand_def] >>
     drule_all mload_ghost_clean >> simp[] >> metis_tac[]) >>
  `t1.t_imm = tn.t_imm` by
    simp[Abbr `t1`, Abbr `a`, step_taint_def, set_var_taint_def,
         imm_taint_def, mk_inst_def] >>
  `op_taint t1 count_op = {} /\ op_prov g1 count_op = NONE /\
   op_prov g1 (Var iv) = NONE` by
    (Cases_on `count_op` >>
     gvs[Abbr `t1`, Abbr `g1`, Abbr `a`, step_taint_def, set_var_taint_def,
         op_taint_def, step_prov_def, set_prov_def, out_prov_def, op_prov_def,
         mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  qexistsl_tac [`g3`, `t3`] >> conj_tac >-
    (`ptr_inst_ok D 0 0 ctx fn G tn a s` by
       (simp[Abbr `a`] >> irule ptr_inst_ok_mload >> simp[]) >>
     `ptr_inst_ok D 0 0 ctx fn g1 t1 b (u with vs_inst_idx := SUC s.vs_inst_idx)` by
       (simp[Abbr `b`] >> irule loop_header_lt_check >> simp[] >>
        simp[Abbr `v`, Abbr `u`, update_var_def]) >>
     `ptr_inst_ok D 0 0 ctx fn g2 t2 c (v with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
       (simp[Abbr `c`] >> irule typed_copy_loop_test_check >> simp[] >>
        simp[Abbr `w`, Abbr `t2`, op_taint_def, FLOOKUP_UPDATE, update_var_def]) >>
     gvs[Abbr `a`, Abbr `b`, Abbr `c`] >>
     simp[abi_encode_array_header_insts_def, inst_seq_ptr_def] >>
     `v.vs_allocas = u.vs_allocas /\ v.vs_fmp = u.vs_fmp /\
      w.vs_allocas = v.vs_allocas /\ w.vs_fmp = v.vs_fmp` by
       simp[Abbr `v`, Abbr `w`, update_var_def] >>
     simp[typed_copy_loop_arith_ghost, Abbr `g2`, Abbr `t2`, Abbr `g3`, Abbr `t3`,
          step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
     asm_rewrite_tac[GSYM mk_inst_def] >>
     simp[out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE,
          Abbr `u`, Abbr `v`, eval_operand_def, lookup_var_update_var] >>
     asm_rewrite_tac[GSYM mk_inst_def]) >>
  simp[Abbr `t3`, Abbr `t2`, op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  simp[Abbr `g3`, Abbr `g2`, Abbr `g1`, Abbr `a`,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  simp[Abbr `t1`, step_taint_def, set_var_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem loop_header_prefix_ambient_counted_ptr[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = abi_encode_array_header_insts id (Var ip) count_op iv cmp done body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ptr_covers G tn ip s 32 /\ lookup_var ip s = SOME p /\
  ~ctx_has_dalloca ctx /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  count_op <> Var iv /\ op_taint tn count_op = {} /\ op_prov G count_op = NONE /\
  eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w j /\ j <= n /\ n < dimword(:256) ==>
  ?Gf tnf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK ((abi_encode_array_header_state iv cmp done j n s) with vs_inst_idx := 3)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    op_taint tnf (Var done) = {} /\
    (!v. v <> iv /\ v <> cmp /\ v <> done ==>
      FLOOKUP Gf v = FLOOKUP G v /\ op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all loop_header_prefix_ambient_ptr >>
  disch_then (qspecl_then [`id`,`fn`,`exit_lbl`,`done`,`cmp`,`body_lbl`,`PG`,`D`]
    strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`] >> simp[] >>
  `eval_operand (Var ip) s = SOME p` by simp[eval_operand_def] >>
  drule_all abi_encode_array_header_prefix >> strip_tac >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) run_inst_seq_gas_path_ptr >>
  simp[abi_encode_array_header_insts_def, mk_inst_def, is_terminator_def] >>
  disch_then irule >> simp[]
QED

Theorem loop_header_branch_ptr[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [Var done;Label exit_lbl;Label body_lbl] []) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_var done s = SOME (bool_to_word (~(j<n))) /\ op_taint tn (Var done) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if j<n then body_lbl else exit_lbl) s))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id JNZ [Var done;Label exit_lbl;Label body_lbl] []) s =
    OK (jump_to (if j<n then body_lbl else exit_lbl) s)` by
    (simp[Once step_inst_base_def, mk_inst_def, eval_operand_def] >>
     Cases_on `j<n` >> simp[bool_to_word_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id JNZ [Var done;Label exit_lbl;Label body_lbl] []) s` by
    (irule typed_copy_loop_test_check >> simp[] >>
     rpt strip_tac >> gvs[op_taint_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if j<n then body_lbl else exit_lbl) s))` by
    (simp[gas_path_ptr_edge_def] >> qexists_tac `0` >>
     simp[gas_count_step_def, ptr_safe_step_def, step_inst_non_invoke, mk_inst_def] >>
     simp[GSYM mk_inst_def, is_terminator_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `if j<n then body_lbl else exit_lbl` >> simp[]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[jump_to_def]
QED

Theorem abi_encode_array_header_ambient_counted_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = abi_encode_array_header_insts id (Var ip) count_op iv cmp done body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ptr_covers G tn ip s 32 /\ lookup_var ip s = SOME p /\
  ~ctx_has_dalloca ctx /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  count_op <> Var iv /\ op_taint tn count_op = {} /\ op_prov G count_op = NONE /\
  eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w j /\ j <= n /\ n < dimword(:256) ==>
  ?Gf tnf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (jump_to (if j<n then body_lbl else exit_lbl)
        (abi_encode_array_header_state iv cmp done j n s))) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. v <> iv /\ v <> cmp /\ v <> done ==>
      FLOOKUP Gf v = FLOOKUP G v /\ op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all loop_header_prefix_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`] >> simp[] >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb u.vs_inst_idx =
    SOME (mk_inst (id+3) JNZ [Var done;Label exit_lbl;Label body_lbl] []) /\
   ~u.vs_halted /\ lookup_var done u = SOME (bool_to_word (~(j<n)))` by
    simp[Abbr `u`, abi_encode_array_header_state_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, get_instruction_def, abi_encode_array_header_insts_def] >>
  drule_all loop_header_branch_ptr >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] mp_tac) >>
  simp[Abbr `u`, jump_to_def] >> strip_tac >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem abi_array_header_entry_ambient_counted_ptr:
  abi_encode_array_header ip count_op sa = ((hdr,body_lbl,exit_lbl),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to hdr s))
Proof
  strip_tac >>
  qabbrev_tac `cut = sa with cs_current_insts := sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label hdr] []]` >>
  `fn_has_code sa cut fn` by
    (gvs[abi_encode_array_header_shape, fn_has_code_def, emitted_blocks_def, Abbr `cut`] >>
     first_x_assum (qspec_then `<|bb_label := sa.cs_current_bb;
       bb_instructions := sa.cs_current_insts ++ [mk_inst sa.cs_next_id JMP
         [Label (fresh_label_output "enc_dyn_hdr" sa.cs_next_label)] []]|>` mp_tac) >>
     simp[] >> strip_tac >> goal_assum drule >> simp[]) >>
  irule emit_jump_zero_path_ptr >>
  simp[] >> qexistsl_tac [`sa`,`cut`] >> simp[Abbr `cut`]
QED
