(* Checked executed prefixes of the guarded BLOCKHASH lowering. *)
Theory bodyPtrEnvBuiltinsBlockHashRun
Ancestors bodyPtrEnvBuiltinsGuards bodyPtrEnvBuiltinsEdges exprSendPtr
  builtinMisc builtinProps compileEnv loweringStateRelDefs emitHelper exprLoweringProps fragExec fragGasSeqPtr
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  context rich_list finite_map pred_set list codegenRel contextCodegenRel
  decoderGhostFramePtr stmtAppendStoragePathPtr emitHelperProps

Theorem blockhash_compile_code:
  compile_blockhash arg sa = (op,sb) ==>
  ?cur lo old good recent out.
    op = Var out /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id NUMBER [] [cur];
       mk_inst (sa.cs_next_id+1) SUB [Var cur; Lit 256w] [lo];
       mk_inst (sa.cs_next_id+2) SLT [arg; Var lo] [old];
       mk_inst (sa.cs_next_id+3) ISZERO [Var old] [good];
       mk_inst (sa.cs_next_id+4) ASSERT [Var good] [];
       mk_inst (sa.cs_next_id+5) LT [arg; Var cur] [recent];
       mk_inst (sa.cs_next_id+6) ASSERT [Var recent] [];
       mk_inst (sa.cs_next_id+7) BLOCKHASH [arg] [out]] /\
    cur = "%" ++ toString sa.cs_next_var /\
    lo = "%" ++ toString (sa.cs_next_var+1) /\
    old = "%" ++ toString (sa.cs_next_var+2) /\
    good = "%" ++ toString (sa.cs_next_var+3) /\
    recent = "%" ++ toString (sa.cs_next_var+4) /\
    out = "%" ++ toString (sa.cs_next_var+5) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 8
Proof
  simp[compile_blockhash_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem blockhash_assert_inst_ok[local]:
  ~ctx_has_dalloca ctx /\ op_taint tn arg = {} ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSERT [arg] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem blockhash_clean_other_operand[local]:
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  (!x. arg = Var x ==> x <> out) ==>
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) arg = {} /\
  op_prov (step_prov PG G (mk_inst id opc ops [out]) t) arg = NONE
Proof
  Cases_on `arg` >> simp[op_taint_def, op_prov_def] >> strip_tac >>
  simp[step_taint_def, set_var_taint_def, step_prov_def, set_prov_def,
       mk_inst_def, op_taint_def] >>
  Cases_on `out_prov PG G (mk_inst id opc ops [out]) t` >>
  gvs[mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem blockhash_assert_cons[local]:
  ~ctx_has_dalloca ctx /\ op_taint tn arg = {} /\
  (?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code
      (s with vs_inst_idx := SUC s.vs_inst_idx) G' tn') ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn
    (mk_inst id ASSERT [arg] [] :: code) s G' tn'
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [arg] []) s` by
    (irule blockhash_assert_inst_ok >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >> Cases_on `eval_operand arg s` >> simp[] >>
  Cases_on `x = 0w` >> simp[] >>
  pure_rewrite_tac[GSYM mk_inst_def] >> simp[assert_ghost_unchanged] >>
  goal_assum (drule_at Any)
QED

Theorem blockhash_tail_certificate[local]:
  code = [mk_inst il LT [arg; cur] [recent];
          mk_inst ia ASSERT [Var recent] [];
          mk_inst ih BLOCKHASH [arg] [out]] /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  op_taint tn cur = {} /\ op_prov G cur = NONE /\
  (!x. arg = Var x ==> x <> recent) /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn'
Proof
  strip_tac >> gvs[] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst il LT [arg; cur] [recent]) s` by
    (irule guard_compare_inst_ok >> simp[] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst il LT [arg; cur] [recent]) s` >> simp[] >>
  rename1 `step_inst_base _ _ = OK u` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst il LT [arg; cur] [recent]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst il LT [arg; cur] [recent]) s u tn` >>
  `op_taint tn1 (Var recent) = {}` by
    (simp[Abbr `tn1`] >> irule (cj 2 guard_compare_output_clean) >> simp[]) >>
  `op_taint tn1 arg = {}` by
    (simp[Abbr `tn1`] >> irule (cj 1 blockhash_clean_other_operand) >>
     simp[] >> goal_assum (drule_at Any)) >>
  irule blockhash_assert_cons >> simp[] >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 (mk_inst ih BLOCKHASH [arg] [out])
      (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    (irule ptr_inst_ok_scalar_builtin >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst ih BLOCKHASH [arg] [out])
      (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))` >>
  simp[inst_seq_ptr_def]
QED

Theorem blockhash_iszero_certificate[local]:
  code = [mk_inst iz ISZERO [old] [good];
          mk_inst ia ASSERT [Var good] [];
          mk_inst il LT [arg; cur] [recent];
          mk_inst ib ASSERT [Var recent] [];
          mk_inst ih BLOCKHASH [arg] [out]] /\
  op_taint tn old = {} /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  op_taint tn cur = {} /\ op_prov G cur = NONE /\
  arg <> Var good /\ cur <> Var good /\ arg <> Var recent /\
  ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn'
Proof
  strip_tac >> gvs[] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst iz ISZERO [old] [good]) s` by
    (irule ptr_inst_ok_scalar_builtin >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst iz ISZERO [old] [good]) s` >> simp[] >>
  rename1 `step_inst_base _ _ = OK u` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst iz ISZERO [old] [good]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst iz ISZERO [old] [good]) s u tn` >>
  `op_taint tn1 (Var good) = {}` by
    (simp[Abbr `tn1`] >> irule scalar_builtin_output_clean >> simp[]) >>
  `op_taint tn1 arg = {} /\ op_prov G1 arg = NONE` by
    (simp[Abbr `tn1`, Abbr `G1`] >>
     irule blockhash_clean_other_operand >> simp[]) >>
  `op_taint tn1 cur = {} /\ op_prov G1 cur = NONE` by
    (simp[Abbr `tn1`, Abbr `G1`] >>
     irule blockhash_clean_other_operand >> simp[]) >>
  irule blockhash_assert_cons >> simp[] >>
  irule blockhash_tail_certificate >> simp[mk_inst_def]
QED

Theorem blockhash_slt_certificate[local]:
  code = [mk_inst is SLT [arg; lo] [old];
          mk_inst iz ISZERO [Var old] [good];
          mk_inst ia ASSERT [Var good] [];
          mk_inst il LT [arg; cur] [recent];
          mk_inst ib ASSERT [Var recent] [];
          mk_inst ih BLOCKHASH [arg] [out]] /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  op_taint tn cur = {} /\ op_prov G cur = NONE /\
  op_taint tn lo = {} /\ op_prov G lo = NONE /\
  arg <> Var old /\ cur <> Var old /\
  arg <> Var good /\ cur <> Var good /\ arg <> Var recent /\
  ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn'
Proof
  strip_tac >> gvs[] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst is SLT [arg; lo] [old]) s` by
    (irule guard_compare_inst_ok >> simp[] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst is SLT [arg; lo] [old]) s` >> simp[] >>
  rename1 `step_inst_base _ _ = OK u` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst is SLT [arg; lo] [old]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst is SLT [arg; lo] [old]) s u tn` >>
  `op_taint tn1 (Var old) = {}` by
    (simp[Abbr `tn1`] >> irule (cj 2 guard_compare_output_clean) >> simp[]) >>
  `op_taint tn1 arg = {} /\ op_prov G1 arg = NONE` by
    (simp[Abbr `tn1`, Abbr `G1`] >>
     irule blockhash_clean_other_operand >> simp[]) >>
  `op_taint tn1 cur = {} /\ op_prov G1 cur = NONE` by
    (simp[Abbr `tn1`, Abbr `G1`] >>
     irule blockhash_clean_other_operand >> simp[]) >>
  irule blockhash_iszero_certificate >> simp[mk_inst_def]
QED

Theorem blockhash_sub_certificate[local]:
  code = [mk_inst is SUB [Var cur; Lit 256w] [lo];
          mk_inst it SLT [arg; Var lo] [old];
          mk_inst iz ISZERO [Var old] [good];
          mk_inst ia ASSERT [Var good] [];
          mk_inst il LT [arg; Var cur] [recent];
          mk_inst ib ASSERT [Var recent] [];
          mk_inst ih BLOCKHASH [arg] [out]] /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  op_taint tn (Var cur) = {} /\ op_prov G (Var cur) = NONE /\
  arg <> Var lo /\ arg <> Var old /\ arg <> Var good /\ arg <> Var recent /\
  cur <> lo /\ cur <> old /\ cur <> good /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn'
Proof
  strip_tac >> gvs[] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst is SUB [Var cur; Lit 256w] [lo]) s` by
    (irule ptr_inst_ok_scalar_builtin >> simp[] >> rpt strip_tac >> gvs[op_taint_def]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst is SUB [Var cur; Lit 256w] [lo]) s` >> simp[] >>
  rename1 `step_inst_base _ _ = OK u` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst is SUB [Var cur; Lit 256w] [lo]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst is SUB [Var cur; Lit 256w] [lo]) s u tn` >>
  `op_taint tn1 (Var lo) = {}` by
    (simp[Abbr `tn1`] >> irule scalar_builtin_output_clean >> simp[] >> rpt strip_tac >> gvs[op_taint_def]) >>
  `op_prov G1 (Var lo) = NONE` by
    (simp[Abbr `G1`] >> irule scalar_arith_output_no_prov >> simp[] >> rpt strip_tac >> gvs[op_prov_def]) >>
  `op_taint tn1 arg = {} /\ op_prov G1 arg = NONE` by
    (simp[Abbr `tn1`, Abbr `G1`] >>
     irule blockhash_clean_other_operand >> simp[]) >>
  `op_taint tn1 (Var cur) = {} /\ op_prov G1 (Var cur) = NONE` by
    (simp[Abbr `tn1`, Abbr `G1`] >>
     irule blockhash_clean_other_operand >> simp[]) >>
  irule blockhash_slt_certificate >> simp[mk_inst_def]
QED

Theorem blockhash_sequence_certificate:
  code = [mk_inst inum NUMBER [] [cur];
          mk_inst is SUB [Var cur; Lit 256w] [lo];
          mk_inst it SLT [arg; Var lo] [old];
          mk_inst iz ISZERO [Var old] [good];
          mk_inst ia ASSERT [Var good] [];
          mk_inst il LT [arg; Var cur] [recent];
          mk_inst ib ASSERT [Var recent] [];
          mk_inst ih BLOCKHASH [arg] [out]] /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  arg <> Var cur /\ arg <> Var lo /\ arg <> Var old /\
  arg <> Var good /\ arg <> Var recent /\
  cur <> lo /\ cur <> old /\ cur <> good /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn'
Proof
  strip_tac >> gvs[] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst inum NUMBER [] [cur]) s` by
    (irule ptr_inst_ok_scalar_builtin >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst inum NUMBER [] [cur]) s` >> simp[] >>
  rename1 `step_inst_base _ _ = OK u` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst inum NUMBER [] [cur]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst inum NUMBER [] [cur]) s u tn` >>
  `op_taint tn1 (Var cur) = {}` by
    (simp[Abbr `tn1`] >> irule scalar_builtin_output_clean >> simp[]) >>
  `op_prov G1 (Var cur) = NONE` by
    (simp[Abbr `G1`] >> irule scalar_builtin_output_no_prov >> simp[]) >>
  `op_taint tn1 arg = {} /\ op_prov G1 arg = NONE` by
    (simp[Abbr `tn1`, Abbr `G1`] >>
     irule blockhash_clean_other_operand >> simp[]) >>
  irule blockhash_sub_certificate >> simp[mk_inst_def]
QED

Theorem blockhash_compile_certificate:
  compile_blockhash arg sa = (op,sb) /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn'
Proof
  strip_tac >> drule blockhash_compile_code >> strip_tac >>
  irule blockhash_sequence_certificate >>
  simp[mk_inst_def] >> rpt conj_tac >> strip_tac >>
  qpat_x_assum `!x. arg = Var x ==> _` drule >>
  simp[not_fresh_at_def] >>
  disch_then (qspec_then `sa.cs_next_var` mp_tac) >> simp[]
QED

Theorem blockhash_suffix_code:
  compile_blockhash arg sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule compile_blockhash_shape >> strip_tac >>
  drule blockhash_compile_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND] >>
  qexists_tac `l` >>
  REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem blockhash_counted_success:
  compile_blockhash arg sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all blockhash_suffix_code >> strip_tac >>
  `?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn'` by
    (irule blockhash_compile_certificate >> simp[] >>
     qexistsl_tac [`arg`, `op`] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_ptr >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[FILTER_EQ_NIL, EVERY_MEM]) >>
  simp[] >> strip_tac >> goal_assum (drule_at Any)
QED

Theorem blockhash_counted_abort:
  compile_blockhash arg sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?G' tn' j. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all blockhash_suffix_code >> strip_tac >>
  `?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn'` by
    (irule blockhash_compile_certificate >> simp[] >>
     qexistsl_tac [`arg`, `op`] >> simp[]) >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  goal_assum (drule_at Any)
QED
