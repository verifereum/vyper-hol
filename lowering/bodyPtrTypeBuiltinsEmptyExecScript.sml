Theory bodyPtrTypeBuiltinsEmptyExec
Ancestors
  bodyPtrTypeBuiltinsEmptyWords bodyPtrTypeBuiltinsEmptyAlloc
  bodyPtrTypeBuiltinsEmptyZero bodyPtrTypeBuiltinsSeq
  builtinSimple emitHelper emitHelperProps exprSimBufferEmptyExec
  compileEnv context venomInst list exprLoweringProps abiEmptySequence rich_list
  fragExec fragGasSeqPtr fragGasPathPtr venomState
  bodyPtrTypeBuiltinsEmptyTail ghostPcTransportPtr instIdxIndep ptrDiscipline
  loweringHalt exprSimAlloc

(* The semantic theory's decomposition is local, so expose this boundary
   for the checked execution port. *)
Theorem empty_buffer_compile_decompose:
  !sz header sa sb buf.
    compile_builtin_empty_complex sz header sa = (buf,sb) ==>
    ?sm. compile_alloc_buffer sz sa = (buf,sm) /\
      (if header then emit_void MSTORE [buf.buf_operand; Lit 0w]
       else compile_zero_words buf.buf_operand ((sz+31) DIV 32)) sm = ((),sb)
Proof
  rpt gen_tac >>
  simp[compile_builtin_empty_complex_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> rename1 `compile_alloc_buffer sz sa = (ba,sm)` >>
  simp[] >> Cases_on `header` >> simp[comp_bind_def, comp_ignore_bind_def,
                                     comp_return_def] >>
  pairarg_tac >> rename1 `_ = (u,st)` >> Cases_on `u` >> simp[] >>
  strip_tac >> gvs[] >> qexists_tac `sm` >> simp[]
QED

Theorem empty_zero_words_no_gas:
  !n pop sa sb. compile_zero_words pop n sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def, emitted_insts_refl] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_zero_words pop n sa` >>
  rename1 `compile_zero_words pop n sa = (unit_result,sm)` >>
  Cases_on `unit_result` >>
  drule_all empty_zero_words_successor_code >> disch_then SUBST1_TAC >>
  simp[mk_inst_def] >> first_x_assum irule >>
  qexists_tac `pop` >> simp[]
QED

Theorem empty_buffer_no_gas:
  !sz header sa sb buf.
    compile_builtin_empty_complex sz header sa = (buf,sb) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >> drule empty_buffer_compile_decompose >> strip_tac >>
  Cases_on `header` >> gvs[]
  >- (gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
      simp[emitted_insts_def, DROP_APPEND1, mk_inst_def]) >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  drule empty_zero_words_no_gas >> strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp_tac (srw_ss()) [Once emitted_insts_def] >>
  qpat_x_assum `inst_extends _ _` mp_tac >>
  simp[inst_extends_def] >> strip_tac >>
  qpat_x_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, EVERY_APPEND,
                   EVERY_DEF, mk_inst_def] >> gvs[mk_inst_def]
QED

Theorem empty_buffer_checked_path:
  !sz header sa sb buf func s t G tn H th D ctx PG.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_ptr D 0 ctx func PG G tn s 0 H th
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  drule empty_buffer_no_gas >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    suspend "code" >>
  drule_all run_inst_seq_gas_path_ptr >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[EVERY_MEM, FILTER_EQ_NIL]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[emitted_insts_def, IS_PREFIX_APPEND] >> simp[]) >> simp[]
QED
Resume empty_buffer_checked_path[code]:
  fs[fn_has_code_def] >>
  gvs[IS_PREFIX_APPEND, emitted_insts_def] >>
  simp[DROP_APPEND1, IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED
Finalise empty_buffer_checked_path

(* Certify the suffix at the cursor actually reached by the prefix.  The
   successful whole run fixes its endpoint before any ghost is chosen. *)
Theorem empty_buffer_prefixed_tail_certificate:
  !header sz sa sb s u t i G tn H th p w D ctx func PG.
    (if header then emit_void MSTORE [Var p; Lit 0w]
     else compile_zero_words (Var p) ((sz+31) DIV 32)) sa = ((),sb) /\
    step_inst_base i s = OK u /\
    inst_seq_ptr D 0 ctx func PG G tn [i] s H th /\
    run_inst_seq (i::emitted_insts sa sb) s = OK t /\
    not_fresh_at sa p /\ lookup_var p u = SOME w /\
    ptr_covers H th p u sz /\ w2n w+sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\ ~ctx_has_dalloca ctx ==>
    ?K tk. inst_seq_ptr D 0 ctx func PG G tn
        (i::emitted_insts sa sb) s K tk /\
      lookup_var p t = SOME w /\ ptr_covers K tk p t sz /\
      tk.t_mem = th.t_mem DIFF
        {a | w2n w <= a /\ a < w2n w+(if header then 32 else sz)} /\
      tk.t_stor = th.t_stor /\ tk.t_trans = th.t_trans /\ tk.t_imm = th.t_imm /\
      t.vs_call_ctx = u.vs_call_ctx /\ t.vs_accounts = u.vs_accounts /\
      t.vs_transient = u.vs_transient /\
      (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q u /\
        FLOOKUP K q = FLOOKUP H q /\ op_taint tk (Var q) = op_taint th (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\j. ~is_terminator j.inst_opcode) (emitted_insts sa sb)` by
    suspend "shape" >>
  `run_inst_seq (emitted_insts sa sb) u = OK t` by
    gvs[run_inst_seq_def] >>
  `?v K tk. run_inst_seq (emitted_insts sa sb)
      (u with vs_inst_idx := SUC s.vs_inst_idx) = OK v /\
    inst_seq_ptr D 0 ctx func PG H th (emitted_insts sa sb)
      (u with vs_inst_idx := SUC s.vs_inst_idx) K tk /\
    lookup_var p v = SOME w /\ ptr_covers K tk p v sz /\
    tk.t_mem = th.t_mem DIFF
      {a | w2n w <= a /\ a < w2n w+(if header then 32 else sz)} /\
    tk.t_stor = th.t_stor /\ tk.t_trans = th.t_trans /\ tk.t_imm = th.t_imm /\
    v.vs_call_ctx = u.vs_call_ctx /\ v.vs_accounts = u.vs_accounts /\
    v.vs_transient = u.vs_transient /\
    (!q. not_fresh_at sa q ==> lookup_var q v = lookup_var q u /\
      FLOOKUP K q = FLOOKUP H q /\ op_taint tk (Var q) = op_taint th (Var q))` by
    suspend "tail" >>
  `v = t with vs_inst_idx := SUC s.vs_inst_idx` by
    (drule run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`u`, `SUC s.vs_inst_idx`] mp_tac) >>
     simp[exec_result_map_def]) >>
  gvs[] >>
  rename1 `ptr_covers finalG finaltn p t sz` >>
  qexistsl_tac [`finalG`, `finaltn`] >>
  gvs[inst_seq_ptr_def, lookup_var_def]
QED
Resume empty_buffer_prefixed_tail_certificate[shape]:
  Cases_on `header` >> gvs[]
  >- (gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
          comp_return_def, emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def,
          is_terminator_def]) >>
  metis_tac[empty_zero_words_nonterminators]
QED
Resume empty_buffer_prefixed_tail_certificate[tail]:
  `lookup_var p (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w` by
    fs[lookup_var_def] >>
  `ptr_covers H th p (u with vs_inst_idx := SUC s.vs_inst_idx) sz` by simp[] >>
  qpat_x_assum `lookup_var p u = _` kall_tac >>
  qpat_x_assum `ptr_covers H th p u sz` kall_tac >>
  drule_all empty_buffer_tail_certificate >>
  disch_then (qspecl_then [`D`, `func`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t'`, `H'`, `th'`] >>
  gvs[lookup_var_def, venom_state_component_equality]
QED
Finalise empty_buffer_prefixed_tail_certificate

Theorem empty_buffer_compile_prefix:
  !sz header sa sb buf func.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func ==>
    ?sm p. compile_alloc_buffer sz sa = (buf,sm) /\
      buf.buf_operand = Var p /\ not_fresh_at sm p /\
      (if header then emit_void MSTORE [Var p; Lit 0w]
       else compile_zero_words (Var p) ((sz+31) DIV 32)) sm = ((),sb) /\
      fn_has_code sa sm func /\
      emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]] /\
      emitted_insts sa sb =
        mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p] :: emitted_insts sm sb
Proof
  rpt gen_tac >> strip_tac >>
  drule empty_buffer_compile_decompose >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `inst_extends sm sb /\ sb.cs_blocks = sm.cs_blocks /\
    sb.cs_current_bb = sm.cs_current_bb` by suspend "tail" >>
  qexistsl_tac [`sm`, `STRING #"%" (toString sa.cs_next_var)`] >>
  gvs[] >> rpt conj_tac
  >- suspend "code"
  >- simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  gvs[inst_extends_def] >>
  simp_tac (srw_ss()) [Once emitted_insts_def] >>
  qpat_x_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >> REFL_TAC
QED
Resume empty_buffer_compile_prefix[tail]:
  Cases_on `header` >> gvs[]
  >- (drule inst_extends_emit_void >> strip_tac >> simp[] >>
      gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def]) >>
  metis_tac[abi_empty_zero_words_shape]
QED
Resume empty_buffer_compile_prefix[code]:
  fs[fn_has_code_def, inst_extends_def, emitted_blocks_def] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]
QED
Finalise empty_buffer_compile_prefix

Theorem empty_buffer_run_certificate:
  !sz header sa sb buf func cenv cx es s t ctx D PG G tn.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?p w H th. buf.buf_operand = Var p /\ lookup_var p t = SOME w /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th /\
      ptr_covers H th p t sz /\
      (!a. w2n w <= a /\ a < w2n w+(if header then 32 else sz) ==>
        a NOTIN th.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_buffer_compile_prefix >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule_all empty_alloc_checked_coverage >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] strip_assume_tac) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s = OK u` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `lookup_var p u = SOME w` by gvs[eval_operand_def] >>
  gvs[] >>
  `w2n w+sz < dimword (:256)` by decide_tac >>
  drule_all empty_buffer_prefixed_tail_certificate >> strip_tac >>
  rename1 `ptr_covers finalG finaltn p t sz` >>
  qexistsl_tac [`w`, `finalG`, `finaltn`] >> gvs[]
QED
