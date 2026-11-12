(* Allocation fields retained on the constructed bytes-encoder witnesses. *)
Theory extRetAbiBytesAllocationPtr
Ancestors
  extRetAbiBytesCountedPtr extRetAbiBytesHeaderPtr extRetBulkCopyCountedPtr abiEncoderBytesCode
  extRetAbiBytesArithPtr venomLayout exprLoweringProps emitHelperProps
  context compileEnv emitHelper venomState ptrDiscipline fragGasSeqPtr
  extRetBytesCopyCountedPtr bodyPtrDefs fragExec fragGasPathPtr words
  venomInst venomExecSemantics ptrSafeRun typedCopyPtr finite_map arithmetic
  abiEncoderInput valueEncoding abiEncoderBytes immutableCopyExecution
  extRetAbiReadCleanPtr abiEncoderInputFrame valueEncodingProps pred_set
  representationCleanPtr valueEncodingProofs robustCopyTransportPtr

Theorem abi_encode_round_allocation_counted_ptr:
  abi_encode_round len sa = (Var out,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ eval_operand len s = SOME (n2w n) /\
  op_taint tn len = {} /\ n <= dimword(:256) - 32 ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (ceil32 n)) /\
    op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_round _ _ = _` mp_tac >>
  simp[abi_encode_round_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  `?v. arg = Var v` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  `cs_extends sa cs' /\ cs_extends cs' sb` by
    (imp_res_tac emit_op_extends >>
     fs[cs_extends_def, same_blocks_def] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code sa cs' fn /\ fn_has_code cs' sb fn` by
    metis_tac[fn_has_code_split] >>
  `eval_operand (Lit 31w) s = SOME 31w /\ op_taint tn (Lit 31w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `eval_operand (Var v) sf = SOME (31w + n2w n) /\
   eval_operand (Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w) sf =
     SOME 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w /\
   op_taint tnf (Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `AND`, `f` |-> `word_and`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `Gf`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at cs' p` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  simp[abi_bytes_round_mask_first] >> metis_tac[]
QED

Theorem abi_encode_bytes_suffix_allocation_counted_ptr:
  abi_encode_bytes_suffix (Var len) sa = (Var out,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var len s = SOME (n2w n) /\
  not_fresh_at sa len /\ op_taint tn (Var len) = {} /\
  n <= dimword(:256) - 32 ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (32 + ceil32 n)) /\
    op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_bytes_suffix _ _ = _` mp_tac >>
  simp[abi_encode_bytes_suffix_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `?v. rounded = Var v` by metis_tac[abi_encode_round_shape] >> gvs[] >>
  `cs_extends sa cs' /\ cs_extends cs' sb` by
    (imp_res_tac abi_encode_round_shape >> imp_res_tac emit_op_extends >>
     gvs[cs_extends_def, inst_extends_def, same_blocks_def]) >>
  `fn_has_code sa cs' fn /\ fn_has_code cs' sb fn` by
    metis_tac[fn_has_code_split] >>
  `eval_operand (Var len) s = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all abi_encode_round_allocation_counted_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `eval_operand (Var v) sf = SOME (n2w (ceil32 n)) /\
   eval_operand (Lit 32w) sf = SOME 32w /\ op_taint tnf (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `Gf`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at cs' p` by
    (imp_res_tac abi_encode_round_shape >> gvs[not_fresh_at_def]) >>
  simp[GSYM word_add_n2w, WORD_ADD_COMM] >> metis_tac[]
QED

Theorem abi_encoder_bytes_header_allocation_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s cap /\
  lookup_var src s = SOME a /\ not_fresh_at sa src /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (LENGTH bs)) /\ op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf src sf cap /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem')
Proof
  strip_tac >>
  `abi_encoder_input (AbiBytestring maxlen) at (BytesV bs)
     (w2n a) cap s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `32 <= cap /\ mem_word_at (w2n a) s.vs_memory = n2w (LENGTH bs)` by
    (gvs[abi_encoder_input_bytes_iff]) >>
  `abi_encoder_read_window (AbiBytestring maxlen) (BytesV bs) (w2n a) (w2n a) 32` by
    simp[abi_encoder_read_window_rules] >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[abi_encoder_read_window_clean] >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  gvs[mload_def, mem_word_at_def] >>
  gvs[ptr_covers_def] >> metis_tac[]
QED

Theorem abi_encode_bytes_prefix_allocation_counted_ptr:
  abi_encode_bytes_prefix (Var dst) (Var src) sa = ((Var len,Var last),sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s (32+ceil32 (LENGTH bs)) /\
  LENGTH bs <= dimword(:256)-32 /\ w2n b + ceil32 (LENGTH bs) < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var len sf = SOME (n2w (LENGTH bs)) /\ op_taint tnf (Var len) = {} /\
    lookup_var last sf = SOME (n2w (w2n b + ceil32 (LENGTH bs))) /\
    ptr_covers Gf tnf last sf 32 /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_bytes_prefix _ _ _ = _` mp_tac >>
  simp[abi_encode_bytes_prefix_def, comp_bind_def, comp_return_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `?v. rounded = Var v` by metis_tac[abi_encode_round_shape] >> gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (Var len,sc1)` >>
  rename1 `abi_encode_round (Var len) sc1 = (Var v,sc2)` >>
  rename1 `emit_op ADD [Var dst; Var v] sc2 = (Var last,sb)` >>
  `cs_extends sa sc1 /\ cs_extends sc1 sc2 /\ cs_extends sc2 sb` by
    (imp_res_tac abi_encode_round_shape >> imp_res_tac emit_op_extends >>
     fs[cs_extends_def, inst_extends_def, same_blocks_def] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code sa sc1 fn /\ fn_has_code sc1 sc2 fn /\ fn_has_code sc2 sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `(!p. not_fresh_at sa p ==> not_fresh_at sc1 p /\ not_fresh_at sc2 p) /\
   not_fresh_at sc1 len /\ not_fresh_at sc2 len` by
    (imp_res_tac abi_encode_round_shape >>
     gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  drule_all abi_encoder_bytes_header_allocation_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var len) sf = SOME (n2w (LENGTH bs))` by simp[eval_operand_def] >>
  drule_all abi_encode_round_allocation_counted_ptr >>
  disch_then (qspecl_then [`PG`, `Gf`, `D`] strip_assume_tac) >>
  `lookup_var dst sf' = SOME b /\
   ptr_covers Gf' tnf' dst sf' (32+ceil32 (LENGTH bs))` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `ceil32 (LENGTH bs) + 32 <= 32 + ceil32 (LENGTH bs) /\
   w2n b + ceil32 (LENGTH bs) < dimword(:256)` by decide_tac >>
  drule_all (abi_bytes_lastptr_ambient_counted_ptr |> Q.INST [`n` |-> `32`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem abi_encode_bytes_copy_allocation_counted_ptr:
  abi_encode_bytes_copy (Var dst) (Var src) (Var len) (Var last) sa = ((),sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa len /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  lookup_var last s = SOME c /\ lookup_var len s = SOME (n2w n) /\
  op_taint tn (Var len) = {} /\ 32+n < dimword(:256) /\
  ptr_covers G tn last s 32 /\ ptr_covers G tn src s (32+n) /\
  ptr_covers G tn dst s (32+n) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (32+n) (mstore (w2n c) 0w s)).vs_memory /\
    tnf.t_mem = ((tn.t_mem DIFF {i | w2n c <= i /\ i < w2n c+32})
      DIFF {i | w2n b <= i /\ i < w2n b+32+n}) UNION
      {w2n b+i | i | i < 32+n /\ w2n a+i IN
        (tn.t_mem DIFF {j | w2n c <= j /\ j < w2n c+32})} /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_bytes_copy _ _ _ _ _ = _` mp_tac >>
  simp[abi_encode_bytes_copy_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
  `?v. copylen = Var v` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  rename1 `emit_void MSTORE [Var last;Lit 0w] sa = ((),sc1)` >>
  rename1 `emit_op ADD [Lit 32w;Var len] sc1 = (Var v,sc2)` >>
  rename1 `emit_void MCOPY [Var dst;Var src;Var v] sc2 = ((),sb)` >>
  `cs_extends sa sc1 /\ cs_extends sc1 sc2 /\ cs_extends sc2 sb` by
    (imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     fs[cs_extends_def, same_blocks_def] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code sa sc1 fn /\ fn_has_code sc1 sc2 fn /\ fn_has_code sc2 sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sc1 p /\ not_fresh_at sc2 p` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var len) sf = SOME (n2w n) /\ op_taint tnf (Var len) = {} /\
   eval_operand (Lit 32w) sf = SOME 32w /\ op_taint tnf (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var src sf' = SOME a /\ lookup_var dst sf' = SOME b /\
   ptr_covers Gf tnf' src sf' (32+n) /\ ptr_covers Gf tnf' dst sf' (32+n) /\
   eval_operand (Var v) sf' = SOME (n2w (32+n))` by
    (gvs[ptr_covers_def, eval_operand_def, word_add_n2w] >> metis_tac[]) >>
  `ptr_covers Gf tnf' src sf' (w2n (n2w (32+n):bytes32)) /\
   ptr_covers Gf tnf' dst sf' (w2n (n2w (32+n):bytes32))` by
    (simp[w2n_n2w, LESS_MOD] >> metis_tac[ADD_COMM]) >>
  drule_all emit_mcopy_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf''`, `sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`G`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf'`, `tnf'`] >> simp[]) >>
  gvs[w2n_n2w, LESS_MOD] >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem compile_abi_encode_bytes_allocation_path_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s (32+ceil32 (LENGTH bs)) /\
  32+LENGTH bs <= cap /\ LENGTH bs <= dimword(:256)-32 /\
  32+ceil32 (LENGTH bs) < dimword(:256) /\
  w2n b + ceil32 (LENGTH bs) < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+ceil32 (LENGTH bs))) /\ op_taint tnf out = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (32+LENGTH bs)
      (mstore (w2n b+ceil32 (LENGTH bs)) 0w s)).vs_memory /\
    tnf.t_mem = ((tn.t_mem DIFF
      {i | w2n b+ceil32 (LENGTH bs) <= i /\ i < w2n b+ceil32 (LENGTH bs)+32})
      DIFF {i | w2n b <= i /\ i < w2n b+32+LENGTH bs}) UNION
      {w2n b+i | i | i < 32+LENGTH bs /\ w2n a+i IN (tn.t_mem DIFF
        {j | w2n b+ceil32 (LENGTH bs) <= j /\ j < w2n b+ceil32 (LENGTH bs)+32})} /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule abi_encode_bytes_trace >> strip_tac >>
  `?len last. ops = (Var len,Var last)` by
    (qpat_x_assum `abi_encode_bytes_prefix _ _ _ = _` mp_tac >>
     simp[abi_encode_bytes_prefix_def, abi_encode_round_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >> gvs[] >>
  `?v. out = Var v` by
    (qpat_x_assum `abi_encode_bytes_suffix _ _ = _` mp_tac >>
     simp[abi_encode_bytes_suffix_def, abi_encode_round_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >> gvs[] >>
  `cs_extends sa ready /\ cs_extends ready copied /\ cs_extends copied sb /\
   (!p. not_fresh_at sa p ==> not_fresh_at ready p /\ not_fresh_at copied p) /\
   not_fresh_at ready len /\ not_fresh_at copied len` by
    (qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` kall_tac >>
     qpat_x_assum `fn_has_code _ _ _` kall_tac >>
     qpat_x_assum `abi_encode_bytes_prefix _ _ _ = _` mp_tac >>
     qpat_x_assum `abi_encode_bytes_copy _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `abi_encode_bytes_suffix _ _ = _` mp_tac >>
     simp[abi_encode_bytes_prefix_def, abi_encode_bytes_copy_def,
          abi_encode_bytes_suffix_def, abi_encode_round_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
          fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     simp[cs_extends_def, not_fresh_at_def] >>
     rpt conj_tac >> rpt strip_tac >> gvs[not_fresh_at_def] >>
     simp[GSYM listTheory.APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa ready fn /\ fn_has_code ready copied fn /\ fn_has_code copied sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `ptr_covers G tn dst s (32+ceil32 (LENGTH bs)) /\
   w2n b + ceil32 (LENGTH bs) < dimword(:256)` by metis_tac[ADD_COMM] >>
  drule_all abi_encode_bytes_prefix_allocation_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
   ptr_covers Gf tnf src sf (32+LENGTH bs) /\
   ptr_covers Gf tnf dst sf (32+LENGTH bs) /\
   32+LENGTH bs < dimword(:256)` by
    (qspec_then `LENGTH (bs:word8 list)` strip_assume_tac abi_bytes_ceil32_gap >>
     gvs[ptr_covers_def] >> decide_tac) >>
  `not_fresh_at ready src /\ not_fresh_at ready dst` by metis_tac[] >>
  drule_all abi_encode_bytes_copy_allocation_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var len sf' = SOME (n2w (LENGTH bs)) /\ op_taint tnf' (Var len) = {}` by
    metis_tac[] >>
  drule_all abi_encode_bytes_suffix_allocation_counted_ptr >>
  disch_then (qspecl_then [`PG`, `Gf'`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]) >>
  gvs[eval_operand_def, w2n_n2w, LESS_MOD] >>
  irule abi_encoder_copy_memory >> irule immutable_mstore_memory_cong >> simp[]
QED


(* Local algebra used by the stronger witness; the old proof's local facts
   are not exported. *)
Theorem bytes_allocation_taint_clean[local]:
  (!i. a <= i /\ i < a+32+l ==> i NOTIN m) /\ l <= r /\ r <= l+32 ==>
  ((m DIFF {i | b+r <= i /\ i < b+r+32}) DIFF
    {i | b <= i /\ i < b+32+l}) UNION
    {b+i | i | i < 32+l /\ a+i IN
      (m DIFF {j | b+r <= j /\ j < b+r+32})} =
  m DIFF {i | b <= i /\ i < b+32+r}
Proof
  strip_tac >>
  `{b+i | i | i < 32+l /\ a+i IN
      (m DIFF {j | b+r <= j /\ j < b+r+32})} = {}` by
    (simp[EXTENSION] >> gen_tac >>
     Cases_on `i < l+32` >> simp[] >>
     `a+i NOTIN m` by (first_x_assum irule >> decide_tac) >> simp[]) >>
  asm_rewrite_tac[] >> simp[EXTENSION] >> gen_tac >> simp[] >>
  Cases_on `x IN m` >> simp[] >> decide_tac
QED

Theorem bytes_allocation_memory_exterior[local]:
  l <= r ==>
  mem_agree_outside {i | b <= i /\ i < b+32+r}
    (mcopy b a (32+l) (mstore (b+r) 0w s)).vs_memory s.vs_memory
Proof
  strip_tac >> simp[mem_agree_outside_def] >> rpt strip_tac >>
  `mem_bytes_at i 1 (mcopy b a (32+l) (mstore (b+r) 0w s)).vs_memory =
   mem_bytes_at i 1 (mstore (b+r) 0w s).vs_memory` by
    (irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  fs[ADD_COMM] >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem bytes_allocation_robust_window[local]:
  mem_bytes_at a cap memf = mem_bytes_at a cap mem /\
  (!i. i < cap ==> (a+i IN mf <=> a+i IN m)) /\
  (!mem'. mem_agree_outside m mem mem' ==>
    abi_encoder_input ei at av a cap mem') ==>
  !mem'. mem_agree_outside mf memf mem' ==>
    abi_encoder_input ei at av a cap mem'
Proof
  rpt strip_tac >> drule_all copied_window_agree_witness >> strip_tac >>
  `abi_encoder_input ei at av a cap mix` by metis_tac[] >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED

Theorem compile_abi_encode_bytes_allocation_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s (32+ceil32 (LENGTH bs)) /\
  32+LENGTH bs <= cap /\ LENGTH bs <= dimword(:256)-32 /\
  32+ceil32 (LENGTH bs) < dimword(:256) /\
  w2n a+cap < dimword(:256) /\ w2n b+32+ceil32 (LENGTH bs) < dimword(:256) /\
  (w2n a+cap <= w2n b \/ w2n b+32+ceil32 (LENGTH bs) <= w2n a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+ceil32 (LENGTH bs))) /\ op_taint tnf out = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (32+LENGTH bs)
      (mstore (w2n b+ceil32 (LENGTH bs)) 0w s)).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)} /\
    (!i. w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs) ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)}
      sf.vs_memory s.vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf dst sf (32+ceil32 (LENGTH bs)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `w2n b+ceil32 (LENGTH bs) < dimword(:256)` by decide_tac >>
  drule_all compile_abi_encode_bytes_allocation_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qspec_then `LENGTH (bs:word8 list)` strip_assume_tac abi_bytes_ceil32_gap >>
  `!i. w2n a <= i /\ i < w2n a+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (`(!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
      (!i. w2n a+32 <= i /\ i < w2n a+32+LENGTH bs ==> i NOTIN tn.t_mem)` by
       (conj_tac
        >- (`!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
                mem_word_at (w2n a) mem' = (n2w (LENGTH bs):bytes32)` by
              gvs[abi_encoder_input_bytes_iff] >>
            drule robust_mem_word_at_clean >> simp[]) >>
        `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
                mem_bytes_at (w2n a+32) (LENGTH bs) mem' = bs` by
          gvs[abi_encoder_input_bytes_iff] >>
        drule robust_mem_bytes_at_clean >> simp[ADD_ASSOC]) >>
     rpt strip_tac >> Cases_on `i < w2n a+32` >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  `tnf.t_mem = tn.t_mem DIFF
    {i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)}` by
    (asm_rewrite_tac[] >> irule bytes_allocation_taint_clean >> simp[]) >>
  `mem_agree_outside {i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)}
      sf.vs_memory s.vs_memory` by
    (asm_rewrite_tac[] >> irule bytes_allocation_memory_exterior >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  asm_rewrite_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  `mem_bytes_at (w2n a) cap sf.vs_memory = mem_bytes_at (w2n a) cap s.vs_memory` by
    (irule listTheory.LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < cap` >>
     `~(w2n b <= w2n a+j /\ w2n a+j < w2n b+32+ceil32 (LENGTH bs))` by decide_tac >>
     `mem_bytes_at (w2n a+j) 1 sf.vs_memory = mem_bytes_at (w2n a+j) 1 s.vs_memory` by
       (gvs[mem_agree_outside_def] >> metis_tac[]) >>
     pop_assum mp_tac >> simp[listTheory.LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `!i. i < cap ==> (w2n a+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)` by
    (rpt strip_tac >> simp[] >> decide_tac) >>
  drule bytes_allocation_robust_window >>
  disch_then assume_tac >>
  qpat_x_assum `tnf.t_mem = _ UNION _` kall_tac >>
  qpat_x_assum `sf.vs_memory = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `tnf.t_mem = _` (fn th => rewrite_tac[GSYM th]) >>
  metis_tac[]
QED

