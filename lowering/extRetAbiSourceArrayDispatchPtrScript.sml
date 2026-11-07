(* Actual AbiDynArray F dispatch, factored only at its finite phases. *)
Theory extRetAbiSourceArrayDispatchPtr
Ancestors
  extRetAbiSourceArrayStaticCountedPtr extRetScratchInitPtr extRetAbiArrayInitPtr
  abiEncoder emitHelper compileEnv fragExec words pair
  extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs venomExecSemantics venomState abiDecoderIndexInit
  valueEncodingProps abiStaticAggregateProps arithmetic pred_set

Definition source_array_static_prefix_def:
  source_array_static_prefix dst src =
    do parent <- compile_alloc_buffer 32;
       emit_void MSTORE [parent.buf_operand; Lit 0w];
       count <- emit_op MLOAD [src];
       emit_void MSTORE [dst; count];
       return (parent.buf_operand,count)
    od
End

Definition source_array_static_suffix_def:
  source_array_static_suffix parent encoded =
    do old <- emit_op MLOAD [parent];
       total <- emit_op ADD [old; encoded];
       emit_void MSTORE [parent; total];
       emit_op MLOAD [parent]
    od
End

Theorem compile_abi_encode_dyn_static_phases:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz F) =
    do ops <- source_array_static_prefix dst src;
       encoded <- compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops);
       source_array_static_suffix (FST ops) encoded
    od
Proof
  simp[Once compile_abi_encode_child_def,
       source_array_static_prefix_def, source_array_static_suffix_def,
       comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> ntac 4 (pairarg_tac >> simp[])
QED

Theorem compile_abi_encode_dyn_static_trace:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz F) sa = (out,se) ==>
  ?ops sp encoded sl.
    source_array_static_prefix dst src sa = (ops,sp) /\
    compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops) sp = (encoded,sl) /\
    source_array_static_suffix (FST ops) encoded sl = (out,se)
Proof
  simp[compile_abi_encode_dyn_static_phases, comp_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> rpt strip_tac >> metis_tac[]
QED

Theorem source_array_static_prefix_trace:
  source_array_static_prefix dst src sa = (ops,sp) ==>
  ?buf s1 s2 count s3.
    compile_alloc_buffer 32 sa = (buf,s1) /\
    emit_void MSTORE [buf.buf_operand; Lit 0w] s1 = ((),s2) /\
    emit_op MLOAD [src] s2 = (count,s3) /\
    emit_void MSTORE [dst; count] s3 = ((),sp) /\
    ops = (buf.buf_operand,count)
Proof
  simp[source_array_static_prefix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem source_array_static_prefix_frontier:
  source_array_static_prefix dst src sa = (ops,sp) ==>
  FST ops = Var (STRING #"%" (toString sa.cs_next_var)) /\
  SND ops = Var (STRING #"%" (toString (sa.cs_next_var+1))) /\
  sp.cs_next_id = sa.cs_next_id+4 /\ sp.cs_next_var = sa.cs_next_var+2 /\
  sp.cs_current_bb = sa.cs_current_bb /\ sp.cs_blocks = sa.cs_blocks
Proof
  simp[source_array_static_prefix_def, contextTheory.compile_alloc_buffer_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

(* The two instructions following parent-cursor initialization. *)
Theorem source_array_header_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var cv,sb) /\
  emit_void MSTORE [Var dst; Var cv] sb = ((),sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sc.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var cv sf = SOME (mload (w2n a) s) /\
    op_taint tnf (Var cv) = {} /\ op_prov Gf (Var cv) = NONE /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Var cv) sf = SOME (mload (w2n a) s)` by
    simp[eval_operand_def] >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  metis_tac[]
QED

Theorem source_array_static_prefix_init:
  source_array_static_prefix dst src =
    do parent <- abi_decode_index_init;
       count <- emit_op MLOAD [src];
       emit_void MSTORE [dst;count];
       return (parent,count)
    od
Proof
  simp[source_array_static_prefix_def, abi_decode_index_init_def,
       comp_bind_assoc, comp_ignore_bind_def] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> ntac 4 (pairarg_tac >> simp[])
QED

Theorem source_array_scratch_frame_mload[local]:
  mem_agree_outside {i | p <= i /\ i < p+32} sf.vs_memory s.vs_memory /\
  (a+32 <= p \/ p+32 <= a) ==>
  mload a sf = mload a s
Proof
  strip_tac >>
  `mem_bytes_at a 32 sf.vs_memory = mem_bytes_at a 32 s.vs_memory` by
    (irule listTheory.LIST_EQ >> simp[valueEncodingProofsTheory.EL_mem_bytes_at] >>
     rpt strip_tac >>
     `mem_bytes_at (a+x) 1 sf.vs_memory = mem_bytes_at (a+x) 1 s.vs_memory` by
       (qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
        simp[mem_agree_outside_def] >> strip_tac >> first_x_assum irule >>
        simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >>
     simp[valueEncodingProofsTheory.EL_mem_bytes_at]) >>
  metis_tac[valueEncodingPropsTheory.mem_word_at_eq_mload,
            abiStaticAggregatePropsTheory.mem_word_at_bytes]
QED

Theorem source_array_static_prefix_code:
  source_array_static_prefix (Var dst) (Var src) sa = ((Var ip,Var cv),sd) /\
  fn_has_code sa sd fn ==>
  ?sb sc.
    abi_decode_index_init sa = (Var ip,sb) /\
    emit_op MLOAD [Var src] sb = (Var cv,sc) /\
    emit_void MSTORE [Var dst;Var cv] sc = ((),sd) /\
    fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn
Proof
  simp[source_array_static_prefix_init, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  rename1 `abi_decode_index_init sa = (Var ip,sb)` >>
  rename1 `emit_op MLOAD [Var src] sb = (Var cv,sc)` >>
  rename1 `emit_void MSTORE [Var dst;Var cv] sc = ((),sd)` >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd` by
    (rpt conj_tac >-
       (drule abi_decode_index_init_shape >>
        simp[emitHelperPropsTheory.inst_extends_def] >> rpt strip_tac >>
        irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
     metis_tac[cj 2 fragExecTheory.cs_appends_emit_helpers,
               cj 3 fragExecTheory.cs_appends_emit_helpers,
               fragExecTheory.cs_appends_def]) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sd fn` by
    (irule fn_has_code_split >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sb sc fn /\ fn_has_code sc sd fn` by
    (irule fn_has_code_split >> simp[]) >>
  metis_tac[]
QED

Theorem source_array_static_prefix_counted_ptr:
  source_array_static_prefix (Var dst) (Var src) sa = ((Var ip,Var cv),sd) /\
  fn_has_code sa sd fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s scap /\ 32 <= scap /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s dcap /\ 32 <= dcap /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) /\
  (w2n a+scap <= addr \/ addr+32 <= w2n a) /\
  (w2n b+dcap <= addr \/ addr+32 <= w2n b) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sd.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    mload addr sf = 0w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    lookup_var cv sf = SOME (mload (w2n a) s) /\
    op_taint tnf (Var cv) = {} /\ op_prov Gf (Var cv) = NONE /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
    lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap /\
    mem_word_at (w2n b) sf.vs_memory = mload (w2n a) s /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
    sf.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
    sf.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
    sf.vs_fmp = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_fmp /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!i. ~(addr <= i /\ i < addr+32) /\ ~(w2n b <= i /\ i < w2n b+32) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all source_array_static_prefix_code >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `not_fresh_at sb ip /\
   (!p. not_fresh_at sa p ==> not_fresh_at sb p)` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all abi_decode_index_init_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
   lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `ptr_covers Gf tnf src sf 32 /\ ptr_covers Gf tnf dst sf 32` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_MONO_ADD_EQ]) >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tnf.t_mem` by
    (rpt strip_tac >> `i < addr \/ addr+32 <= i` by decide_tac >> metis_tac[]) >>
  `mload (w2n a) sf = mload (w2n a) s` by
    (irule source_array_scratch_frame_mload >> qexists_tac `addr` >> simp[] >> decide_tac) >>
  `not_fresh_at sb dst` by metis_tac[] >>
  drule_all source_array_header_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var ip sf' = SOME (n2w addr) /\ ptr_covers Gf' tnf' ip sf' 32 /\
   lookup_var src sf' = SOME a /\ ptr_covers Gf' tnf' src sf' scap /\
   lookup_var dst sf' = SOME b /\ ptr_covers Gf' tnf' dst sf' dcap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `mload addr sf' = 0w` by
    (rewrite_tac[GSYM mem_word_at_eq_mload] >>
     simp[] >> irule EQ_TRANS >>
     qexists_tac `mem_word_at addr sf.vs_memory` >>
     reverse conj_tac >- simp[mem_word_at_eq_mload] >>
     irule mstore_mem_word_at_disjoint >> decide_tac) >>
  `!i. ~(w2n b <= i /\ i < w2n b+32) ==>
    mem_bytes_at i 1 sf'.vs_memory = mem_bytes_at i 1 sf.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `!i. ~(addr <= i /\ i < addr+32) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tnf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> `i < addr \/ addr+32 <= i` by decide_tac >>
     qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
     simp[mem_agree_outside_def] >> metis_tac[]) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[mstore_mem_word_at_same, IN_DIFF] >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

