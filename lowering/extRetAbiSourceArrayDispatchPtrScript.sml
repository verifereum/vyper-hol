(* Actual AbiDynArray F dispatch, factored only at its finite phases. *)
Theory extRetAbiSourceArrayDispatchPtr
Ancestors
  extRetAbiSourceArrayStaticCountedPtr extRetScratchInitPtr extRetAbiArrayInitPtr
  abiEncoder emitHelper compileEnv fragExec words pair
  extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs venomExecSemantics venomState abiDecoderIndexInit
  valueEncodingProps abiStaticAggregateProps arithmetic pred_set
  extRetRobustSourceChildrenPtr representationCleanPtr abiDecoderBulk
  abiEncoderArrayContext abiEncoderArrayPhases abiEncoderArrayCode abiDecoderReentry loweringShapeDefs

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


Theorem source_array_static_suffix_code:
  source_array_static_suffix (Var ip) (Var ev) sa = (out,se) /\
  fn_has_code sa se fn /\ not_fresh_at sa ip /\ not_fresh_at sa ev ==>
  ?old total ov sb sc sd.
    emit_op MLOAD [Var ip] sa = (Var old,sb) /\
    emit_op ADD [Var old;Var ev] sb = (Var total,sc) /\
    emit_void MSTORE [Var ip;Var total] sc = ((),sd) /\
    emit_op MLOAD [Var ip] sd = (Var ov,se) /\ out = Var ov /\
    fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
    fn_has_code sc sd fn /\ fn_has_code sd se fn /\
    not_fresh_at sb ev /\ not_fresh_at sb ip /\
    not_fresh_at sc ip /\ not_fresh_at sd ip /\
    (!p. not_fresh_at sa p ==>
      not_fresh_at sb p /\ not_fresh_at sc p /\ not_fresh_at sd p)
Proof
  simp[source_array_static_suffix_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> rpt strip_tac >>
  rename1 `emit_op MLOAD [Var ip] sa = (oldop,sb)` >>
  rename1 `emit_op ADD [oldop; Var ev] sb = (totalop,sc)` >>
  `?old total ov. oldop = Var old /\ totalop = Var total /\ out = Var ov` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def] >> metis_tac[]) >>
  gvs[] >> rename1 `emit_void MSTORE _ sc = ((),sd)` >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd /\ cs_extends sd se` by
    metis_tac[cj 2 fragExecTheory.cs_appends_emit_helpers,
              cj 3 fragExecTheory.cs_appends_emit_helpers,
              fragExecTheory.cs_appends_def] >>
  `fn_has_code sa sb fn /\ fn_has_code sb se fn` by
    (irule fn_has_code_split >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sb sc fn /\ fn_has_code sc se fn` by
    (irule fn_has_code_split >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sc sd fn /\ fn_has_code sd se fn` by
    (irule fn_has_code_split >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
   sc.cs_next_var <= sd.cs_next_var` by
    gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  simp[] >> rpt strip_tac >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, LESS_EQ_TRANS]
QED

Theorem source_array_static_suffix_counted_ptr:
  source_array_static_suffix (Var ip) (Var ev) sa = (out,se) /\
  fn_has_code sa se fn /\ not_fresh_at sa ip /\ not_fresh_at sa ev /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var ip s = SOME a /\
  ptr_covers G tn ip s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  lookup_var ev s = SOME w /\ op_taint tn (Var ev) = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\
    sf.vs_inst_idx = LENGTH se.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (mload (w2n a) s + w) /\
    op_taint tnf out = {} /\ op_prov Gf out = NONE /\
    sf.vs_memory = (mstore (w2n a) (mload (w2n a) s + w) s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ tnf.t_imm = tn.t_imm /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_call_ctx = s.vs_call_ctx /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all source_array_static_suffix_code >> strip_tac >> gvs[] >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var old) sf = SOME (mload (w2n a) s) /\
   eval_operand (Var ev) sf = SOME w /\ op_taint tnf (Var ev) = {}` by
    simp[eval_operand_def] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `Gf`, `D`] strip_assume_tac) >>
  rename1 `lookup_var sumvar sf' = SOME (mload (w2n a) s + w)` >>
  `lookup_var ip sf' = SOME a /\ ptr_covers Gf' tnf' ip sf' 32 /\
   eval_operand (Var sumvar) sf' = SOME (mload (w2n a) s + w)` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var ip sf'' = SOME a /\ ptr_covers Gf' tnf'' ip sf'' 32 /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tnf''.t_mem)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `lookup_var ov laststate = SOME (mload (w2n a) sf'')` >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gf' tnf'' sf'' 0 lastG lasttn (OK laststate)` >>
  qexistsl_tac [`lastG`, `lasttn`, `laststate`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf''`, `tnf''`] >> simp[]) >>
  `mload (w2n a) sf'' = mload (w2n a) s + w` by
    (qspec_then `w2n a` mp_tac venomMemPropsTheory.mload_mstore_same >>
     disch_then (qspecl_then [`mload (w2n a) s + w`, `sf'`] mp_tac) >>
     simp[mload_def]) >>
  simp[eval_operand_def] >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem source_array_static_prefix_robust_counted_ptr:
  source_array_static_prefix (Var dst) (Var src) sa = ((Var ip,Var cv),sp) /\
  fn_has_code sa sp fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s scap /\ 32 <= scap /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s dcap /\ 32 <= dcap /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) /\
  (w2n a+scap <= addr \/ addr+32 <= w2n a) /\
  (w2n b+dcap <= addr \/ addr+32 <= w2n b) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  LENGTH avs = LENGTH vs /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sp.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sp.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    mload addr sf = 0w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    lookup_var cv sf = SOME (n2w (LENGTH avs)) /\
    op_taint tnf (Var cv) = {} /\ op_prov Gf (Var cv) = NONE /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
    lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap /\
    mem_bytes_at (w2n b) 32 sf.vs_memory = word_to_bytes (n2w (LENGTH avs):bytes32) T /\
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
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    mem_word_at (w2n a) mem' = n2w (LENGTH vs)` by
    (drule robust_dynamic_source_length >> simp[]) >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  `mload (w2n a) s = n2w (LENGTH avs)` by
    (simp[GSYM mem_word_at_eq_mload] >>
     first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all source_array_static_prefix_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac >- simp[abiEncoderMemoryTheory.abi_encoder_word_window] >>
  rpt strip_tac >> irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  conj_tac >- (drule valueTypingMemoryPropsTheory.value_has_type_memory_wf >> simp[]) >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | addr <= i /\ i < addr+32} UNION {i | w2n b <= i /\ i < w2n b+32}`] >>
  simp[loweringPostsTheory.val_footprint_def] >> rpt strip_tac >> decide_tac
QED

Theorem source_array_static_phase_aliases:
  source_array_static_prefix dst src = abi_encode_array_prefix src dst /\
  source_array_static_suffix parent encoded = abi_encode_array_finish parent encoded
Proof
  simp[source_array_static_prefix_init, abi_encode_array_prefix_def,
       source_array_static_suffix_def, abi_encode_array_finish_def]
QED

Theorem source_array_static_dispatch_code:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiDynArray ei asz msz F) sa = (out,se) /\
  fn_has_code sa se fn ==>
  ?ip cv ev sp sl.
    source_array_static_prefix (Var dst) (Var src) sa = ((Var ip,Var cv),sp) /\
    compile_abi_encode_dyn_static_loop (Var dst) (Var src) ei asz msz (Var cv) sp = (Var ev,sl) /\
    source_array_static_suffix (Var ip) (Var ev) sl = (out,se) /\
    fn_has_code sa sp fn /\ fn_has_code sp sl fn /\ fn_has_code sl se fn /\
    sp.cs_next_id = sa.cs_next_id+4 /\ sp.cs_next_var = sa.cs_next_var+2 /\
    sp.cs_next_var <= sl.cs_next_var /\ not_fresh_at sl ev /\
    not_fresh_at sp ip /\ not_fresh_at sp cv /\ not_fresh_at sl ip /\
    (!p. not_fresh_at sa p ==> not_fresh_at sp p /\ not_fresh_at sl p)
Proof
  strip_tac >> drule_all abi_encode_array_context >> simp[] >> strip_tac >>
  `source_array_static_prefix (Var dst) (Var src) sa = (ops,loop_st) /\
   source_array_static_suffix (FST ops) size_op loop_end = (out,se)` by
    metis_tac[source_array_static_phase_aliases] >>
  drule source_array_static_prefix_frontier >> strip_tac >>
  `?ev. size_op = Var ev` by
    (drule abi_encode_array_static_loop_trace >> strip_tac >>
     qpat_x_assum `abi_encode_array_static_exit _ _ _ = _` mp_tac >>
     simp[abi_encode_array_static_exit_def, comp_bind_def] >>
     ntac 2 (pairarg_tac >> simp[]) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`, `ev`, `loop_end`] >>
  simp[] >> conj_tac >- metis_tac[pairTheory.PAIR] >>
  conj_tac >-
    gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  simp[not_fresh_at_def] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.NOT_LESS,
            ASCIInumbersTheory.toString_inj]
QED

Theorem compile_abi_encode_source_dyn_static_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiDynArray ei asz msz F) sa = (out,se) /\
  fn_has_code sa se fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s scap /\ 32 <= scap /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s dcap /\
  evaluate_type env (ArrayT t (Dynamic maxn)) = SOME (ArrayTV tv (Dynamic maxn)) /\
  value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  vyper_to_abi env (ArrayT t (Dynamic maxn)) (ArrayV (DynArrayV vs)) = SOME (contractABI$ListV avs) /\
  ct = vyper_to_abi_type env t /\ ~is_dynamic ct /\
  has_type (Array NONE ct) (contractABI$ListV avs) /\
  asz = abi_member_head_size ct /\ static_length ct = asz /\
  type_memory_size tv = asz /\ msz = type_memory_size tv /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) <= scap /\ LENGTH avs = LENGTH vs /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
  ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  LENGTH (enc (Array NONE ct) (contractABI$ListV avs)) <= dcap /\
  32+LENGTH avs*asz <= dcap /\ LENGTH avs < dimword(:256) /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id = SOME (parent,32) /\
  FLOOKUP (abi_builtin_allocate_state (sa.cs_next_id+4) 32
    (abi_builtin_allocate_state sa.cs_next_id 32 s)).vs_allocas (sa.cs_next_id+4) = SOME (index,32) /\
  parent+32 < dimword(:256) /\ index+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n a+scap <= parent \/ parent+32 <= w2n a) /\
  (w2n b+dcap <= parent \/ parent+32 <= w2n b) /\
  (w2n a+scap <= index \/ index+32 <= w2n a) /\
  (w2n b+dcap <= index \/ index+32 <= w2n b) /\
  (parent+32 <= index \/ index+32 <= parent) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\ sf.vs_inst_idx = LENGTH se.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+LENGTH avs*asz)) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b) (32+LENGTH avs*asz) sf.vs_memory = enc (Array NONE ct) (contractABI$ListV avs) /\
    (!i. w2n b <= i /\ i < w2n b+32+LENGTH avs*asz ==> i NOTIN tnf.t_mem) /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
    lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
    (!site region. FLOOKUP s.vs_allocas site = SOME region ==> FLOOKUP sf.vs_allocas site = SOME region) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+dcap) /\
         ~(parent <= i /\ i < parent+32) /\ ~(index <= i /\ i < index+32) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all source_array_static_dispatch_code >> strip_tac >>
  `32 <= dcap` by decide_tac >>
  drule_all source_array_static_prefix_robust_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  `FLOOKUP (abi_builtin_allocate_state sp.cs_next_id 32 s1).vs_allocas sp.cs_next_id = SOME (index,32)` by
    (drule_all abiBuiltinAllocationTheory.abi_builtin_allocate_state_transport >>
     disch_then (qspecl_then [`sa.cs_next_id+4`,`32`] strip_assume_tac) >> simp[]) >>
  `DISJOINT {i | w2n (n2w parent:bytes32) <= i /\ i < w2n (n2w parent:bytes32)+32}
    ({i | w2n b <= i /\ i < w2n b+dcap} UNION {i | index <= i /\ i < index+32})` by
    (simp[w2n_n2w, DISJOINT_DEF, EXTENSION] >> decide_tac) >>
  `not_fresh_at sp src /\ not_fresh_at sp dst /\
   LENGTH (word_to_bytes (n2w (LENGTH avs):bytes32) T) = 32 /\
   (!i. w2n (n2w parent:bytes32) <= i /\ i < w2n (n2w parent:bytes32)+32 ==> i NOTIN tn1.t_mem)` by
    (simp[w2n_n2w] >> metis_tac[]) >>
  drule_all compile_abi_encode_source_dyn_static_loop_parent_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2)` >>
  `lookup_var ev s2 = SOME (n2w (32+LENGTH avs*asz))` by
    (qpat_x_assum `eval_operand (Var ev) s2 = _` mp_tac >>
     simp[eval_operand_def]) >>
  drule_all source_array_static_suffix_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>

  rename1 `gas_path_ptr D 0 ctx fn PG G2 tn2 s2 0 G3 tn3 (OK s3)` >>
  qexistsl_tac [`G3`,`tn3`,`s3`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`G1`,`s1`,`tn1`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`G2`,`s2`,`tn2`] >> simp[]) >>
  `w2n (n2w parent:bytes32) = parent` by simp[w2n_n2w] >>
  `mload (w2n (n2w parent:bytes32)) s2 = 0w` by asm_rewrite_tac[] >>
  `mem_bytes_at (w2n b) (32+LENGTH avs*asz) s3.vs_memory =
     enc (Array NONE ct) (contractABI$ListV avs)` by
    (`mem_bytes_at (w2n b) (32+LENGTH avs*asz) s3.vs_memory =
      mem_bytes_at (w2n b) (32+LENGTH avs*asz) s2.vs_memory` by
       (qpat_x_assum `s3.vs_memory = _` (fn th => rewrite_tac[th]) >>
        irule mstore_mem_bytes_at_disjoint >>
        qpat_x_assum `w2n (n2w parent:bytes32) = parent` (fn th => rewrite_tac[th]) >>
        decide_tac) >>
     `enc (Array NONE ct) (contractABI$ListV avs) =
        word_to_bytes (n2w (LENGTH avs):bytes32) T ++ FLAT (MAP (enc ct) avs)` by
       (qpat_x_assum `is_static ct` mp_tac >> rpt (pop_assum kall_tac) >>
        metis_tac[static_dynarray_encoding]) >>
     pop_assum mp_tac >>
     qpat_x_assum `mem_bytes_at _ _ s2.vs_memory = _` mp_tac >>
     qpat_x_assum `mem_bytes_at _ _ s3.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `ptr_covers G3 tn3 src s3 scap /\ ptr_covers G3 tn3 dst s3 dcap` by
    (qpat_x_assum `!p. not_fresh_at sa p ==> not_fresh_at sp p /\ _` mp_tac >>
     qpat_x_assum `!p. not_fresh_at sl p ==> _` mp_tac >>
     qpat_x_assum `ptr_covers G2 tn2 src s2 scap` mp_tac >>
     qpat_x_assum `ptr_covers G2 tn2 dst s2 dcap` mp_tac >>
     qpat_x_assum `s3.vs_allocas = s2.vs_allocas` mp_tac >>
     qpat_x_assum `not_fresh_at sa src` mp_tac >>
     qpat_x_assum `not_fresh_at sa dst` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def] >> metis_tac[]) >>
  `!i. ~(parent <= i /\ i < parent+32) ==>
    mem_bytes_at i 1 s3.vs_memory = mem_bytes_at i 1 s2.vs_memory /\
    (i IN tn3.t_mem <=> i IN tn2.t_mem)` by
    (gen_tac >> disch_tac >> conj_tac >-
       (qpat_x_assum `s3.vs_memory = _` (fn th => rewrite_tac[th]) >>
        irule mstore_mem_bytes_at_disjoint >>
        qpat_x_assum `w2n (n2w parent:bytes32) = parent` (fn th => rewrite_tac[th]) >>
        decide_tac) >>
     simp[]) >>

  `!p. not_fresh_at sa p ==>
    lookup_var p s3 = lookup_var p s /\ FLOOKUP G3 p = FLOOKUP G p /\
    op_taint tn3 (Var p) = op_taint tn (Var p)` by
    (qpat_x_assum `!p. not_fresh_at sa p ==> not_fresh_at sp p /\ _` mp_tac >>
     qpat_x_assum `!p. not_fresh_at sa p ==> lookup_var p s1 = _ /\ _` mp_tac >>
     qpat_x_assum `!p. not_fresh_at sp p ==> lookup_var p s2 = _ /\ _` mp_tac >>
     qpat_x_assum `!p. not_fresh_at sl p ==> lookup_var p s3 = _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `lookup_var src s3 = SOME a /\ lookup_var dst s3 = SOME b` by
    (qpat_assum `!p. not_fresh_at sa p ==> lookup_var p s3 = _ /\ _` mp_tac >>
     qpat_x_assum `not_fresh_at sa src` mp_tac >>
     qpat_x_assum `not_fresh_at sa dst` mp_tac >>
     qpat_x_assum `lookup_var src s = _` mp_tac >>
     qpat_x_assum `lookup_var dst s = _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!mem'. mem_agree_outside tn3.t_mem s3.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) (w2n a) mem'` by
    (rpt strip_tac >> irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
     conj_tac >- (drule valueTypingMemoryPropsTheory.value_has_type_memory_wf >> simp[]) >>
     qexistsl_tac [`s2.vs_memory`, `s3.vs_memory`, `tn2.t_mem`, `tn3.t_mem`,
       `{i | parent <= i /\ i < parent+32}`] >>
     simp[loweringPostsTheory.val_footprint_def] >> rpt strip_tac >> decide_tac) >>
  `!site region. FLOOKUP s.vs_allocas site = SOME region ==>
    FLOOKUP s3.vs_allocas site = SOME region` by
    (qpat_x_assum `s3.vs_allocas = s2.vs_allocas` mp_tac >>
     qpat_x_assum `!site region. FLOOKUP s1.vs_allocas site = _ ==> _` mp_tac >>
     qpat_x_assum `s1.vs_allocas = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[] >> first_x_assum irule >>
     gvs[abiBuiltinAllocationTheory.abi_builtin_allocate_state_def] >>
     IF_CASES_TAC >> gvs[] >>
     Cases_on `site = sa.cs_next_id` >> gvs[finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[] >>
  qpat_x_assum `32 <= dcap` mp_tac >>
  qpat_x_assum `mem_agree_outside _ s2.vs_memory s1.vs_memory` mp_tac >>
  qpat_x_assum `!i. ~(parent <= i /\ i < parent+32) /\ _ ==> mem_bytes_at i 1 s1.vs_memory = _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[mem_agree_outside_def] >>
  rpt strip_tac >>
  `~(w2n b <= i /\ i < w2n b+32)` by decide_tac >>
  metis_tac[]
QED


