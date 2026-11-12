Theory extRetLoopInitAmbientPtr
Ancestors
  extRetRecursiveResourceInitPtr extRetRecursiveResourcePtr
  extRetScratchResourceInitPtr extRetScratchResourcePtr extRetScratchInitPtr
  extRetAbiArrayInitPtr extRetAbiSourceArrayDispatchPtr extRetBulkCopyCountedPtr
  extRetBytesCopyCountedPtr allocaSiteResource compileEnv emitHelper fragExec
  fragGasPathPtr fragGasSeqPtr ptrDiscipline bodyPtrDefs venomState venomMemDefs
  venomMemProps venomExecSemantics valueEncodingProps abiStaticAggregateProps
  abiDecoderIndexInit abiDecoderReentry context words finite_map pred_set
  arithmetic list

Theorem encoder_scratch_init_ambient_counted_ptr:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; init] sm = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites q len protected s /\
  sa.cs_next_id IN sites /\ eval_operand init s = SOME w /\ op_taint tn init = {} /\
  (!v. init = Var v ==> not_fresh_at sa v) ==>
  ?ip addr Gf tnf sf.
    buf.buf_operand = Var ip /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    addr+32 < dimword(:256) /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\
    mload addr sf = w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> regions_disjoint (q,len) (addr,32)) /\
    (!id b n. MEM (id,b,n) protected /\ n <> 0 ==>
      regions_disjoint (b,n) (addr,32)) /\
    sf.vs_memory = (mstore addr w s).vs_memory /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\
      parent <> sa.cs_next_id ==>
      mload p sf = mload p s /\
      ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
       (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem))) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `scratch_resource ctx fn sites q len s` by fs[encoder_resource_def] >>
  drule_all scratch_word_init_resource_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_registered_intro >> simp[] >>
     fs[encoder_resource_def] >> metis_tac[]) >>
  `!id b n. MEM (id,b,n) protected /\ n <> 0 ==>
    regions_disjoint (b,n) (addr,32)` by
    (rpt gen_tac >> strip_tac >>
     drule_all encoder_resource_protected >> strip_tac >>
     irule alloca_site_registered_disjoint >> metis_tac[]) >>
  `!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\
    parent <> sa.cs_next_id ==>
    mload p sf = mload p s /\
    ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
     (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem))` by
    (rpt gen_tac >> strip_tac >>
     irule scratch_word_init_registered_cursor >>
     conj_tac >- (gen_tac >> Cases >> simp[] >> metis_tac[]) >>
     simp[] >> qexistsl_tac [`addr`,`sa.cs_next_id`,`parent`,`w`] >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`ip`,`addr`,`Gf`,`tnf`,`sf`] >> simp[] >> metis_tac[]
QED

Theorem abi_decode_index_init_ambient_counted_ptr:
  abi_decode_index_init sa = (Var ip,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    sf.vs_allocas = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas /\
    sf.vs_alloca_next = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next /\
    sf.vs_fmp = (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_fmp /\
    mload addr sf = 0w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    sf.vs_memory = (mstore addr 0w s).vs_memory /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_labels = s.vs_labels
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op ALLOCA _ sa = (Var ip,sc)` >>
  `cs_extends sa sc` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sc sb` by
    metis_tac[cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  drule_all emit_alloca_index_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `eval_operand (Lit 0w) sf = SOME 0w /\ op_taint tnf (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `addr < dimword(:256)` by decide_tac >>
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  `ptr_covers Gf tnf' ip sf' 32` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  `sf'.vs_memory = (mstore addr 0w s).vs_memory` by
    simp[mstore_def, write_memory_with_expansion_def, w2n_n2w, LESS_MOD] >>
  simp[w2n_n2w, LESS_MOD] >>
  conj_tac >-
    (`mload addr sf' = mload addr (mstore addr 0w sf)` by
       gvs[mload_def] >> simp[mload_mstore_same]) >>
  conj_tac >-
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  rpt strip_tac >> simp[IN_DIFF] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem source_array_static_prefix_ambient_counted_ptr:
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
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all source_array_static_prefix_code >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `not_fresh_at sb ip /\
   (!p. not_fresh_at sa p ==> not_fresh_at sb p)` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all abi_decode_index_init_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf scap /\
   lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `ptr_covers Gf tnf src sf 32 /\ ptr_covers Gf tnf dst sf 32` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_MONO_ADD_EQ]) >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tnf.t_mem` by
    (rpt strip_tac >> `i < addr \/ addr+32 <= i` by decide_tac >> metis_tac[]) >>
  `mload (w2n a) sf = mload (w2n a) s` by
    (rewrite_tac[GSYM mem_word_at_eq_mload] >> simp[] >>
     irule mstore_mem_word_at_disjoint >> decide_tac) >>
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
    (rpt strip_tac >>
     qpat_x_assum `sf'.vs_memory = _` (fn th => rewrite_tac[th]) >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
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
