Theory extRetDynamicArrayInitFramePtr
Ancestors
  extRetRecursiveResourceInitPtr extRetRecursiveResourcePtr
  extRetScratchResourcePtr extRetScratchResourceInitPtr extRetScratchInitPtr
  extRetAbiArrayInitPtr extRetFramedChildPtr
  extRetEvaluatedStaticLoopResourcePtr extRetLoopScalarAmbientPtr
  extRetLoopInitAmbientPtr abiDecoderReentry abiEncoderArrayCode abiDecoderIndexInit
  allocaSiteResource allocaFootprint abiBuiltinAllocation allocationPtr
  localPtrsProps loweringHalt fragExecPtr fragGasPathPtr fragGasSeqPtr
  exprLoweringProps compileEnv emitHelper context codegenRel loweringPosts
  ptrDiscipline bodyPtrDefs venomState venomInst venomExecSemantics
  venomMemProps venomMemDefs valueEncodingProps words finite_map pred_set
  arithmetic list rich_list emitHelperProps fragExec extRetBulkCopyCountedPtr
  extRetBytesCopyCountedPtr typedCopyPtr wordLoadStorePtr loweringStateRelDefs

(* The earlier allocate-state resource lemma is local to its theory.
   This boundary additionally retains exact allocation equality off-site. *)
Theorem encoder_scratch_allocate_exact_state:
  scratch_resource ctx fn sites q len s /\ id IN sites /\
  MEM (mk_inst id ALLOCA [Lit 32w] [ip]) (fn_insts fn) ==>
  ?addr. scratch_resource ctx fn sites q len (abi_builtin_allocate_state id 32 s) /\
    FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas id = SOME (addr,32) /\
    addr+32 < dimword(:256) /\
    s.vs_alloca_next <= (abi_builtin_allocate_state id 32 s).vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> regions_disjoint (q,len) (addr,32)) /\
    (!aid. aid <> id ==> FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas aid =
      FLOOKUP s.vs_allocas aid)
Proof
  strip_tac >>
  mp_tac (Q.INST [`inst` |-> `mk_inst id ALLOCA [Lit 32w] [ip]`, `out` |-> `ip`]
    scratch_resource_alloca) >> simp[mk_inst_def] >> strip_tac >>
  `t.vs_allocas = (abi_builtin_allocate_state id 32 s).vs_allocas /\
   t.vs_alloca_next = (abi_builtin_allocate_state id 32 s).vs_alloca_next` by
    (Cases_on `FLOOKUP s.vs_allocas id` >>
     gvs[exec_alloca_def, mk_inst_def, abi_builtin_allocate_state_def,
         update_var_def, AllCaseEqs(), dimword_def]) >>
  `scratch_resource ctx fn sites q len (abi_builtin_allocate_state id 32 s)` by
    (irule scratch_resource_fields >> qexists_tac `t` >> simp[]) >>
  `b+32 < dimword(:256)` by
    (`alloca_inv t /\ alloca_room ctx fn t` by metis_tac[scratch_resource_def] >>
     drule_all alloca_site_registered_below >>
     drule alloca_room_next_lt >> decide_tac) >>
  `!aid. aid <> id ==> FLOOKUP (abi_builtin_allocate_state id 32 s).vs_allocas aid =
      FLOOKUP s.vs_allocas aid` by
    (gen_tac >> strip_tac >>
     Cases_on `FLOOKUP s.vs_allocas id = NONE` >>
     simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]) >>
  qexists_tac `b` >> metis_tac[]
QED

Theorem encoder_scratch_word_exact_counted_ptr:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; init] sm = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ scratch_resource ctx fn sites q len s /\
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
    scratch_resource ctx fn sites q len sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> regions_disjoint (q,len) (addr,32)) /\
    sf.vs_memory = (mstore addr w s).vs_memory /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    alloca_inv sf /\ sf.vs_labels = s.vs_labels /\
    encoder_ambient_frame tn s tnf sf /\
    (!aid. aid <> sa.cs_next_id ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid)
Proof
  strip_tac >>
  `emit_op ALLOCA [Lit 32w] sa = (buf.buf_operand,sm)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[cj 2 cs_appends_emit_helpers, cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by metis_tac[fn_has_code_split] >>
  `?ip. buf.buf_operand = Var ip /\
    sm.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [ip]]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
     qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> gvs[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [ip]) (fn_insts fn)` by
    (qpat_x_assum `fn_has_code sa sm fn` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [ip]) bb.bb_instructions` by
       gvs[IS_PREFIX_APPEND] >> metis_tac[lookup_block_fn_insts]) >>
  drule_all encoder_scratch_allocate_exact_state >> strip_tac >>
  `emit_op ALLOCA [Lit 32w] sa = (Var ip,sm)` by simp[] >>
  drule_all emit_alloca_index_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `scratch_resource ctx fn sites q len sf` by
    (irule scratch_resource_fields >>
     qexists_tac `abi_builtin_allocate_state sa.cs_next_id 32 s` >> simp[]) >>
  `eval_operand init sf = SOME w /\ op_taint tnf init = {}` by
    (Cases_on `init` >> gvs[eval_operand_def, op_taint_def]) >>
  qpat_x_assum `sm.cs_current_insts = _` kall_tac >>
  gvs[] >> drule_all scratch_store_state_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`addr`, `Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> metis_tac[]) >>
  `addr < dimword(:256)` by decide_tac >>
  `sf'.vs_allocas = sf.vs_allocas /\ sf'.vs_alloca_next = sf.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  `scratch_resource ctx fn sites q len sf'` by
    (irule scratch_resource_fields >> qexists_tac `sf` >> simp[]) >>
  `alloca_inv sf'` by metis_tac[scratch_resource_def] >>
  `sf'.vs_memory = (mstore addr w s).vs_memory` by
    simp[mstore_def, write_memory_with_expansion_def, w2n_n2w, LESS_MOD] >>
  `mload addr sf' = w` by
    (qspecl_then [`addr`, `w`, `s`] mp_tac mload_mstore_same >> simp[mload_def]) >>
  `mem_agree_outside {i | addr <= i /\ i < addr+32} sf'.vs_memory s.vs_memory` by
    metis_tac[mstore_memory_frame] >>
  `ptr_covers Gf tnf' ip sf' 32` by (gvs[ptr_covers_def] >> metis_tac[]) >>
  simp[encoder_ambient_frame_def] >>
  simp[mstore_def, write_memory_with_expansion_def, w2n_n2w, LESS_MOD] >>
  metis_tac[]
QED

Theorem encoder_scratch_init_exact_counted_ptr:
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
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\ mload addr sf = w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> regions_disjoint (q,len) (addr,32)) /\
    (!id b n. MEM (id,b,n) protected /\ n <> 0 ==> regions_disjoint (b,n) (addr,32)) /\
    sf.vs_memory = (mstore addr w s).vs_memory /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    sf.vs_labels = s.vs_labels /\
    encoder_ambient_frame tn s tnf sf /\
    (!aid. aid NOTIN sites ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\ parent <> sa.cs_next_id ==>
      mload p sf = mload p s /\
      ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
       (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem)))
Proof
  strip_tac >>
  `scratch_resource ctx fn sites q len s` by fs[encoder_resource_def] >>
  drule_all encoder_scratch_word_exact_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_registered_intro >> simp[] >>
     fs[encoder_resource_def] >> metis_tac[]) >>
  `!id b n. MEM (id,b,n) protected /\ n <> 0 ==>
    regions_disjoint (b,n) (addr,32)` by
    (rpt gen_tac >> strip_tac >> drule_all encoder_resource_protected >> strip_tac >>
     irule alloca_site_registered_disjoint >> metis_tac[]) >>
  `!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\ parent <> sa.cs_next_id ==>
    mload p sf = mload p s /\
    ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
     (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem))` by
    (rpt gen_tac >> strip_tac >> irule scratch_word_init_registered_cursor >>
     conj_tac >- (gen_tac >> Cases >> simp[] >> metis_tac[]) >>
     simp[] >> qexistsl_tac [`addr`,`sa.cs_next_id`,`parent`,`w`] >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`ip`,`addr`,`Gf`,`tnf`,`sf`] >> simp[] >> metis_tac[]
QED

Theorem encoder_cursor_product_init_exact_counted_ptr:
  emit_op ALLOCA [Lit 32w] sa = (Var cursor,sb) /\
  emit_op MUL [count_op; Lit (n2w stride)] sb = (Var product,sc) /\
  emit_void MSTORE [Var cursor; Var product] sc = ((),sd) /\
  fn_has_code sa sd fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites q len protected s /\
  sa.cs_next_id IN sites /\ eval_operand count_op s = SOME (n2w n) /\
  op_taint tn count_op = {} /\ (!v. count_op = Var v ==> not_fresh_at sa v) ==>
  ?addr Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sd.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var cursor sf = SOME (n2w addr) /\ ptr_covers Gf tnf cursor sf 32 /\
    addr+32 < dimword(:256) /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (addr,32) /\
    mload addr sf = n2w (n*stride) /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    (len <> 0 ==> regions_disjoint (q,len) (addr,32)) /\
    (!id b z. MEM (id,b,z) protected /\ z <> 0 ==> regions_disjoint (b,z) (addr,32)) /\
    sf.vs_memory = (mstore addr (n2w (n*stride)) s).vs_memory /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\ parent <> sa.cs_next_id ==>
      mload p sf = mload p s /\
      ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
       (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem))) /\
    encoder_ambient_frame tn s tnf sf /\
    (!aid. aid <> sa.cs_next_id ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid)
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd` by
    metis_tac[cj 2 cs_appends_emit_helpers, cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sa sc` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn` by (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by (irule fn_has_code_split >> simp[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [cursor]]` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [cursor]) (fn_insts fn)` by
    (qpat_x_assum `fn_has_code sa sb fn` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [cursor]) bb.bb_instructions` by
       gvs[IS_PREFIX_APPEND] >> metis_tac[lookup_block_fn_insts]) >>
  drule_all encoder_index_allocate_resource >> strip_tac >>
  drule_all emit_alloca_index_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `eval_operand count_op sf = SOME (n2w n) /\ op_taint tnf count_op = {}` by
    (Cases_on `count_op` >> gvs[eval_operand_def, op_taint_def]) >>
  `eval_operand (Lit (n2w stride)) sf = SOME (n2w stride) /\
   op_taint tnf (Lit (n2w stride)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_bulk_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `MUL`, `f` |-> `word_mul`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] strip_assume_tac) >>
  `not_fresh_at sb cursor /\ (!v. not_fresh_at sa v ==> not_fresh_at sb v)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `lookup_var cursor sf' = SOME (n2w addr) /\ ptr_covers Gf' tnf' cursor sf' 32 /\
   eval_operand (Var product) sf' = SOME (n2w (n*stride))` by
    (gvs[ptr_covers_def, eval_operand_def, word_mul_n2w] >> metis_tac[]) >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tnf' (OK sf')` by
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  `addr < dimword(:256)` by decide_tac >>
  `sf''.vs_memory = (mstore addr (n2w (n*stride)) s).vs_memory` by
    simp[mstore_def, write_memory_with_expansion_def, w2n_n2w, LESS_MOD] >>
  `encoder_resource ctx fn sites q len protected sf''` by
    (irule encoder_resource_fields >>
     qexists_tac `abi_builtin_allocate_state sa.cs_next_id 32 s` >> simp[]) >>
  `mload addr sf'' = n2w (n*stride)` by metis_tac[mload_def, mload_mstore_same] >>
  `mem_agree_outside {i | addr <= i /\ i < addr+32} sf''.vs_memory s.vs_memory` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `ptr_covers Gf' tnf'' cursor sf'' 32` by (gvs[ptr_covers_def] >> metis_tac[]) >>
  `!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\ parent <> sa.cs_next_id ==>
    mload p sf'' = mload p s /\
    ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
     (!i. p <= i /\ i < p+32 ==> i NOTIN tnf''.t_mem))` by
    (rpt gen_tac >> strip_tac >> irule scratch_word_init_registered_cursor >>
     conj_tac >- (gen_tac >> Cases >> simp[] >> metis_tac[]) >>
     conj_tac >- metis_tac[encoder_resource_def, scratch_resource_def] >>
     qexistsl_tac [`addr`,`sa.cs_next_id`,`parent`,`n2w (n*stride)`] >>
     simp[] >> metis_tac[encoder_resource_def, scratch_resource_def]) >>
  `!aid. aid <> sa.cs_next_id ==> FLOOKUP sf''.vs_allocas aid = FLOOKUP s.vs_allocas aid` by
    (rpt strip_tac >> simp[] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id = NONE` >>
     simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`addr`,`Gf'`,`tnf''`,`sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD, IN_DIFF, encoder_ambient_frame_def] >>
  conj_tac >- (rpt strip_tac >> first_assum irule >> simp[] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!i. i < addr \/ addr+32 <= i ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\ _ ==> _`
    (qspecl_then [`parent`,`p`] mp_tac) >> simp[]
QED

Theorem abi_array_dynamic_init_exact_counted_ptr:
  abi_encode_array_dynamic_init count_op stride sa = ((Var ip,Var cursor),sd) /\
  fn_has_code sa sd fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ encoder_resource ctx fn sites q len protected s /\
  sa.cs_next_id IN sites /\ sa.cs_next_id+2 IN sites /\
  eval_operand count_op s = SOME (n2w n) /\ op_taint tn count_op = {} /\
  (!v. count_op = Var v ==> not_fresh_at sa v) ==>
  ?ia ca Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sd.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w ia) /\ ptr_covers Gf tnf ip sf 32 /\
    lookup_var cursor sf = SOME (n2w ca) /\ ptr_covers Gf tnf cursor sf 32 /\
    ia+32 < dimword(:256) /\ ca+32 < dimword(:256) /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (ia,32) /\
    FLOOKUP sf.vs_allocas (sa.cs_next_id+2) = SOME (ca,32) /\
    mload ia sf = 0w /\ mload ca sf = n2w (n*stride) /\
    (!i. ia <= i /\ i < ia+32 ==> i NOTIN tnf.t_mem) /\
    (!i. ca <= i /\ i < ca+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    s.vs_alloca_next <= sf.vs_alloca_next /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (p,sz)) /\
    mem_agree_outside ({i | ia <= i /\ i < ia+32} UNION
      {i | ca <= i /\ i < ca+32}) sf.vs_memory s.vs_memory /\
    (!i. ~(ia <= i /\ i < ia+32) /\ ~(ca <= i /\ i < ca+32) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    encoder_ambient_frame tn s tnf sf /\
    (!aid. aid NOTIN sites ==> FLOOKUP sf.vs_allocas aid = FLOOKUP s.vs_allocas aid)
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_array_dynamic_init _ _ _ = _` mp_tac >>
  simp[abi_encode_array_dynamic_init_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, compile_alloc_buffer_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_index_init sa = (Var ip,sb)` >>
  rename1 `emit_op ALLOCA [Lit 32w] sb = (Var cursor,sc)` >>
  rename1 `emit_op MUL [count_op; Lit (n2w stride)] sc = (prod,se)` >>
  `?product. prod = Var product` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def, emit_def,
        comp_ignore_bind_def, comp_return_def] >> gvs[] >>
  rename1 `emit_void MSTORE [Var cursor; Var product] se = ((),sd)` >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `cs_extends sa sb` by gvs[cs_extends_def, inst_extends_def] >>
  `cs_extends sb sc /\ cs_extends sc se /\ cs_extends se sd` by
    metis_tac[cj 2 cs_appends_emit_helpers, cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sb sd` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sd fn` by (irule fn_has_code_split >> simp[]) >>
  drule abi_decode_index_init_trace >> strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {} /\
   (!v. Lit 0w = Var v ==> not_fresh_at sa v)` by simp[eval_operand_def, op_taint_def] >>
  drule_all encoder_scratch_init_exact_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >> fs[] >>
  `eval_operand count_op sf = SOME (n2w n) /\ op_taint tnf count_op = {}` by
    (Cases_on `count_op` >> gvs[eval_operand_def, op_taint_def]) >>
  `!v. count_op = Var v ==> not_fresh_at sb v` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `sb.cs_next_id IN sites /\ sf.vs_current_bb = sb.cs_current_bb` by simp[] >>
  drule_all encoder_cursor_product_init_exact_counted_ptr >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] strip_assume_tac) >>
  `not_fresh_at sb ip /\ (!v. not_fresh_at sa v ==> not_fresh_at sb v)` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `lookup_var ip sf' = SOME (n2w addr) /\ ptr_covers Gf' tnf' ip sf' 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `mload addr sf' = 0w /\ (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf'.t_mem)` by
    (qpat_x_assum `!parent p. FLOOKUP sf.vs_allocas parent = SOME (p,32) /\ _ ==> _`
      (qspecl_then [`sa.cs_next_id`,`addr`] mp_tac) >> simp[]) >>
  qexistsl_tac [`addr`,`addr'`,`Gf'`,`tnf'`,`sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  `FLOOKUP sf'.vs_allocas (sa.cs_next_id+2) = SOME (addr',32)` by
    (qpat_x_assum `FLOOKUP sf'.vs_allocas sb.cs_next_id = _` mp_tac >> simp[]) >>
  `mem_agree_outside ({i | addr <= i /\ i < addr+32} UNION
      {i | addr' <= i /\ i < addr'+32}) sf'.vs_memory s.vs_memory` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     qpat_x_assum `mem_agree_outside _ sf'.vs_memory sf.vs_memory`
       (mp_tac o REWRITE_RULE [mem_agree_outside_def]) >>
     disch_then (qspec_then `i` mp_tac) >>
     qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory`
       (mp_tac o REWRITE_RULE [mem_agree_outside_def]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `encoder_ambient_frame tn s tnf' sf'` by metis_tac[encoder_ambient_frame_trans] >>
  `!aid. aid NOTIN sites ==> FLOOKUP sf'.vs_allocas aid = FLOOKUP s.vs_allocas aid` by
    (rpt strip_tac >> `aid <> sb.cs_next_id` by metis_tac[] >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >>
  `i < addr \/ addr+32 <= i` by decide_tac >>
  `i < addr' \/ addr'+32 <= i` by decide_tac >>
  qpat_x_assum `!i. i < addr \/ addr+32 <= i ==> _` (qspec_then `i` mp_tac) >>
  qpat_x_assum `!i. i < addr' \/ addr'+32 <= i ==> _` (qspec_then `i` mp_tac) >> simp[]
QED
