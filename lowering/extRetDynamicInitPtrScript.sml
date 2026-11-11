Theory extRetDynamicInitPtr
Ancestors
  abiEncoderArrayCode abiDecoderIndexInit context
  extRetEvaluatedStaticLoopResourcePtr extRetRecursiveResourcePtr
  extRetAbiArrayInitPtr extRetLoopScalarAmbientPtr extRetBulkCopyCountedPtr
  extRetScratchInitPtr extRetScratchResourcePtr extRetLoopInitAmbientPtr
  fragGasPathPtr fragExec emitHelperProps exprLoweringProps emitHelper compileEnv
  ptrDiscipline bodyPtrDefs venomState venomExecSemantics venomInst
  venomMemDefs venomMemProps valueEncodingProps codegenRel
  abiDecoderReentry words finite_map pred_set arithmetic list rich_list

(* Unlike a contiguous scratch initializer, MUL really occurs between allocation
   and store.  This boundary does not assume that the allocation site is fresh. *)
Theorem encoder_cursor_product_init_counted_ptr:
  emit_op ALLOCA [Lit 32w] sa = (Var cursor,sb) /\
  emit_op MUL [count_op; Lit (n2w stride)] sb = (Var product,sc) /\
  emit_void MSTORE [Var cursor; Var product] sc = ((),sd) /\
  fn_has_code sa sd fn /\
  s.vs_current_bb = sa.cs_current_bb /\
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
    (!id b z. MEM (id,b,z) protected /\ z <> 0 ==>
      regions_disjoint (b,z) (addr,32)) /\
    sf.vs_memory = (mstore addr (n2w (n*stride)) s).vs_memory /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\
      parent <> sa.cs_next_id ==>
      mload p sf = mload p s /\
      ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
       (!i. p <= i /\ i < p+32 ==> i NOTIN tnf.t_mem))) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd` by
    metis_tac[cj 2 cs_appends_emit_helpers, cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sa sc` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    (irule fn_has_code_split >> simp[]) >>
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
  `not_fresh_at sb cursor /\
   (!v. not_fresh_at sa v ==> not_fresh_at sb v)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
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
  `mload addr sf'' = n2w (n*stride)` by
    metis_tac[mload_def, mload_mstore_same] >>
  `mem_agree_outside {i | addr <= i /\ i < addr+32} sf''.vs_memory s.vs_memory` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `ptr_covers Gf' tnf'' cursor sf'' 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\
    parent <> sa.cs_next_id ==>
    mload p sf'' = mload p s /\
    ((!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
     (!i. p <= i /\ i < p+32 ==> i NOTIN tnf''.t_mem))` by
    (rpt gen_tac >> strip_tac >>
     irule scratch_word_init_registered_cursor >>
     conj_tac >- (gen_tac >> Cases >> simp[] >> metis_tac[]) >>
     conj_tac >- metis_tac[encoder_resource_def, scratch_resource_def] >>
     qexistsl_tac [`addr`,`sa.cs_next_id`,`parent`,`n2w (n*stride)`] >>
     simp[] >> metis_tac[encoder_resource_def, scratch_resource_def]) >>
  qexistsl_tac [`addr`,`Gf'`,`tnf''`,`sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD, IN_DIFF] >>
  conj_tac >- (rpt strip_tac >> first_assum irule >> simp[] >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!i. i < addr \/ addr+32 <= i ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!parent p. FLOOKUP s.vs_allocas parent = SOME (p,32) /\ _ ==> _`
    (qspecl_then [`parent`,`p`] mp_tac) >> simp[]
QED

Theorem abi_array_dynamic_init_resource_ambient_counted_ptr:
  abi_encode_array_dynamic_init count_op stride sa = ((Var ip,Var cursor),sd) /\
  fn_has_code sa sd fn /\
  s.vs_current_bb = sa.cs_current_bb /\
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
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
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
  `fn_has_code sa sb fn /\ fn_has_code sb sd fn` by
    (irule fn_has_code_split >> simp[]) >>
  drule_all encoder_index_init_resource_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `eval_operand count_op sf = SOME (n2w n) /\ op_taint tnf count_op = {}` by
    (Cases_on `count_op` >> gvs[eval_operand_def, op_taint_def]) >>
  `!v. count_op = Var v ==> not_fresh_at sb v` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  drule_all encoder_cursor_product_init_counted_ptr >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] strip_assume_tac) >>
  cheat
QED
