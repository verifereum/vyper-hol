(* Compiler cuts for the actual nonraw bytestring return statement. *)
Theory extRetSingletonStmtPtr
Ancestors
  extRetRawStmtPtr extRetSingletonWordCapacityPtr extRetAbiSingletonReturnPtr
  extRetBufferCursorStatePtr exprOperandVar loweringHalt exprLoweringProps
  emitHelperProps fragExec stmtLowering compileEnv stmtSimReturn loweringPosts rich_list
  vyperTypeArgFits vyperTyping vyperTypeSystem allocationPtr allocaFootprint
  extRetAbiBytesLivePtr abiEncoderInput robustCopyTransportPtr valueEncodingProofs
  words finite_map arithmetic pred_set abiEncoderInputFrame
  extRetBufferStatePtr exprSimOperands venomState venomInst bodyPtrDefs exprLowering emitHelper context
  abiBuiltinAllocation

Theorem external_return_singleton_stmt_parts[local]:
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  fn_has_code sa sb func /\ ~block_is_terminated sa /\
  cenv.ce_return_pc = NONE /\ ~is_word_type ty /\ ~cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e) ==>
  ?op sm buf sn len so.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    compile_alloc_buffer cenv.ce_max_return_size sm = (buf,sn) /\
    compile_abi_encode_to_buf buf.buf_operand op cenv.ce_ret_enc_info sn = (len,so) /\
    emit_inst RETURN [buf.buf_operand;len] [] so = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\
    fn_has_code sn so func /\ fn_has_code so sb func
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule compile_external_return_abi_parts >> simp[] >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule compile_abi_encode_to_buf_extends >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends sb cs'` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sa' cs'` by
    (irule cs_extends_trans >> qexists `sb` >> simp[]) >>
  `cs_extends cs'' cs'` by
    (irule cs_extends_trans >> qexists `sa'` >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code cs'' sa' func /\ fn_has_code sa' cs' func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa' sb func /\ fn_has_code sb cs' func` by
    (irule fn_has_code_split >> simp[]) >>
  metis_tac[]
QED

(* Assignment compatibility, not equality of source and declared types. *)
Theorem external_return_declared_value_typed[local]:
  type_stmt env ty (Return (SOME e)) = SOME env' /\
  env.type_defs = get_tenv cx /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v ==>
  ?tu. evaluate_type (get_tenv cx) ty = SOME tu /\ value_has_type tu v
Proof
  simp[Once type_stmt_def] >> strip_tac >> gvs[] >>
  drule_all type_widens_to_value_has_type >> simp[]
QED

(* Interval form of the pointwise expression allocation invariant. *)
Theorem singleton_source_allocated_interval[local]:
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty ea eb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ fn_inst_ids_distinct fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs = [out] /\
  not_local_ptr cenv es.scopes out /\
  (inst.inst_id < ea.cs_next_id \/ eb.cs_next_id <= inst.inst_id) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  0 < n /\ 0 < val_footprint tv v ==>
  b+n <= w2n w \/ w2n w + val_footprint tv v <= b
Proof
  strip_tac >> spose_not_then assume_tac >>
  `w2n w <= MAX b (w2n w) /\
   MAX b (w2n w) < w2n w + val_footprint tv v` by
    (simp[MAX_DEF] >> decide_tac) >>
  Q.SUBGOAL_THEN
    `inst.inst_id < ea.cs_next_id \/ eb.cs_next_id <= inst.inst_id`
    assume_tac >- simp[] >>
  `~(b <= MAX b (w2n w) /\ MAX b (w2n w) < b+n)` by
    metis_tac[expr_val_at_alloca_disjoint] >>
  gvs[MAX_DEF] >> decide_tac
QED

(* Source provenance and the robust live input survive the destination ALLOCA.
   The source's capacity need not be the declared ABI capacity. *)
Theorem singleton_buffer_source_resources[local]:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ n < dimword(:256) /\ 0 < n /\
  expr_val_at cenv cx ty ea sa es v (Var src) s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_footprint tv v = 32+LENGTH bs /\
  lookup_var src s = SOME (n2w a) /\ a < dimword(:256) /\
  ptr_covers G tn src s (32+LENGTH bs) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_input (AbiBytestring maxlen) at (contractABI$BytesV bs)
      a (32+LENGTH bs) mem) ==>
  ?dst b Gf tnf sf.
    buf.buf_operand = Var dst /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    stmt_state_rel ctx fn cenv cx es sf /\
    lookup_var dst sf = SOME (n2w b) /\ ptr_covers Gf tnf dst sf n /\
    lookup_var src sf = SOME (n2w a) /\
    ptr_covers Gf tnf src sf (32+LENGTH bs) /\
    b+n < dimword(:256) /\
    (b+n <= a \/ a+(32+LENGTH bs) <= b) /\
    (!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
      abi_encoder_input (AbiBytestring maxlen) at (contractABI$BytesV bs)
        a (32+LENGTH bs) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >>
     simp[not_fresh_at_def]) >>
  drule_all compile_alloc_buffer_state_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var src sf = SOME (n2w a) /\
   FLOOKUP Gf src = FLOOKUP G src /\
   op_taint tnf (Var src) = op_taint tn (Var src)` by metis_tac[] >>
  `expr_val_at cenv cx ty ea sa es v (Var src) sf` by
    (qpat_x_assum `!t ea eb v op. _` irule >> simp[eval_operand_def]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    (qpat_x_assum `fn_has_code sa sb fn` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]) bb.bb_instructions` by
       gvs[IS_PREFIX_APPEND] >> metis_tac[lookup_block_fn_insts]) >>
  `addr+n <= a \/ a+(32+LENGTH bs) <= addr` by
    (drule_at (Pat `MEM _ _`)
       (SRULE [mk_inst_def] singleton_source_allocated_interval) >>
     disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ sf`)) >>
     simp[eval_operand_def, LESS_MOD, mk_inst_def] >>
     disch_then drule_all >> simp[]) >>
  `!i. i < 32+LENGTH bs ==>
      (a+i IN tnf.t_mem <=> a+i IN tn.t_mem)` by
    (rpt strip_tac >>
     qpat_x_assum `!i. i < addr \/ _ ==> _` irule >> decide_tac) >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
      abi_encoder_input (AbiBytestring maxlen) at (contractABI$BytesV bs)
        a (32+LENGTH bs) mem` by
    (rpt strip_tac >>
     Q.SUBGOAL_THEN
       `mem_bytes_at a (32+LENGTH bs) sf.vs_memory =
        mem_bytes_at a (32+LENGTH bs) s.vs_memory` assume_tac >- simp[] >>
     drule_all copied_window_agree_witness >> strip_tac >>
     `abi_encoder_input (AbiBytestring maxlen) at (contractABI$BytesV bs)
        a (32+LENGTH bs) mix` by metis_tac[] >>
     drule_all abi_encoder_input_mem_agree >> simp[]) >>
  qexistsl_tac [`ip`, `addr`, `Gf`, `tnf`, `sf`] >>
  simp[] >> gvs[ptr_covers_def, LESS_MOD] >>
  qexistsl_tac [`b`, `sz'`] >> simp[]
QED
