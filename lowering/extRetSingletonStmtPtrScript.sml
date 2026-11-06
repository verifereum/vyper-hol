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
  abiBuiltinAllocation extRetAbiSingletonWrapperPtr abiEncoderComplexPrefix
  abiEncoder fragGasPathPtr abiEncoderComplexCode extRetNormalEvidencePtr
  extRetSomeComposePtr typedCopyPtr extRetStaticStmtPtr vyperValue vyperArith vyperTypeABI venomLayout
  extRetAbiSourceInputPtr vfmConstants abiBytesExecution representationCleanPtr valueEncoding valueEncodingTyping

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
Theorem singleton_buffer_return_suffix[local]:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb fn /\
  compile_abi_encode_to_buf buf.buf_operand (Var src)
    (AbiComplex [(AbiBytestring maxlen,32,cap,T)]) sb = (out,sc) /\
  emit_inst RETURN [buf.buf_operand;out] [] sc = (u,sd) /\
  fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
  64+ceil32 (LENGTH bs) <= n /\ 32+LENGTH bs <= cap /\
  LENGTH bs <= dimword(:256)-32 /\
  32+ceil32 (LENGTH bs) < dimword(:256) /\
  a+(32+LENGTH bs) < dimword(:256) /\ stor_taint_ok cx tn s /\
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
  ?Gf tnf t.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 Gf tnf (Halt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >>
     simp[not_fresh_at_def]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qpat_assum `buf.buf_operand = _` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_all abi_singleton_wrapper_context >> strip_tac >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sb.cs_next_var)]) (fn_insts fn)` by
    (qpat_x_assum `abi_encode_complex_prefix _ _ = _` mp_tac >>
     simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >>
     qpat_x_assum `fn_has_code sb _ fn` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     `MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sb.cs_next_var)]) bb.bb_instructions` by
       gvs[IS_PREFIX_APPEND] >>
     metis_tac[lookup_block_fn_insts]) >>
  drule_all (Q.INST [`used` |-> `64+ceil32 (LENGTH bs)`]
    compile_alloc_buffer_cursor_state_counted_ptr) >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `cx_dead cx`]
    (qx_choose_then `ip'` (qx_choose_then `addr` (qx_choose_then `Gf`
      (qx_choose_then `tnf` (qx_choose_then `sf`
        (map_every assume_tac o CONJUNCTS))))))) >>
  qpat_x_assum `?cursor. _` (qx_choose_then `cursor` (map_every assume_tac o CONJUNCTS)) >>
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
  Q.SUBGOAL_THEN `addr+n <= a \/ a+(32+LENGTH bs) <= addr` assume_tac
  >- (drule_at (Pat `MEM _ _`)
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
  `ip' = STRING #"%" (toString sa.cs_next_var)` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `not_fresh_at sb src /\ not_fresh_at sb ip'` by metis_tac[] >>
  `ptr_covers Gf tnf src sf (32+LENGTH bs)` by
    (qpat_x_assum `ptr_covers G tn src s _` mp_tac >>
     gvs[ptr_covers_def, LESS_MOD] >> rpt strip_tac >>
     qexistsl_tac [`b`, `sz'`] >> simp[]) >>
  `ptr_covers Gf tnf ip' sf (64+ceil32 (LENGTH bs))` by
    (qpat_assum `ptr_covers Gf tnf ip' sf n` mp_tac >>
     rewrite_tac[ptr_covers_def] >> strip_tac >>
     conj_tac >- simp[] >>
     qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >> decide_tac) >>
  Q.SUBGOAL_THEN
    `cursor+32 <= a \/ a+(32+LENGTH bs) <= cursor` assume_tac
  >- (qpat_x_assum `!ty ea eb v op tv w. _` mp_tac >>
      disch_then (qspecl_then [`ty`, `ea`, `sa`, `v`, `Var src`, `tv`, `n2w a`] mp_tac) >>
      simp[eval_operand_def, LESS_MOD]) >>
  `stor_taint_ok cx tnf sf` by
    fs[stor_taint_ok_def] >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem` by
    (rpt strip_tac >> irule abi_encoder_input_capacity >>
     qexists_tac `32+LENGTH bs` >> simp[]) >>
  `addr+64+ceil32 (LENGTH bs) < dimword(:256)` by decide_tac >>
  Q.SUBGOAL_THEN
    `cursor+32 <= addr \/ addr+64+ceil32 (LENGTH bs) <= cursor` assume_tac
  >- decide_tac >>
  Q.SUBGOAL_THEN
    `a+(32+LENGTH bs) <= addr \/ addr+64+ceil32 (LENGTH bs) <= a` assume_tac
  >- decide_tac >>
  qpat_x_assum `ip' = _` SUBST_ALL_TAC >>
  drule_all compile_abi_encode_singleton_bytes_live_return_counted_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `t`] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]
QED

Theorem external_return_singleton_bytes_stmt_frag_ptr:
  cenv.ce_return_pc = NONE /\ ~cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\ k <= n /\
  is_bytestring_type (lowered_value_type cenv e) /\
  cenv.ce_ret_enc_info = AbiComplex [(AbiBytestring n,32,cap,T)] /\
  32+n <= cap /\ 64+ceil32 n <= cenv.ce_max_return_size /\
  cenv.ce_max_return_size < dimword(:256) /\
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  expr_sim_ptr d ctx PG func cenv cx (BaseT (BytesT (Dynamic n))) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx (BaseT (BytesT (Dynamic n))) (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> rw[stmt_frag_ptr_def] >>
  drule external_return_singleton_stmt_parts >>
  simp[is_word_type_def, is_bytestring_type_def] >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) compile_lower_value_var >>
  simp[] >> disch_then assume_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule gas_outcome_ptr_normal_evidence >> strip_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    external_return_some_outcome_ptr >>
  disch_then irule >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule expr_post_ptr_return_inputs >> simp[] >> disch_then drule_all >> strip_tac >>
  `n <= ceil32 n` by simp[ceil32_ge] >>
  `k < dimword(:256)` by decide_tac >>
  `type_slot_size (BaseTV (BytesT (Dynamic k))) <= dimword(:256)` by
    (Cases_on `k = 0` >- simp[type_slot_size_def, word_size_def, dimword_def] >>
     `word_size k <= k` by (irule word_size_le >> decide_tac) >>
     simp[type_slot_size_def] >> decide_tac) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic k)))` by
    simp[evaluate_type_def] >>
  drule_all external_return_forced_value_typed >> strip_tac >>
  `?bs. v = BytesV bs` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `LENGTH bs <= k` by fs[vyperTypingTheory.value_has_type_def] >>
  `ceil32 (LENGTH bs) <= ceil32 n` by
    (simp[abi_bytes_ceil32_eq] >> irule ceil32_mono >> decide_tac) >>
  `val_footprint (BaseTV (BytesT (Dynamic k))) (BytesV bs) = 32+LENGTH bs` by
    simp[val_footprint_def] >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic k))) sa sm ee (BytesV bs) op t` by
    gvs[expr_post_def] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) expr_val_at_bound >>
  simp[is_word_type_def] >> disch_then drule_all >> strip_tac >>
  `val_footprint (BaseTV (BytesT (Dynamic k))) (BytesV bs) <> 0 /\
   32+LENGTH bs <= val_footprint (BaseTV (BytesT (Dynamic k))) (BytesV bs)` by simp[] >>
  drule ptr_val_ok_read_covers >> simp[is_word_type_def] >>
  disch_then (qspec_then `32+LENGTH bs` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  `val_wf (BaseTV (BytesT (Dynamic k))) (BytesV bs)` by
    metis_tac[value_has_type_val_wf] >>
  `k < dimword(:256)` by decide_tac >>
  drule ptr_val_ok_bytes_abi_input >>
  disch_then (qspec_then `w` mp_tac) >> simp[] >> disch_then assume_tac >>
  `!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
    abi_encoder_input (AbiBytestring n) (Bytes NONE) (contractABI$BytesV bs)
      (w2n w) (32+LENGTH bs) mem` by
    (rpt strip_tac >>
     qpat_x_assum `!mem'. mem_agree_outside _ _ _ ==> _` drule >>
     simp[abi_encoder_input_bytes_iff] >> decide_tac) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[cs_extends_def]) >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) singleton_buffer_return_suffix >>
  disch_then irule >>
  simp[] >>
  `0 < cenv.ce_max_return_size` by decide_tac >> simp[] >>
  qexistsl_tac [`w2n w`, `Bytes NONE`, `bs`, `cap`, `cenv`, `sa`, `ee`,
    `n`, `len`, `so`, `sb`, `p`, `BaseTV (BytesT (Dynamic k))`,
    `BaseT (BytesT (Dynamic k))`, `BytesV bs`] >>
  simp[is_word_type_def, eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  fs[eval_operand_def]
QED
