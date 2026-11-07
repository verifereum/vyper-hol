Theory extRetAbiSourceComplexDispatchPtr
Ancestors extRetAbiSourceComplexBytesPtr extRetAbiArrayInitPtr
  extRetBulkCopyCountedPtr extRetBytesCopyCountedPtr abiBuiltinAllocation
  bodyPtrDefs venomMemProps valueEncodingProofs pred_set finite_map
  abiEncoderComplexCode abiEncoderComplexPrefix abiEncoderMembersBoundary
  abiEncoderAddressReach abiEncoder abiEncoderMemberCode exprLoweringProps
  emitHelperProps exprLowering fragExec fragGasPathPtr compileEnv emitHelper
  ptrDiscipline venomState context words list arithmetic

Theorem abi_complex_empty_dispatch_counted_ptr:
  compile_abi_encode_to_buf dst src (AbiComplex []) sa = (out,sb) /\ ~s.vs_halted ==>
  out = Lit 0w /\ sb = sa /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK s) /\
  eval_operand out s = SOME 0w /\ op_taint tn out = {}
Proof
  simp[Once compile_abi_encode_child_def, comp_return_def,
       gas_path_ptr_rules, eval_operand_def, op_taint_def]
QED

Theorem abi_complex_bytes_dispatch_trace:
  bss <> [] /\
  compile_abi_encode_to_buf dst src
    (AbiComplex (MAP (\bs. (AbiBytestring N,32,msz,T)) bss)) sa = (out,sb) /\
  fn_has_code sa sb fn ==>
  ?ip alloc prepared ignored middle.
    emit_op ALLOCA [Lit 32w] sa = (Var ip,alloc) /\
    emit_void MSTORE [Var ip; Lit (n2w (32*LENGTH bss))] alloc = ((),prepared) /\
    compile_abi_encode_complex_elems dst src
      (MAP (\bs. (AbiBytestring N,32,msz,T)) bss) 0 0 (Var ip)
      prepared = (ignored,middle) /\
    emit_op MLOAD [Var ip] middle = (out,sb) /\
    fn_has_code sa alloc fn /\ fn_has_code alloc prepared fn /\
    fn_has_code prepared middle fn /\ fn_has_code middle sb fn
Proof
  strip_tac >>
  `EXISTS (\(_,_,_,dyn). dyn)
    (MAP (\bs. (AbiBytestring N,32,msz,T)) bss)` by
    (Cases_on `bss` >> gvs[]) >>
  drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_trace >> strip_tac >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `?ip. op = Var ip` by
    (qpat_x_assum `emit_op ALLOCA _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  gvs[] >>
  `SUM (MAP (\bs. 32) bss) = 32*LENGTH bss` by
    (POP_ASSUM_LIST (K all_tac) >> Induct_on `bss` >> simp[MULT_CLAUSES]) >>
  gvs[MAP_MAP_o, combinTheory.o_DEF] >>
  `cs_extends sa allocation_st /\ cs_extends allocation_st prepared /\
   cs_extends prepared middle /\ cs_extends middle sb` by
    (rpt conj_tac
     >- (irule cs_extends_same_block >>
         drule emit_op_extends >> simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND])
     >- (irule cs_extends_same_block >>
         drule emit_void_extends >> simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND])
     >- metis_tac[abi_encoder_members_bounds] >>
     irule cs_extends_same_block >>
     qpat_x_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac emit_op_extends) >>
     simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends allocation_st sb /\ cs_extends prepared sb` by
    metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

Theorem abi_complex_cursor_init_counted_ptr:
  emit_op ALLOCA [Lit 32w] sa = (Var ip,alloc) /\
  emit_void MSTORE [Var ip; Lit (n2w k)] alloc = ((),prepared) /\
  fn_has_code sa alloc fn /\ fn_has_code alloc prepared fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (cursor,32) /\ cursor+32 < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = prepared.cs_current_bb /\
    sf.vs_inst_idx = LENGTH prepared.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w cursor) /\ ptr_covers Gf tnf ip sf 32 /\
    mload cursor sf = n2w k /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | cursor <= i /\ i < cursor+32} sf.vs_memory s.vs_memory /\
    (!i. i < cursor \/ cursor+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all emit_alloca_index_ambient_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >> strip_tac >>
  drule emit_mstore_clean_ambient_counted_ptr >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ ip _ 32`)) >>
  disch_then (drule_at (Pat `lookup_var ip _ = _`)) >>
  disch_then (qspecl_then [`n2w k`, `ctx`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[eval_operand_def, op_taint_def]) >> strip_tac >>
  `w2n (n2w cursor : bytes32) = cursor` by (simp[w2n_n2w] >> decide_tac) >>
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (`gas_path_ptr D 0 ctx fn PG G tn s (0+0) Gf tnf' (OK sf')` by
       (irule gas_path_ptr_then >> metis_tac[]) >> gvs[]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `ptr_covers Gf tnf ip sf 32` mp_tac >> simp[ptr_covers_def]) >>
  conj_tac
  >- (qsuff_tac `mload cursor sf' = mload cursor (mstore cursor (n2w k) sf)`
      >- simp[venomMemPropsTheory.mload_mstore_same] >> simp[mload_def]) >>
  conj_tac
  >- metis_tac[typedCopyPtrTheory.mstore_memory_frame] >>
  metis_tac[]
QED

Theorem abi_complex_bytes_source_dispatch_counted_ptr:
  bss <> [] /\ msz = type_memory_size (BaseTV (BytesT (Dynamic N))) /\
  tail = SUM (MAP (\bs. 32+ceil32 (LENGTH bs)) bss) /\
  encsz = 32*LENGTH bss+tail /\
  compile_abi_encode_to_buf (Var dst) (Var src)
    (AbiComplex (MAP (\bs. (AbiBytestring N,32,msz,T)) bss)) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\ not_fresh_at sa src /\
  lookup_var src s = SOME (n2w a) /\ a+scap < dimword(:256) /\
  ptr_covers G tn src s scap /\ LENGTH bss*msz <= scap /\
  lookup_var dst s = SOME (n2w b) /\ b+cap < dimword(:256) /\
  ptr_covers G tn dst s cap /\ encsz <= cap /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (cursor,32) /\ cursor+32 < dimword(:256) /\
  (a+scap <= b \/ b+cap <= a) /\
  (a+scap <= cursor \/ cursor+32 <= a) /\
  (b+cap <= cursor \/ cursor+32 <= b) /\ N < dimword(:256) /\
  (!j. j < LENGTH bss ==>
    32+LENGTH (EL j bss) <= msz /\
    LENGTH (EL j bss) <= dimword(:256)-32 /\
    value_has_type (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss)) /\
    val_wf (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss)) /\
    (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
      val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss))
        (a+j*msz) mem')) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w encsz) /\ op_taint tnf out = {} /\
    (!i. b <= i /\ i < b+encsz ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside ({i | b <= i /\ i < b+encsz} UNION
      {i | cursor <= i /\ i < cursor+32}) sf.vs_memory s.vs_memory /\
    (!i. i NOTIN ({i | b <= i /\ i < b+encsz} UNION
      {i | cursor <= i /\ i < cursor+32}) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!j mem'. j < LENGTH bss /\ mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss))
        (a+j*msz) mem')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_all abi_complex_bytes_dispatch_trace >> strip_tac >>
  drule_all abi_complex_cursor_init_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >> strip_tac >>
  `not_fresh_at prepared ip /\
   (!v. not_fresh_at sa v ==> not_fresh_at prepared v)` by
    (qpat_x_assum `emit_op ALLOCA _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >> decide_tac) >>
  `lookup_var src sf = SOME (n2w a) /\ lookup_var dst sf = SOME (n2w b) /\
   ptr_covers Gf tnf src sf scap /\ ptr_covers Gf tnf dst sf cap` by
    (simp[] >> conj_tac
     >- (qpat_x_assum `ptr_covers G tn src s scap` mp_tac >> simp[ptr_covers_def]) >>
     qpat_x_assum `ptr_covers G tn dst s cap` mp_tac >> simp[ptr_covers_def]) >>
  `!j. j < LENGTH bss ==>
    32+LENGTH (EL j bss) <= msz /\
    LENGTH (EL j bss) <= dimword(:256)-32 /\
    value_has_type (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss)) /\
    val_wf (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (BaseTV (BytesT (Dynamic N))) (vyperValue$BytesV (EL j bss))
        (a+j*msz) mem')` by
    (gen_tac >> strip_tac >>
     qpat_assum `!j. j < LENGTH bss ==> _` (qspec_then `j` mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
     simp[] >> rpt strip_tac >>
     irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
       `{i | cursor <= i /\ i < cursor+32}`] >>
     simp[] >> rpt conj_tac
     >- (qpat_x_assum `msz = type_memory_size _` (SUBST_ALL_TAC o SYM) >> metis_tac[]) 
     >- (rpt strip_tac >> qpat_x_assum `!i. i < cursor \/ _ ==> _`
           (qspec_then `i` mp_tac) >> simp[] >> decide_tac)
     >- (qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
         simp[mem_agree_outside_def]) >>
     `SUC j*msz <= LENGTH bss*msz` by simp[LE_MULT_RCANCEL] >>
     simp_tac (srw_ss()) [loweringPostsTheory.val_footprint_def] >>
     rpt strip_tac >> qpat_x_assum `msz = type_memory_size _` (SUBST_ALL_TAC o SYM) >>
     RULE_ASSUM_TAC (PURE_REWRITE_RULE [MULT_CLAUSES]) >> decide_tac) >>
  drule_at (Pat `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = _`)
    abi_complex_bytes_source_members_counted_ptr >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var src sf = _`)) >>
  disch_then (drule_at (Pat `lookup_var dst sf = _`)) >>
  disch_then (drule_at (Pat `lookup_var ip sf = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ src _ scap`)) >>
  disch_then (drule_at (Pat `mload cursor sf = _`)) >>
  disch_then (qspecl_then [`ctx`, `PG`, `D`, `scap`, `tail`] mp_tac) >>
  (impl_tac >-
    (asm_simp_tac (srw_ss()) [] >>
     qpat_x_assum `msz = type_memory_size _` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `tail = SUM _` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `encsz = 32 * LENGTH _ + _` (SUBST_ALL_TAC o SYM) >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     rpt strip_tac >> metis_tac[])) >> strip_tac >>
  `?result. out = Var result` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `out = Var _` SUBST_ALL_TAC >>
  `lookup_var ip sf' = SOME (n2w cursor) /\ ptr_covers Gf' tnf' ip sf' 32` by
    (conj_tac >- metis_tac[] >>
     qpat_x_assum `ptr_covers Gf tnf ip sf 32` mp_tac >>
     simp[ptr_covers_def]) >>
  `w2n (n2w cursor : bytes32) = cursor` by (simp[w2n_n2w] >> decide_tac) >>
  drule_at (Pat `emit_op MLOAD _ _ = _`) emit_mload_clean_ambient_counted_ptr >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers Gf' tnf' ip sf' 32`)) >>
  disch_then (drule_at (Pat `lookup_var ip sf' = _`)) >>
  disch_then (qspecl_then [`ctx`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!v. not_fresh_at prepared v ==> not_fresh_at middle v` by
    (drule abi_encoder_members_bounds >> simp[not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac >-
    (`gas_path_ptr D 0 ctx fn PG G tn s (0+0) Gf' tnf' (OK sf')` by
       (irule gas_path_ptr_then >> metis_tac[]) >>
     pop_assum (assume_tac o PURE_REWRITE_RULE [ADD_CLAUSES]) >>
     `gas_path_ptr D 0 ctx fn PG G tn s (0+0) Gf'' tnf'' (OK sf'')` by
       (irule gas_path_ptr_then >> metis_tac[]) >> fs[ADD_CLAUSES]) >>
  ntac 3 (conj_tac >- metis_tac[]) >>
  conj_tac >- (pure_asm_rewrite_tac [eval_operand_def] >> REFL_TAC) >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qpat_x_assum `tnf''.t_mem = _` (SUBST1_TAC) >>
     gen_tac >> disch_tac >>
     Cases_on `i < b+32*LENGTH bss`
     >- (qpat_x_assum `!i. b + 0 <= i /\ _ ==> _` irule >> decide_tac) >>
     qpat_x_assum `!i. b + 32 * LENGTH bss <= i /\ _ ==> _` irule >> decide_tac) >>
  `({i | b+32*LENGTH bss <= i /\ i < b+32*LENGTH bss+tail} UNION
     {i | b+0 <= i /\ i < b+0+32*LENGTH bss} UNION
     {i | cursor <= i /\ i < cursor+32}) =
    ({i | b <= i /\ i < b+encsz} UNION {i | cursor <= i /\ i < cursor+32})` by
    (simp_tac (srw_ss()) [EXTENSION, IN_UNION, GSPECIFICATION] >>
     gen_tac >> decide_tac) >>
  conj_tac >-
    (qpat_x_assum `sf''.vs_memory = _` SUBST1_TAC >>
     qpat_x_assum `mem_agree_outside _ sf'.vs_memory sf.vs_memory` mp_tac >>
     qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
     pure_asm_rewrite_tac [] >>
     simp_tac (srw_ss()) [mem_agree_outside_def, IN_UNION, GSPECIFICATION] >>
     rpt strip_tac >> metis_tac[]) >>
  conj_tac >-
    (qpat_x_assum `tnf''.t_mem = _` SUBST1_TAC >>
     qpat_x_assum `!i. i NOTIN _ ==> (i IN tnf'.t_mem <=> _)` mp_tac >>
     pure_asm_rewrite_tac [] >>
     disch_tac >> gen_tac >> disch_tac >>
     `i < cursor \/ cursor+32 <= i` by
       (qpat_x_assum `i NOTIN _` mp_tac >>
        simp_tac (srw_ss()) [IN_UNION, GSPECIFICATION] >> decide_tac) >>
     qpat_x_assum `!i. i NOTIN _ ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_x_assum `!i. i < cursor \/ _ ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- simp[]) >> metis_tac[]) >>
  ntac 6 (conj_tac >- metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  qpat_x_assum `!j mem'. j < LENGTH bss /\ _ ==> _` mp_tac >>
  pure_asm_rewrite_tac [ADD_CLAUSES] >> metis_tac[]
QED
