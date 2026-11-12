Theory extRetEvaluatedStaticBodyPtr
Ancestors
  extRetLoopAddressesAmbientPtr extRetLoopStaticInfoAmbientPtr
  extRetRecursiveResourcePtr extRetRecursiveLayoutPtr representationCleanPtr
  robustCopyTransportPtr abiEncoderArrayCode abiEncoderArrayBodyCode abiEncoderAppend
  abiDecoderDynamicLoopSetup abiEncoder emitHelper emitHelperProps exprLoweringProps
  bodyPtrDefs fragExec fragGasPathPtr fragGasSeqPtr venomState compileEnv
  ptrDiscipline words finite_map pred_set arithmetic valueEncoding valueEncodingProofs
  extRetRecursiveFramePtr valueTypingMemoryProps vyperTyping vyperTypeABI

Theorem loop_addresses_vars[local]:
  abi_encode_array_addresses ip src dst asz msz sa = (coords,sb) ==>
  ?idx child_src data child_dst.
    coords = ((Var idx,Var child_src),(Var data,Var child_dst)) /\
    cs_extends sa sb /\ not_fresh_at sb idx /\
    not_fresh_at sb child_src /\ not_fresh_at sb child_dst
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def,
       abi_decode_indexed_coordinates_def, comp_bind_def, comp_return_def,
       emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[cs_extends_def, not_fresh_at_def, rich_listTheory.IS_PREFIX_APPEND,
       GSYM listTheory.APPEND_ASSOC]
QED

Theorem loop_static_body_clean_ambient_counted_ptr:
  abi_encode_array_static_body (Var ip) (Var src) (Var dst) ei n n sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var ip s = SOME p /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn ip s 32 /\ ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  mload (w2n p) s = n2w j /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  ((ei = AbiPrimWord /\ n = 32) \/ ei = AbiCopy n) /\
  32+j*n+n <= scap /\ 32+j*n+n <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  (!i. w2n a+32+j*n <= i /\ i < w2n a+32+j*n+n ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w j) /\ op_taint tnf out = {} /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b+32+j*n <= i /\ i < w2n b+32+j*n+n} /\
    mem_agree_outside {i | w2n b+32+j*n <= i /\ i < w2n b+32+j*n+n}
      sf.vs_memory s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `abi_encode_array_static_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_encode_array_static_body_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gnvs[] >>
  drule loop_addresses_vars >> strip_tac >> gnvs[] >>
  rename1 `abi_encode_array_addresses _ _ _ _ _ sa = (_,sc)` >>
  rename1 `compile_abi_encode_static_info _ _ ei sc = (res,sb)` >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    (irule fn_has_code_split >> metis_tac[cs_appends_def, cs_appends_abi_encode_static_info]) >>
  `32+j*n+n <= scap /\ 32+j*n+n <= dcap /\
   w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256)` by decide_tac >>
  drule_all abi_array_addresses_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `w2n a+32+j*n < dimword(:256) /\ w2n b+32+j*n < dimword(:256) /\
   n < dimword(:256)` by decide_tac >>
  `!i. w2n (n2w (w2n a+32+j*n):bytes32) <= i /\
        i < w2n (n2w (w2n a+32+j*n):bytes32)+n ==> i NOTIN tnf.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all loop_static_info_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  `!v. not_fresh_at sa v ==> not_fresh_at sc v` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >- (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
    qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  gnvs[w2n_n2w, LESS_MOD, eval_operand_def] >> metis_tac[]
QED

(* Evaluated dynamic-array input, including zero-size static children. *)
Theorem encoder_evaluated_static_body_counted_ptr:
  abi_encode_array_static_body (Var ip) (Var src) (Var dst) ei k k sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var ip s = SOME p /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn ip s 32 /\ ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  mload (w2n p) s = n2w j /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  ((ei = AbiPrimWord /\ k = 32) \/ ei = AbiCopy k) /\
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) /\
  k = type_memory_size tv /\ type_memory_size (ArrayTV tv (Dynamic n)) <= scap /\
  value_has_type (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) /\ j < LENGTH vs /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) (w2n a) mem') /\
  32+LENGTH vs*k <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n p+32 <= w2n b \/ w2n b+dcap <= w2n p) /\
  encoder_resource ctx fn sites q len protected s ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w j) /\ op_taint tnf out = {} /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b+32+j*k <= i /\ i < w2n b+32+j*k+k} /\
    mem_agree_outside {i | w2n b+32+j*k <= i /\ i < w2n b+32+j*k+k}
      sf.vs_memory s.vs_memory /\
    (!i. w2n b+32+j*k <= i /\ i < w2n b+32+j*k+k ==> i NOTIN tnf.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    ptr_covers Gf tnf ip sf 32 /\ ptr_covers Gf tnf src sf scap /\
    ptr_covers Gf tnf dst sf dcap /\ mload (w2n p) sf = n2w j /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q len protected sf /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) (w2n a) mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all encoder_dynamic_source_window >> strip_tac >>
  `value_has_type tv (EL j vs)` by
    (fs[value_has_type_def, all_have_type_EVERY, listTheory.EVERY_EL] >> metis_tac[]) >>
  `!i. w2n a+32+j*k <= i /\ i < w2n a+32+j*k+k ==> i NOTIN tn.t_mem` by
    metis_tac[robust_val_in_memory_static_clean] >>
  `32+j*k+k <= scap /\ 32+j*k+k <= dcap` by
    (`j*k+k <= LENGTH vs*k` by
      (irule abiDecoderArraySliceTheory.abi_decoder_array_cell_capacity >> simp[]) >>
     qpat_x_assum `k = _` (fn th => rule_assum_tac (PURE_REWRITE_RULE [GSYM th])) >>
     decide_tac) >>
  drule_all loop_static_body_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  `!i. i NOTIN {i | w2n b+32+j*k <= i /\ i < w2n b+32+j*k+k} ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)` by simp[] >>
  `!i. w2n p <= i /\ i < w2n p+32 ==>
    i NOTIN {i | w2n b+32+j*k <= i /\ i < w2n b+32+j*k+k}` by
    (simp[NoAsms] >> rpt strip_tac >> decide_tac) >>
  drule_all encoder_frame_clean_word >> strip_tac >>
  `val_wf (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    metis_tac[value_has_type_memory_wf] >>
  `!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
    val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) (w2n a) mem'` by
    (rpt gen_tac >> strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
       `{i | w2n b+32+j*k <= i /\ i < w2n b+32+j*k+k}`] >>
     conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
     conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
     conj_tac >-
       (qpat_x_assum `mem_agree_outside _ sf.vs_memory s.vs_memory` mp_tac >>
        rewrite_tac[mem_agree_outside_def]) >>
     conj_tac >-
       (simp[NoAsms, loweringPostsTheory.val_footprint_def] >>
        rpt strip_tac >> decide_tac) >>
     first_assum MATCH_ACCEPT_TAC) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac >-
    (qpat_x_assum `ptr_covers G tn ip s 32` mp_tac >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >-
    (qpat_x_assum `ptr_covers G tn src s scap` mp_tac >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  qpat_x_assum `ptr_covers G tn dst s dcap` mp_tac >>
  simp[ptr_covers_def] >> metis_tac[]
QED
