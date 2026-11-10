Theory extRetRecursiveLeavesPtr
Ancestors
  extRetRecursiveResourcePtr extRetRecursiveFramePtr extRetBulkCopyCountedPtr
  extRetBytesCopyCountedPtr exprLoweringProps typedCopyPtr
  abiEncoder exprLowering emitHelper emitHelperProps compileEnv fragExec
  fragGasPathPtr bodyPtrDefs ptrDiscipline venomState valueEncodingProps
  immutableCopyExecution words finite_map pred_set arithmetic
  extRetLeafAllocationFramePtr extRetAbiBytesLivePtr abiEncoderLeafGlobals
  abiEncoderBytesCode abiEncoderInput extRetAbiBytesArithPtr forPtrWord

Overload ceil32[local] = ``contractABI$ceil32``

(* The primitive case needs only its robust 32-byte read, not an ABI
   representative uniform across all memories. *)
Theorem encoder_word_resource_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  encoder_resource ctx fn sites q len protected s ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME 32w /\ op_taint tnf out = {} /\
    sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    encoder_resource ctx fn sites q len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf (w2n b) 32)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf (w2n b) 32 ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  `?v. val_op = Var v` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  rename1 `emit_void MSTORE [Var dst; Var v] cs' = ((),sb)` >>
  `cs_extends sa cs' /\ cs_extends cs' sb` by
    (imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     gvs[cs_extends_def, inst_extends_def, same_blocks_def]) >>
  `fn_has_code sa cs' fn /\ fn_has_code cs' sb fn` by
    metis_tac[fn_has_code_split] >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf 32 /\
   eval_operand (Var v) sf = SOME (mload (w2n a) s)` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q len protected sf'` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  `sf'.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory` by
    (irule EQ_TRANS >> qexists_tac `(mstore (w2n b) (mload (w2n a) s) sf).vs_memory` >>
     simp[] >> irule immutable_mstore_memory_cong >> simp[]) >>
  simp[eval_operand_def, op_taint_def] >>
  conj_tac >-
    (irule encoder_memory_frame_mono >>
     qexists_tac `{i | w2n b <= i /\ i < w2n b+32}` >>
     simp[encoder_write_envelope_def, SUBSET_DEF, mem_agree_outside_def] >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  simp[encoder_write_envelope_def]
QED

(* Evaluated, fixed-value robust source interface for the primitive leaf. *)
Theorem encoder_typed_word_resource_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n a) mem) /\
  encoder_resource ctx fn sites q len protected s ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME 32w /\ op_taint tnf out = {} /\
    sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    encoder_resource ctx fn sites q len protected sf /\
    mem_agree_outside (encoder_write_envelope sites sf (w2n b) 32)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf (w2n b) 32 ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
    metis_tac[for_typed_word_robust_clean] >>
  irule encoder_word_resource_ptr >> simp[] >>
  qexistsl_tac [`dst`, `src`] >> simp[]
QED

Theorem encoder_bytes_resource_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+LENGTH bs) /\
  ptr_covers G tn dst s (32+ceil32 (LENGTH bs)) /\
  32+LENGTH bs <= cap /\ LENGTH bs <= dimword(:256)-32 /\
  32+ceil32 (LENGTH bs) < dimword(:256) /\
  w2n a+(32+LENGTH bs) < dimword(:256) /\
  w2n b+32+ceil32 (LENGTH bs) < dimword(:256) /\
  (w2n a+(32+LENGTH bs) <= w2n b \/ w2n b+32+ceil32 (LENGTH bs) <= w2n a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') /\
  encoder_resource ctx fn sites q len protected s ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+ceil32 (LENGTH bs))) /\ op_taint tnf out = {} /\
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
      abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) (w2n a) cap mem') /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\ encoder_resource ctx fn sites q len protected sf /\
    mem_agree_outside
      (encoder_write_envelope sites sf (w2n b) (32+ceil32 (LENGTH bs)))
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope sites sf (w2n b) (32+ceil32 (LENGTH bs)) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_encode_bytes_shape >> strip_tac >>
  drule abi_encoder_bytes_global_code >> strip_tac >>
  `fn_has_code sa sb (leaf_cut_function sb fn)` by
    (irule leaf_cut_function_has_code >> simp[]) >>
  qpat_x_assum `fn_has_code sa sb fn` mp_tac >>
  drule_all (SRULE [abi_bytes_ceil32_eq]
    compile_abi_encode_bytes_live_ambient_counted_ptr) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  disch_tac >>
  drule leaf_cut_path_transport >>
  disch_then (qspecl_then [`sa`, `sb`, `fn`, `sf`] mp_tac) >>
  simp[] >> (impl_tac >- fs[]) >> strip_tac >>
  `encoder_resource ctx fn sites q len protected sf` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> gns[] >>
  conj_tac >-
    (irule encoder_memory_frame_mono >>
     qexists_tac `{i | w2n b <= i /\ i < w2n b+32+ceil32 (LENGTH bs)}` >>
     gvs[encoder_write_envelope_def, SUBSET_DEF]) >>
  simp[encoder_write_envelope_def]
QED
