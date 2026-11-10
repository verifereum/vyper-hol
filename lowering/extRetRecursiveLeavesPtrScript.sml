Theory extRetRecursiveLeavesPtr
Ancestors
  extRetRecursiveResourcePtr extRetRecursiveFramePtr extRetBulkCopyCountedPtr
  extRetBytesCopyCountedPtr exprLoweringProps typedCopyPtr
  abiEncoder exprLowering emitHelper emitHelperProps compileEnv fragExec
  fragGasPathPtr bodyPtrDefs ptrDiscipline venomState valueEncodingProps
  immutableCopyExecution words finite_map pred_set arithmetic

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
