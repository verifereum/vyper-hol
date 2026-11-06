(* Counted phases of singleton dynamic ABI encoding. *)
Theory extRetAbiSingletonCountedPtr
Ancestors
  extRetAbiArrayInitPtr extRetAbiBytesCountedPtr extRetAbiWrappedSourcePtr
  abiEncoderComplexCode abiEncoderMemberCode abiBuiltinAllocation
  extRetBulkCopyCountedPtr extRetCountedPtr extRetBytesCopyCountedPtr
  fragGasPathPtr fragGasSeqPtr fragExec emitHelperProps exprLoweringProps
  context compileEnv emitHelper exprLowering ptrDiscipline bodyPtrDefs venomState venomExecSemantics
  venomMemProps
  valueEncodingProps valueEncodingProofs words finite_map pred_set arithmetic

Theorem abi_encode_singleton_prefix_counted_ptr:
  abi_encode_complex_prefix [(ei,32,cap,T)] sa = (Var ip,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas sa.cs_next_id =
    SOME (addr,32) /\ addr+32 < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w addr) /\ ptr_covers Gf tnf ip sf 32 /\
    mload addr sf = 32w /\
    (!i. addr <= i /\ i < addr+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    mem_agree_outside {i | addr <= i /\ i < addr+32} sf.vs_memory s.vs_memory /\
    (!i. i < addr \/ addr+32 <= i ==> (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_complex_prefix _ _ = _` mp_tac >>
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `fn_has_code sa sb fn` >>
  rename1 `emit_op ALLOCA _ sa = (Var ip,sc)` >>
  `cs_extends sa sc` by
    metis_tac[cj 2 cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sc sb` by
    metis_tac[cj 3 cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  drule_all emit_alloca_index_counted_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `eval_operand (Lit 32w) sf = SOME 32w /\ op_taint tnf (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all emit_mstore_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `addr < dimword(:256)` by decide_tac >>
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  `ptr_covers Gf tnf' ip sf' 32` by
    (fs[ptr_covers_def] >> metis_tac[]) >>
  simp[w2n_n2w, LESS_MOD] >>
  conj_tac >-
    (`mload addr sf' = mload addr (mstore addr 32w sf)` by simp[mload_def] >>
     simp[mload_mstore_same]) >>
  conj_tac >-
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     `mem_bytes_at i 1 (mstore addr 32w sf).vs_memory = mem_bytes_at i 1 sf.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> gvs[] >> decide_tac) >> simp[]) >>
  rpt strip_tac >> simp[IN_DIFF] >> metis_tac[LESS_LESS_EQ_TRANS]
QED
