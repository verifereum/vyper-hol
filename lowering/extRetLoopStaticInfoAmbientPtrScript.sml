Theory extRetLoopStaticInfoAmbientPtr
Ancestors
  extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr extRetRecursiveResourcePtr
  abiEncoder emitHelper emitHelperProps exprLoweringProps immutableCopyExecution
  bodyPtrDefs fragExec fragGasPathPtr fragGasSeqPtr venomState
  ptrDiscipline words finite_map pred_set arithmetic compileEnv valueEncodingProps

Theorem loop_static_info_dispatch:
  ei = AbiPrimWord \/ (?k. ei = AbiCopy k) ==>
  compile_abi_encode_static_info dst src ei = compile_abi_encode_to_buf dst src ei
Proof
  strip_tac >> gvs[compile_abi_encode_static_info_def, Once compile_abi_encode_child_def]
QED

Theorem loop_word_clean_ambient_counted_ptr[local]:
  compile_abi_encode_static (Var dst) (Var src) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME 32w /\ op_taint tnf out = {} /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+32} sf.vs_memory s.vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_encode_static _ _ _ = _` mp_tac >>
  simp[compile_abi_encode_static_def,
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
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[eval_operand_def, op_taint_def] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  qpat_x_assum `sf'.vs_memory = _` (fn th => rewrite_tac[th]) >>
  simp[mstore_mem_bytes_at_disjoint]
QED

Theorem loop_static_info_clean_ambient_counted_ptr:
  ((ei = AbiPrimWord /\ n = 32) \/ ei = AbiCopy n) /\
  compile_abi_encode_static_info (Var dst) (Var src) ei sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\ n < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a+n ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+n} sf.vs_memory s.vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> gvs[compile_abi_encode_static_info_def]
  >- (drule_all loop_word_clean_ambient_counted_ptr >> simp[]) >>
  qpat_x_assum `comp_ignore_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {} /\
   ptr_covers G tn src s (w2n (n2w n:bytes32)) /\
   ptr_covers G tn dst s (w2n (n2w n:bytes32))` by
    simp[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD] >>
  drule_all emit_mcopy_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `{w2n b+i | i < n /\ w2n a+i IN tn.t_mem} = {}` by
    (simp[EXTENSION] >> rpt strip_tac >> Cases_on `i < n` >> simp[] >>
     `w2n a+i NOTIN tn.t_mem` by (first_x_assum irule >> decide_tac) >> simp[]) >>
  qexistsl_tac [`G`, `tnf`, `sf`] >>
  gvs[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED
