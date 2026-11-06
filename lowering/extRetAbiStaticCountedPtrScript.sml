(* Counted static ABI encoder bases. *)
Theory extRetAbiStaticCountedPtr
Ancestors
  extRetAbiBytesCountedPtr extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr
  abiEncoder abiEncoderInput abiEncoderInputFrame extRetAbiReadCleanPtr
  valueEncoding valueEncodingProps valueEncodingProofs robustCopyTransportPtr
  representationCleanPtr fragExec immutableCopyExecution
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  bodyPtrDefs fragGasPathPtr fragGasSeqPtr venomState venomLayout
  ptrDiscipline ptrSafeRun words finite_map pred_set arithmetic

Theorem abi_static_copy_path_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy n) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s n /\ n <= cap /\
  n < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiCopy n) at av (w2n a) cap mem') ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `emit_void MCOPY [Var dst; Var src; Lit (n2w n)] sa = ((),sb) /\
   out = Lit (n2w n)` by
    (gvs[Once compile_abi_encode_child_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >> pairarg_tac >> gvs[]) >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {} /\
   ptr_covers G tn src s (w2n (n2w n:bytes32)) /\
   ptr_covers G tn dst s (w2n (n2w n:bytes32))` by
    (simp[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD] >>
     gvs[ptr_covers_def] >> decide_tac) >>
  drule_all emit_mcopy_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!i. w2n a <= i /\ i < w2n a+n ==> i NOTIN tn.t_mem` by
    (`!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
       mem_bytes_at (w2n a) n mem' = enc at av` by
       gvs[abi_encoder_input_copy_iff] >>
     drule robust_mem_bytes_at_clean >> simp[]) >>
  `{w2n b+i | i < n /\ w2n a+i IN tn.t_mem} = {}` by
    (simp[EXTENSION] >> rpt strip_tac >>
     Cases_on `i < n` >> simp[] >>
     `w2n a+i NOTIN tn.t_mem` by (first_x_assum irule >> decide_tac) >> simp[]) >>
  qexistsl_tac [`tnf`, `sf`] >>
  gvs[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD]
QED

Theorem abi_static_word_path_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s 32 /\ 32 <= cap /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input AbiPrimWord at av (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME 32w /\ op_taint tnf out = {} /\
    sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
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
  `ptr_covers G tn src s 32` by (gvs[ptr_covers_def] >> decide_tac) >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
    (`!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
       mem_bytes_at (w2n a) 32 mem' = enc at av` by
       gvs[abi_encoder_input_word_iff] >>
     drule robust_mem_bytes_at_clean >> simp[]) >>
  drule_all emit_mload_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf 32 /\
   eval_operand (Var v) sf = SOME (mload (w2n a) s)` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all emit_mstore_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[eval_operand_def, op_taint_def] >>
  irule immutable_mstore_memory_cong >> simp[]
QED

Theorem compile_abi_static_slice_ptr[local]:
  ((ei = AbiPrimWord /\ n = 32) \/ ei = AbiCopy n) /\
  compile_abi_encode_to_buf (Var dst) (Var src) ei sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s n /\ n <= cap /\
  n < dimword(:256) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input ei at av (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b) n sf.vs_memory = enc at av /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n} /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+n} sf.vs_memory s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> gvs[]
  >- suspend "word"
  >> suspend "copy"
QED

Resume compile_abi_static_slice_ptr[word]:
  drule_all abi_static_word_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `mem_bytes_at (w2n a) 32 s.vs_memory = enc at av` by
    (qpat_x_assum `!mem'. _ ==> _` (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, abi_encoder_input_word_iff]) >>
  `mem_bytes_at (w2n b) 32 (mstore (w2n b) (mload (w2n a) s) s).vs_memory =
   mem_bytes_at (w2n a) 32 s.vs_memory` by
    (irule mload_eq_mem_bytes_at_eq >>
     rewrite_tac[GSYM mem_word_at_eq_mload, mstore_mem_word_at_same]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Resume compile_abi_static_slice_ptr[copy]:
  drule_all abi_static_copy_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `mem_bytes_at (w2n a) n s.vs_memory = enc at av` by
    (qpat_x_assum `!mem'. _ ==> _` (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, abi_encoder_input_copy_iff]) >>
  qexistsl_tac [`G`, `tnf`, `sf`] >>
  asm_rewrite_tac[mcopy_mem_bytes_at_same] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  irule mcopy_mem_bytes_at_disjoint >> decide_tac
QED

Finalise compile_abi_static_slice_ptr

Theorem compile_abi_encode_static_counted_ptr:
  ((ei = AbiPrimWord /\ n = 32) \/ ei = AbiCopy n) /\
  compile_abi_encode_to_buf (Var dst) (Var src) ei sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s n /\ n <= cap /\
  n < dimword(:256) /\ w2n a+cap < dimword(:256) /\
  w2n b+n < dimword(:256) /\
  (w2n a+cap <= w2n b \/ w2n b+n <= w2n a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input ei at av (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b) n sf.vs_memory = enc at av /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n} /\
    (!i. w2n b <= i /\ i < w2n b+n ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+n} sf.vs_memory s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf dst sf n /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input ei at av (w2n a) cap mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all compile_abi_static_slice_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  `mem_bytes_at (w2n a) cap sf.vs_memory = mem_bytes_at (w2n a) cap s.vs_memory` by
    suspend "source_memory" >>
  `!i. i < cap ==> (w2n a+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)` by
    (rpt strip_tac >> simp[] >> decide_tac) >>
  qpat_x_assum `tnf.t_mem = _` (fn th => rewrite_tac[GSYM th]) >>
  rpt strip_tac >> drule_all copied_window_agree_witness >> strip_tac >>
  `abi_encoder_input ei at av (w2n a) cap mix` by metis_tac[] >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED

Resume compile_abi_encode_static_counted_ptr[source_memory]:
  irule listTheory.LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < cap` >>
  `~(w2n b <= w2n a+j /\ w2n a+j < w2n b+n)` by decide_tac >>
  `mem_bytes_at (w2n a+j) 1 sf.vs_memory = mem_bytes_at (w2n a+j) 1 s.vs_memory` by
    (gvs[mem_agree_outside_def] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[listTheory.LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Finalise compile_abi_encode_static_counted_ptr

Theorem compile_abi_encode_static_info_counted_ptr:
  ((ei = AbiPrimWord /\ n = 32) \/ ei = AbiCopy n) /\
  compile_abi_encode_static_info (Var dst) (Var src) ei sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s cap /\ ptr_covers G tn dst s n /\ n <= cap /\
  n < dimword(:256) /\ w2n a+cap < dimword(:256) /\
  w2n b+n < dimword(:256) /\
  (w2n a+cap <= w2n b \/ w2n b+n <= w2n a) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input ei at av (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b) n sf.vs_memory = enc at av /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n} /\
    (!i. w2n b <= i /\ i < w2n b+n ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+n} sf.vs_memory s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf dst sf n /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input ei at av (w2n a) cap mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `compile_abi_encode_to_buf (Var dst) (Var src) ei sa = (out,sb)` by
    (qpat_x_assum `(_ /\ _) \/ _` strip_assume_tac >>
     gvs[compile_abi_encode_static_info_def] >>
     simp[Once compile_abi_encode_child_def]) >>
  drule_all compile_abi_encode_static_counted_ptr >> simp[]
QED
