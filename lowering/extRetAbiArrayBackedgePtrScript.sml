(* Counted scratch-index update and header backedge. *)
Theory extRetAbiArrayBackedgePtr
Ancestors
  extRetAbiArrayInitPtr extRetCopyCountedPtr extRetBytesCopyCountedPtr
  extRetBulkCopyCountedPtr abiDecoderLoopEmit bodyPtrCtrlCases
  fragExec fragGasSeqPtr fragGasPathPtr bodyPtrDefs emitHelper emitHelperProps
  exprLoweringProps compileEnv ptrDiscipline ptrSafeRun venomExecSemantics
  venomExecProofs venomInst venomState venomMemProps valueEncodingProps
  valueEncodingProofs robustCopyTransportPtr abiEncoderInputFrame
  words finite_map pred_set arithmetic

Theorem abi_decode_loop_suffix_counted_ptr:
  abi_decode_loop_suffix (Var ip) idx hdr exit_lbl sa = ((),sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\
  eval_operand idx s = SOME (n2w j) /\ op_taint tn idx = {} /\
  lookup_var ip s = SOME p /\ ptr_covers G tn ip s 32 /\
  w2n p+32 < dimword(:256) /\ j+1 < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = hdr /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    lookup_var ip sf = SOME p /\ ptr_covers Gf tnf ip sf 32 /\
    mload (w2n p) sf = n2w (j+1) /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n p <= i /\ i < w2n p+32} /\
    (!i. i NOTIN {i | w2n p <= i /\ i < w2n p+32} ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    mem_agree_outside {i | w2n p <= i /\ i < w2n p+32} sf.vs_memory s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_loop_suffix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (inc,sc)` >>
  rename1 `emit_void MSTORE _ sc = ((),sd)` >>
  rename1 `emit_inst JMP _ _ sd = ((),se)` >>
  rename1 `new_block exit_lbl se = (_,sb)` >>
  `?nv. inc = Var nv` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> metis_tac[]) >> gvs[] >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd se /\ cs_extends se sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd se fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `eval_operand (Lit 1w) s = SOME 1w /\ op_taint tn (Lit 1w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_copy_len_binop_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var ip sf = SOME p /\ ptr_covers Gf tnf ip sf 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Var nv) sf = SOME (n2w (j+1))` by
    simp[eval_operand_def, word_add_n2w] >>
  drule_all emit_mstore_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `se.cs_blocks = sd.cs_blocks /\ se.cs_current_bb = sd.cs_current_bb /\
   se.cs_current_insts = sd.cs_current_insts ++
     [mk_inst sd.cs_next_id JMP [Label hdr] []]` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `gas_path_ptr D 0 ctx fn PG Gf tnf' sf' 0 Gf tnf' (OK (jump_to hdr sf'))` by
    (irule emit_jump_zero_path_ptr >> simp[] >>
     qexistsl_tac [`sd`, `se`] >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf'`, `jump_to hdr sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf'`, `tnf'`] >> simp[]) >>
  `ptr_covers Gf tnf' ip sf' 32` by (fs[ptr_covers_def] >> metis_tac[]) >>
  `mload (w2n p) sf' = n2w (j+1)` by
    (`mload (w2n p) sf' = mload (w2n p) (mstore (w2n p) (n2w (j+1)) sf)` by
       simp[mload_def] >> simp[mload_mstore_same]) >>
  simp[jump_to_def, lookup_var_def] >>
  conj_tac >- (gvs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- gvs[mload_def] >>
  simp[mem_agree_outside_def] >> rpt strip_tac >>
  `mem_bytes_at i 1 (mstore (w2n p) (n2w (j+1)) sf).vs_memory =
   mem_bytes_at i 1 sf.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> gvs[] >> decide_tac) >> simp[]
QED

Theorem abi_decode_loop_suffix_source_prefix_counted_ptr:
  abi_decode_loop_suffix (Var ip) idx hdr exit_lbl sa = ((),sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\
  eval_operand idx s = SOME (n2w j) /\ op_taint tn idx = {} /\
  lookup_var ip s = SOME p /\ ptr_covers G tn ip s 32 /\
  w2n p+32 < dimword(:256) /\ j+1 < dimword(:256) /\
  not_fresh_at sa src /\ lookup_var src s = SOME a /\ ptr_covers G tn src s cap /\
  not_fresh_at sa dst /\ lookup_var dst s = SOME b /\ ptr_covers G tn dst s dcap /\
  k <= dcap /\ mem_bytes_at (w2n b) k s.vs_memory = prefix /\
  (!i. w2n b <= i /\ i < w2n b+k ==> i NOTIN tn.t_mem) /\
  (w2n a+cap <= w2n p \/ w2n p+32 <= w2n a) /\
  (w2n b+k <= w2n p \/ w2n p+32 <= w2n b) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input info ty v (w2n a) cap mem') ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = hdr /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    lookup_var ip sf = SOME p /\ ptr_covers Gf tnf ip sf 32 /\
    mload (w2n p) sf = n2w (j+1) /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tnf.t_mem) /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf cap /\
    lookup_var dst sf = SOME b /\ ptr_covers Gf tnf dst sf dcap /\
    mem_bytes_at (w2n b) k sf.vs_memory = prefix /\
    (!i. w2n b <= i /\ i < w2n b+k ==> i NOTIN tnf.t_mem) /\
    mem_agree_outside {i | w2n p <= i /\ i < w2n p+32} sf.vs_memory s.vs_memory /\
    (!i. i NOTIN {i | w2n p <= i /\ i < w2n p+32} ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input info ty v (w2n a) cap mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_decode_loop_suffix_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  `!off len. (off+len <= w2n p \/ w2n p+32 <= off) ==>
    mem_bytes_at off len sf.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >> irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     `mem_bytes_at (off+x) 1 sf.vs_memory = mem_bytes_at (off+x) 1 s.vs_memory` by
       (qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
        simp[mem_agree_outside_def] >> strip_tac >> first_x_assum irule >>
        simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  conj_tac >- metis_tac[] >>
  `mem_bytes_at (w2n a) cap sf.vs_memory = mem_bytes_at (w2n a) cap s.vs_memory` by
    metis_tac[] >>
  `!i. i < cap ==> (w2n a+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)` by
    (rpt strip_tac >> simp[IN_DIFF] >> decide_tac) >>
  rpt strip_tac >>
  `mem_agree_outside tnf.t_mem sf.vs_memory mem'` by simp[] >>
  drule_all copied_window_agree_witness >> strip_tac >>
  `abi_encoder_input info ty v (w2n a) cap mix` by metis_tac[] >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED
