Theory extRetLoopTailAmbientPtr
Ancestors
  extRetLoopScalarAmbientPtr extRetAbiArrayInitPtr extRetCopyCountedPtr
  extRetBytesCopyCountedPtr extRetBulkCopyCountedPtr abiDecoderLoopEmit
  abiEncoderArrayCode bodyPtrCtrlCases fragExec fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs emitHelper emitHelperProps exprLoweringProps compileEnv
  ptrDiscipline ptrSafeRun venomExecSemantics venomExecProofs venomInst
  venomState venomMemProps valueEncodingProps valueEncodingProofs
  robustCopyTransportPtr words finite_map pred_set arithmetic

Theorem abi_decode_loop_suffix_ambient_counted_ptr:
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
    mem_agree_outside {i | w2n p <= i /\ i < w2n p+32} sf.vs_memory s.vs_memory /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_memory = (mstore (w2n p) (n2w (j+1)) s).vs_memory
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
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var ip sf = SOME p /\ ptr_covers Gf tnf ip sf 32` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Var nv) sf = SOME (n2w (j+1))` by
    simp[eval_operand_def, word_add_n2w] >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
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
  conj_tac >-
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     `mem_bytes_at i 1 (mstore (w2n p) (n2w (j+1)) sf).vs_memory =
      mem_bytes_at i 1 sf.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> gvs[] >> decide_tac) >> simp[]) >>
  simp[mstore_def]
QED

Theorem abi_array_static_exit_ambient_counted_ptr:
  abi_encode_array_static_exit (Var src) asz sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  mload (w2n a) s = n2w n /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w (32+n*asz)) /\ op_taint tnf out = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_array_static_exit _ _ _ = _` mp_tac >>
  simp[abi_encode_array_static_exit_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (len,sc)` >>
  rename1 `emit_op MUL [len;_] sc = (payload,sd)` >>
  `?lv pv ov. len = Var lv /\ payload = Var pv /\ out = Var ov` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    (imp_res_tac emit_op_extends >> gvs[cs_extends_def, inst_extends_def, same_blocks_def]) >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x /\ not_fresh_at sd x` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op MUL _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> decide_tac) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Var lv) sf = SOME (n2w n) /\
   eval_operand (Lit (n2w asz)) sf = SOME (n2w asz) /\
   op_taint tnf (Lit (n2w asz)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_bulk_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `MUL`,`f` |-> `word_mul`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`Gf`,`D`] strip_assume_tac) >>
  `eval_operand (Lit 32w) sf' = SOME 32w /\
   eval_operand (Var pv) sf' = SOME (n2w (n*asz)) /\
   op_taint tnf' (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def, GSYM word_mul_n2w] >>
  drule_all (emit_copy_len_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `ADD`,`f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`Gf'`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`,`tnf''`,`sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`,`m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  simp[eval_operand_def, GSYM word_add_n2w, WORD_ADD_COMM] >> metis_tac[]
QED
