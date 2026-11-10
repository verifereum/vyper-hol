Theory extRetLoopAddressesAmbientPtr
Ancestors
  extRetLoopScalarAmbientPtr extRetAbiBytesCountedPtr extRetBulkCopyCountedPtr
  extRetBytesCopyCountedPtr abiEncoderArrayCode abiEncoderArrayBodyCode
  abiDecoderDynamicLoopSetup context compileEnv emitHelper emitHelperProps exprLoweringProps
  bodyPtrDefs fragExec fragGasPathPtr fragGasSeqPtr venomState venomLayout
  ptrDiscipline ptrSafeRun words finite_map pred_set arithmetic

Theorem loop_coordinates_compiler[local]:
  abi_decode_indexed_coordinates root_op idx stride sa = (ops,sb) ==>
  cs_extends sa sb /\ sb.cs_next_var = sa.cs_next_var+3 /\
  ?data addr. ops = (Var data,Var addr) /\
    not_fresh_at sb data /\ not_fresh_at sb addr
Proof
  simp[abi_decode_indexed_coordinates_def, comp_bind_def, comp_return_def,
       emit_op_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[cs_extends_def, not_fresh_at_def, rich_listTheory.IS_PREFIX_APPEND,
       GSYM listTheory.APPEND_ASSOC]
QED

Theorem loop_coordinates_ambient_counted_ptr[local]:
  abi_decode_indexed_coordinates (Var root) (Var idx) stride sa =
    ((Var data,Var addr),sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa root /\ not_fresh_at sa idx /\
  lookup_var root s = SOME a /\ lookup_var idx s = SOME (n2w j) /\
  op_taint tn (Var idx) = {} /\ ptr_covers G tn root s cap /\
  32+j*stride+n <= cap /\ w2n a+cap < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    lookup_var data sf = SOME (n2w (w2n a+32)) /\
    lookup_var addr sf = SOME (n2w (w2n a+32+j*stride)) /\
    ptr_covers Gf tnf addr sf n /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_indexed_coordinates _ _ _ _ = _` mp_tac >>
  simp[abi_decode_indexed_coordinates_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  `?v. offset_op = Var v` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  rename1 `emit_op ADD [Var root; Lit 32w] sa = (Var data,sc)` >>
  rename1 `emit_op MUL [Var idx; Lit (n2w stride)] sc = (Var off,sd)` >>
  rename1 `emit_op ADD [Var data; Var off] sd = (Var addr,sb)` >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    (imp_res_tac emit_op_extends >>
     gvs[cs_extends_def, inst_extends_def, same_blocks_def]) >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sc p /\ not_fresh_at sd p` by
    (qpat_x_assum `emit_op ADD [Var root; _] _ = _` mp_tac >>
     qpat_x_assum `emit_op MUL _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> decide_tac) >>
  `not_fresh_at sc data /\ not_fresh_at sd data` by
    (qpat_x_assum `emit_op ADD [Var root; _] _ = _` mp_tac >>
     qpat_x_assum `emit_op MUL _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def]) >>
  `32+(j*stride+n) <= cap /\ w2n a+32 < dimword(:256)` by decide_tac >>
  drule_all (emit_bulk_offset_ambient_counted_ptr |> Q.INST [`off` |-> `32`, `n` |-> `j*stride+n`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var idx) sf = SOME (n2w j) /\
   eval_operand (Lit (n2w stride)) sf = SOME (n2w stride) /\
   op_taint tnf (Var idx) = {} /\ op_taint tnf (Lit (n2w stride)) = {}` by
    (simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_all (emit_bulk_binop_ambient_counted_ptr |>
    Q.INST [`opc` |-> `MUL`, `f` |-> `word_mul`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `Gf`, `D`] strip_assume_tac) >>
  `lookup_var data sf' = SOME (n2w (w2n a+32)) /\
   lookup_var off sf' = SOME (n2w (j*stride)) /\
   ptr_covers Gf' tnf' data sf' (j*stride+n) /\
   w2n (n2w (w2n a+32):bytes32)+j*stride < dimword(:256)` by
    (gvs[ptr_covers_def, GSYM word_mul_n2w, w2n_n2w, LESS_MOD] >>
     `w2n a+32 < dimword(:256)` by decide_tac >>
     simp[LESS_MOD] >> metis_tac[]) >>
  `j*stride+n <= j*stride+n` by simp[] >>
  drule_all abi_bytes_lastptr_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]) >>
  simp[w2n_n2w, LESS_MOD] >> metis_tac[]
QED

Theorem abi_array_addresses_ambient_counted_ptr:
  abi_encode_array_addresses (Var ip) (Var src) (Var dst) asz msz sa =
    (((Var idx,Var child_src),(Var data,Var child_dst)),sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var ip s = SOME p /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn ip s 32 /\ ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  mload (w2n p) s = n2w j /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  32+j*msz+msz <= scap /\ 32+j*asz+asz <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    lookup_var idx sf = SOME (n2w j) /\ op_taint tnf (Var idx) = {} /\
    lookup_var child_src sf = SOME (n2w (w2n a+32+j*msz)) /\
    lookup_var child_dst sf = SOME (n2w (w2n b+32+j*asz)) /\
    ptr_covers Gf tnf child_src sf msz /\ ptr_covers Gf tnf child_dst sf asz /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_array_addresses _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def,
       comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `(\(coords,cs). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [Var ip] sa = (Var idx,sc)` >>
  imp_res_tac loop_coordinates_compiler >> gvs[] >>
  rename1 `abi_decode_indexed_coordinates (Var src) (Var idx) msz sc = ((Var srcdata,Var child_src),sd)` >>
  rename1 `abi_decode_indexed_coordinates (Var dst) (Var idx) asz sd = ((Var data,Var child_dst),sb)` >>
  `cs_extends sa sc /\ sc.cs_next_var = sa.cs_next_var+1 /\
   not_fresh_at sc idx` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     simp[cs_extends_def, not_fresh_at_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!v. not_fresh_at sa v ==> not_fresh_at sc v /\ not_fresh_at sd v` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `not_fresh_at sd idx /\ not_fresh_at sd child_src` by
    (gvs[not_fresh_at_def] >> decide_tac) >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
   lookup_var idx sf = SOME (n2w j) /\
   ptr_covers Gf tnf src sf scap /\ ptr_covers Gf tnf dst sf dcap /\
   not_fresh_at sc src /\ not_fresh_at sc dst` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `32+j*msz+msz <= scap /\ w2n a+scap < dimword(:256)` by decide_tac >>
  drule_all loop_coordinates_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf' = SOME b /\ lookup_var idx sf' = SOME (n2w j) /\
   ptr_covers Gf' tnf' dst sf' dcap /\ op_taint tnf' (Var idx) = {} /\
   not_fresh_at sd dst` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `32+j*asz+asz <= dcap /\ w2n b+dcap < dimword(:256)` by decide_tac >>
  qpat_x_assum `abi_decode_indexed_coordinates (Var src) _ _ _ = _` kall_tac >>
  drule_all loop_coordinates_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]) >>
  simp[] >> gvs[ptr_covers_def] >> metis_tac[]
QED
