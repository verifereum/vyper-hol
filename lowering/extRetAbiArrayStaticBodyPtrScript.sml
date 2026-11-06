(* Counted static-array body address and memory interfaces. *)
Theory extRetAbiArrayStaticBodyPtr
Ancestors
  extRetAbiStaticCountedPtr extRetAbiBytesCountedPtr extRetBulkCopyCountedPtr
  extRetBytesCopyCountedPtr abiEncoderArrayCode abiEncoderArrayBodyCode abiEncoderAppend
  abiDecoderDynamicLoopSetup abiEncoderInput abiEncoderInputFrame
  robustCopyTransportPtr context compileEnv emitHelper emitHelperProps exprLoweringProps
  bodyPtrDefs fragExec fragGasPathPtr fragGasSeqPtr venomState venomLayout
  ptrDiscipline ptrSafeRun words finite_map pred_set arithmetic valueEncoding valueEncodingProofs

Theorem abi_array_coordinates_compiler[local]:
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

Theorem abi_array_coordinates_counted_ptr[local]:
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
      op_taint tnf (Var p) = op_taint tn (Var p))
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
  drule_all (emit_bulk_offset_counted_ptr |> Q.INST [`off` |-> `32`, `n` |-> `j*stride+n`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var idx) sf = SOME (n2w j) /\
   eval_operand (Lit (n2w stride)) sf = SOME (n2w stride) /\
   op_taint tnf (Var idx) = {} /\ op_taint tnf (Lit (n2w stride)) = {}` by
    (simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_all (emit_bulk_binop_counted_ptr |>
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
  drule_all abi_bytes_lastptr_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac >- suspend "path" >>
  simp[w2n_n2w, LESS_MOD] >> metis_tac[]
QED

Resume abi_array_coordinates_counted_ptr[path]:
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]
QED

Finalise abi_array_coordinates_counted_ptr

Theorem abi_array_static_selected_bounds[local]:
  ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  j < LENGTH avs /\
  (!mem'. mem_agree_outside tn.t_mem mem mem' ==>
    abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
      a cap mem') /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= ocap ==>
  (!mem'. mem_agree_outside tn.t_mem mem mem' ==>
    abi_encoder_input ei ty (EL j avs) (a+32+j*msz) msz mem') /\
  32+j*msz+msz <= cap /\ 32+j*asz+asz <= ocap /\ asz <= msz /\
  j < dimword(:256)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs) a cap mem` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all abi_encoder_array_selected_input >> strip_tac >>
  `has_type (Array NONE ty) (ListV avs)` by metis_tac[abi_encoder_input_typed] >>
  `!mem'. mem_agree_outside tn.t_mem mem mem' ==>
    abi_encoder_input ei ty (EL j avs) (a+32+j*msz) msz mem'` by
    (rpt strip_tac >>
     `abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs) a cap mem'` by metis_tac[] >>
     drule_at (Pat `abi_encoder_input _ _ _ _ _ mem'`) abi_encoder_array_selected_input >> simp[]) >>
  `asz <= msz` by
    (qpat_x_assum `(_ /\ _) \/ _` strip_assume_tac >>
     gvs[abi_encoder_input_word_iff, abi_encoder_input_copy_iff]) >>
  `~is_dynamic ty` by simp[] >>
  drule_all abi_encoder_array_static_size >> strip_tac >>
  `j <= LENGTH avs` by decide_tac >>
  drule_all abi_encoder_array_prefix_types >> strip_tac >>
  simp[] >>
  `j*asz+asz <= LENGTH avs*asz` by
    (`j+1 <= LENGTH avs` by decide_tac >>
     `j*asz+asz = (j+1)*asz` by simp[RIGHT_ADD_DISTRIB] >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `asz = _` SUBST_ALL_TAC >> fs[] >> gvs[]
QED

Theorem abi_array_addresses_counted_ptr[local]:
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
      op_taint tnf (Var v) = op_taint tn (Var v))
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
  imp_res_tac abi_array_coordinates_compiler >> gvs[] >>
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
  drule_all emit_mload_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
   lookup_var idx sf = SOME (n2w j) /\
   ptr_covers Gf tnf src sf scap /\ ptr_covers Gf tnf dst sf dcap /\
   not_fresh_at sc src /\ not_fresh_at sc dst` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `32+j*msz+msz <= scap /\ w2n a+scap < dimword(:256)` by decide_tac >>
  drule_all abi_array_coordinates_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf' = SOME b /\ lookup_var idx sf' = SOME (n2w j) /\
   ptr_covers Gf' tnf' dst sf' dcap /\ op_taint tnf' (Var idx) = {} /\
   not_fresh_at sd dst` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `32+j*asz+asz <= dcap /\ w2n b+dcap < dimword(:256)` by decide_tac >>
  qpat_x_assum `abi_decode_indexed_coordinates (Var src) _ _ _ = _` kall_tac >>
  drule_all abi_array_coordinates_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`, `tnf''`, `sf''`] >>
  conj_tac >- suspend "path" >>
  simp[] >> gvs[ptr_covers_def] >> metis_tac[]
QED

Resume abi_array_addresses_counted_ptr[path]:
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
  irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]
QED

Finalise abi_array_addresses_counted_ptr

Theorem abi_array_addresses_vars[local]:
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

Theorem compile_abi_array_static_body_counted_ptr:
  abi_encode_array_static_body (Var ip) (Var src) (Var dst) ei asz msz sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa ip /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var ip s = SOME p /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn ip s 32 /\ ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
  mload (w2n p) s = n2w j /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  j < LENGTH avs /\ ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
      (w2n a) scap mem') /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  w2n p+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n p+32 <= w2n b \/ w2n b+dcap <= w2n p) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    eval_operand out sf = SOME (n2w j) /\ op_taint tnf out = {} /\
    mem_bytes_at (w2n b+32+j*asz) asz sf.vs_memory = enc ty (EL j avs) /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b+32+j*asz <= i /\ i < w2n b+32+(j+1)*asz} /\
    mem_agree_outside {i | w2n b+32+j*asz <= i /\ i < w2n b+32+(j+1)*asz}
      sf.vs_memory s.vs_memory /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sa v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)) /\
    ptr_covers Gf tnf ip sf 32 /\ ptr_covers Gf tnf src sf scap /\
    ptr_covers Gf tnf dst sf dcap /\ mload (w2n p) sf = n2w j /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tnf.t_mem) /\
    (!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
      abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
        (w2n a) scap mem')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_array_static_selected_bounds >> strip_tac >>
  qpat_x_assum `abi_encode_array_static_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_encode_array_static_body_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gnvs[] >>
  drule abi_array_addresses_vars >> strip_tac >> gnvs[] >>
  rename1 `abi_encode_array_addresses _ _ _ _ _ sa = (_,sc)` >>
  rename1 `compile_abi_encode_static_info _ _ ei sc = (res,sb)` >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    (irule fn_has_code_split >> metis_tac[cs_appends_def, cs_appends_abi_encode_static_info]) >>
  `32+j*msz+msz <= scap /\ 32+j*asz+asz <= dcap /\
   w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256)` by decide_tac >>
  drule_all abi_array_addresses_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `asz < dimword(:256) /\
   w2n (n2w (w2n a+32+j*msz):bytes32)+msz < dimword(:256) /\
   w2n (n2w (w2n b+32+j*asz):bytes32)+asz < dimword(:256)` by
    (`w2n a+32+j*msz < dimword(:256) /\ w2n b+32+j*asz < dimword(:256)` by decide_tac >>
     simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  Q.SUBGOAL_THEN
   `w2n (n2w (w2n a+32+j*msz):bytes32)+msz <= w2n (n2w (w2n b+32+j*asz):bytes32) \/
    w2n (n2w (w2n b+32+j*asz):bytes32)+asz <= w2n (n2w (w2n a+32+j*msz):bytes32)` assume_tac
  >- (`w2n a+32+j*msz < dimword(:256) /\ w2n b+32+j*asz < dimword(:256)` by decide_tac >>
      simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  `!mem'. mem_agree_outside tnf.t_mem sf.vs_memory mem' ==>
    abi_encoder_input ei ty (EL j avs) (w2n (n2w (w2n a+32+j*msz):bytes32)) msz mem'` by
    (rpt strip_tac >> `w2n a+32+j*msz < dimword(:256)` by decide_tac >>
     simp[w2n_n2w, LESS_MOD] >> fs[] >> metis_tac[]) >>
  drule_all compile_abi_encode_static_info_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  `!v. not_fresh_at sa v ==> not_fresh_at sc v` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `w2n a+32+j*msz < dimword(:256) /\ w2n b+32+j*asz < dimword(:256)` by decide_tac >>
  `w2n b+32+(j+1)*asz = w2n b+32+j*asz+asz` by simp[RIGHT_ADD_DISTRIB] >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >- (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
    qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  gnvs[w2n_n2w, LESS_MOD, eval_operand_def] >>
  suspend "endpoint"
QED

Resume compile_abi_array_static_body_counted_ptr[endpoint]:
  `w2n b+(asz*(j+1)+32) = asz+(w2n b+(asz*j+32))` by
    simp[LEFT_ADD_DISTRIB] >>
  asm_rewrite_tac[] >>
  conj_tac >- (qpat_x_assum `ptr_covers G tn ip s 32` mp_tac >>
    simp[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- (qpat_x_assum `ptr_covers G tn src s scap` mp_tac >>
    simp[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- (qpat_x_assum `ptr_covers G tn dst s dcap` mp_tac >>
    simp[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- suspend "index" >>
  suspend "parent"
QED

Resume compile_abi_array_static_body_counted_ptr[index]:
  `mem_bytes_at (w2n p) 32 sf'.vs_memory = mem_bytes_at (w2n p) 32 s.vs_memory` by
    (irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     `mem_bytes_at (w2n p+x) 1 sf'.vs_memory = mem_bytes_at (w2n p+x) 1 s.vs_memory` by
       (qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
        simp[mem_agree_outside_def] >> strip_tac >> first_x_assum irule >>
        simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  fs[mem_bytes_at_def, mload_def]
QED

Resume compile_abi_array_static_body_counted_ptr[parent]:
  `mem_bytes_at (w2n a) scap sf'.vs_memory = mem_bytes_at (w2n a) scap s.vs_memory` by
    (irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     `mem_bytes_at (w2n a+x) 1 sf'.vs_memory = mem_bytes_at (w2n a+x) 1 s.vs_memory` by
       (qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
        simp[mem_agree_outside_def] >> strip_tac >> first_x_assum irule >>
        simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  qmatch_goalsub_abbrev_tac `mem_agree_outside mf` >>
  `!i. i < scap ==> (w2n a+i IN mf <=> w2n a+i IN tn.t_mem)` by
    (simp[Abbr `mf`] >> rpt strip_tac >> decide_tac) >>
  rpt strip_tac >> drule_all copied_window_agree_witness >> strip_tac >>
  `abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    (w2n a) scap mix` by metis_tac[] >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED

Finalise compile_abi_array_static_body_counted_ptr

(* Semantic endpoint corollary: the old prefix is framed, including when
   the selected element has zero size. Instantiate prefix with the already
   encoded array header and preceding elements; no allocation assumption. *)
Theorem abi_array_static_body_prefix_frame:
  mem_agree_outside {i | b+32+j*asz <= i /\ i < b+32+(j+1)*asz}
    mf mi /\
  tf = ti DIFF {i | b+32+j*asz <= i /\ i < b+32+(j+1)*asz} /\
  mem_bytes_at b (32+j*asz) mi = prefix /\
  mem_bytes_at (b+32+j*asz) asz mf = enc ty v /\
  (!i. b <= i /\ i < b+32+j*asz ==> i NOTIN ti) ==>
  mem_bytes_at b (32+j*asz) mf = prefix /\
  mem_bytes_at b (32+(j+1)*asz) mf = prefix ++ enc ty v /\
  (!i. b <= i /\ i < b+32+(j+1)*asz ==> i NOTIN tf)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `mem_bytes_at b (32+j*asz) mf = mem_bytes_at b (32+j*asz) mi` by
    (irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     `mem_bytes_at (b+x) 1 mf = mem_bytes_at (b+x) 1 mi` by
       (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[] >> decide_tac) >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  conj_tac >- simp[] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[IN_DIFF, GSPECIFICATION] >>
    Cases_on `i < b+32+j*asz` >> fs[] >> decide_tac) >>
  `32+(j+1)*asz = (32+j*asz)+asz` by simp[RIGHT_ADD_DISTRIB] >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[mem_bytes_at_split_padded] >>
  `b+(32+j*asz) = b+32+j*asz` by decide_tac >>
  pure_asm_rewrite_tac[] >> REFL_TAC
QED
