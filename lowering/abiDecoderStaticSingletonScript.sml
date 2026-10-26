(* Static singleton prefixes keep the source at offset zero. *)
Theory abiDecoderStaticSingleton
Ancestors
  abiDecoderSingletonSetup
  abiDecoderSingleton abiDecoderTypedContract abiDecoderTypedCompose abiDecoderComplexHead
  abiDecoderGuard abiDecoderGuards abiDecoderDynamic abiDecoderBytesBound abiDecoderOffset
  abiDecoderReservation abiDecoderContract abiEncoder compileEnv emitHelper emitHelperProps
  exprLoweringProps valueEncoding vyperABI contractABI venomExecSemantics venomState venomInst
  words arithmetic list rich_list

Theorem canonical_static_singleton_encoding:
  ~is_dynamic aty ==> enc (Tuple [aty]) (ListV [av]) = enc aty av
Proof
  simp[enc_def, head_lengths_def, REV_REVERSE_LEM]
QED

Theorem abi_decoder_static_singleton_pre_child:
  abi_decoder_pre ce env (TupleT [ty]) (TupleTV [tv]) di
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s /\
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  abi_decoder_pre ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    av v st last src dst opc hi sb d b cap s
Proof
  pure_rewrite_tac[abi_decoder_pre_def] >> strip_tac >>
  drule_all abi_decoder_singleton_metadata_child >> strip_tac >>
  gvs[vyper_to_abi_type_def, canonical_static_singleton_encoding,
      type_memory_bytes_def, Excl "enc_def"]
QED

Definition abi_decode_static_singleton_setup_def:
  abi_decode_static_singleton_setup dst src hi head_sz =
    do abi_decode_complex_head_guard src hi head_sz;
       child_src <- emit_op ADD [src; Lit 0w];
       child_dst <- emit_op ADD [dst; Lit 0w];
       return (child_src,child_dst)
    od
End

Definition abi_decode_static_singleton_setup_pre_def:
  abi_decode_static_singleton_setup_pre st src dst hi head_sz sb d s <=>
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    fresh_vars_wrt st s /\
    (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                        sb + head_sz <= h /\ h < dimword (:256))
End

Theorem abi_decode_static_singleton_setup_sequence:
  abi_decode_static_singleton_setup dst src hi head_sz st =
    ((child_src,child_dst),st') /\
  abi_decode_static_singleton_setup_pre st src dst hi head_sz sb d s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_src t = SOME (n2w sb) /\
    eval_operand child_dst t = SOME (n2w d) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_static_singleton_setup_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `abi_decode_complex_head_guard src hi head_sz st = (guard_result,c1)` >>
  rename1 `emit_op ADD [src; Lit 0w] c1 = (child_src,c2)` >>
  rename1 `emit_op ADD [dst; Lit 0w] c2 = (child_dst,st')` >>
  Cases_on `guard_result` >> gvs[] >>
  qpat_x_assum `abi_decode_static_singleton_setup_pre _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decode_static_singleton_setup_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_complex_head_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `eval_operand (Lit 0w) s1 = SOME 0w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit 0w) s2 = SOME 0w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  `run_inst_seq (emitted_insts c1 st') s1 = OK t /\ inst_extends c1 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_static_singleton_setup_shape:
  abi_decode_static_singleton_setup dst src hi head_sz st =
    ((child_src,child_dst),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  st.cs_next_id <= st'.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_static_singleton_setup_def, abi_decode_complex_head_guard_def,
       abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       emitted_insts_def, IS_PREFIX_APPEND] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_static_singleton_members[local]:
  ~abi_decoder_dynamic di ==>
  compile_abi_decode_complex_elems dst src opc hi [(di,head_sz,mem_sz)] 0 0 =
    do child_src <- emit_op ADD [src; Lit 0w];
       child_dst <- emit_op ADD [dst; Lit 0w];
       compile_abi_decode_to_buf child_dst child_src opc hi di
    od
Proof
  strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  simp[FUN_EQ_THM, abi_decoder_dynamic_case, abi_decode_complex_nil,
       abi_decoder_needs_offset_iff,
       compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_static_singleton_phases:
  ~abi_decoder_dynamic di ==>
  compile_abi_decode_to_buf dst src opc hi (DecComplex F [(di,head_sz,mem_sz)]) =
    do child_ops <- abi_decode_static_singleton_setup dst src hi head_sz;
       compile_abi_decode_to_buf (SND child_ops) (FST child_ops) opc hi di
    od
Proof
  strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  Cases_on `hi = Lit 0w` >>
  simp[FUN_EQ_THM, abi_decode_static_singleton_setup_def,
       abi_decode_complex_head_guard_def, abi_decode_le_guard_def,
       abi_static_singleton_members, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED
