(* Actual static singleton execution and its unwrapped memory result. *)
Theory abiDecoderStaticSingletonFragment
Ancestors
  abiDecoderStaticSingletonTyped abiDecoderStaticSingleton abiDecoderSingletonFragment
  abiDecoderTypedCompose abiDecoderWordTyped abiDecoderTypedContract
  abiDecoderPrimitive abiDecoderClampedWord
  abiDecoderCoherence abiDecoderContract abiDecoderBytesTyped abiDecoderDynamic
  abiDecoderGuards
  abiEncoder exprLoweringProps compileEnv emitHelper emitHelperProps valueEncoding
  fragExec venomExecSemantics venomState venomInst words rich_list list combin

Theorem abi_decoder_static_wrapped_word_sequence:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex F [(DecPrimWord clamp,32,32)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(DecPrimWord clamp,32,32)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v])) st' d 32 b cap s t
Proof
  strip_tac >>
  `~abi_decoder_dynamic (DecPrimWord clamp)` by simp[abi_decoder_dynamic_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_singleton_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_static_singleton_setup dst src hi 32 st = (child_ops,c1)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_static_singleton_setup dst src hi 32 st = ((child_src,child_dst),c1)` >>
  `compile_abi_decode_to_buf child_dst child_src opc hi (DecPrimWord clamp) c1 =
     ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decoder_static_singleton_setup >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK mid` >>
  drule_all abi_decoder_typed_primitive_word_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') mid = OK t` >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `inst_extends c1 st'` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v])) st' d 32 b cap s t` by
    (simp_tac bool_ss [abi_decoder_singleton_post] >>
     drule_all abi_decoder_post_pure_prefix >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_decoder_static_unwrapped_word_sequence =
  SIMP_RULE bool_ss [abi_decoder_singleton_post] abi_decoder_static_wrapped_word_sequence;

Theorem abi_decoder_static_wrapped_word_shape:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex F [(DecPrimWord clamp,32,32)]) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >>
  `~abi_decoder_dynamic (DecPrimWord clamp)` by simp[abi_decoder_dynamic_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_singleton_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_static_singleton_setup dst src hi 32 st = (child_ops,c1)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_static_singleton_setup dst src hi 32 st = ((child_src,child_dst),c1)` >>
  `compile_abi_decode_to_buf child_dst child_src opc hi (DecPrimWord clamp) c1 =
     ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decode_static_singleton_setup_shape >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `inst_extends st c1 /\ inst_extends c1 st'` by
    (conj_tac >> irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  gvs[EVERY_CONJ] >> irule IS_PREFIX_TRANS >> qexists_tac `c1.cs_current_insts` >> simp[]
QED

Theorem abi_decoder_static_wrapped_word_from_state:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex F [(DecPrimWord clamp,32,32)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(DecPrimWord clamp,32,32)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v])) st' d 32 b cap initial) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_static_wrapped_word_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_static_wrapped_word_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx]
QED

Theorem abi_decoder_static_unwrapped_word_from_state =
  SIMP_RULE bool_ss [abi_decoder_singleton_post_function]
    abi_decoder_static_wrapped_word_from_state;

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_STATIC_SINGLETON_FRAGMENT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI static wrapped word execution not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderStaticSingletonFragment");
