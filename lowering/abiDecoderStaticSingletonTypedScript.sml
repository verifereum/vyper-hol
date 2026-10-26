(* Typed static singleton setup, including the wrapped uint256 path. *)
Theory abiDecoderStaticSingletonTyped
Ancestors
  abiDecoderStaticSingleton abiDecoderWordTyped abiDecoderLayout
  abiDecoderTypedContract abiDecoderTypedCompose abiDecoderCoherence
  abiDecoderDynamic abiDecodeRanges
  abiDecoderReservation abiDecoderContract exprLowering compileEnv
  emitHelperProps valueEncoding vyperABI contractABI
  venomExecSemantics venomState venomInst words list

Theorem abi_decoder_pre_operands:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s /\
  eval_operand child_src s = SOME (n2w sb) /\
  eval_operand child_dst s = SOME (n2w d) ==>
  abi_decoder_pre ce env ty tv di av v st last child_src child_dst opc hi sb d b cap s
Proof
  rw[abi_decoder_pre_def, abi_decoder_ranges_def]
QED

Theorem abi_decoder_static_singleton_child:
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(di,head_sz,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s ==>
  abi_decoder_recursive_pre ce env sf ty tv di av v
    st last src dst opc hi sb d b cap s /\
  type_memory_bytes ce ty = mem_sz /\
  LENGTH (enc (vyper_to_abi_type env ty) av) = head_sz /\
  head_sz = mem_sz /\ ~abi_decoder_dynamic di
Proof
  strip_tac >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_tuple_iff] >>
  `type_to_abi_dec_info sf ce ty = di /\
   ~is_abi_dynamic ce.ce_struct_fields ty /\
   abi_embedded_static_size ce.ce_struct_fields ty = head_sz /\
   type_memory_bytes ce ty = mem_sz` by
    (qpat_x_assum `DecComplex F _ = type_to_abi_dec_info sf ce (TupleT [ty])` mp_tac >>
     simp[Once type_to_abi_dec_info_def] >> metis_tac[]) >>
  `abi_decoder_header ce env ty tv` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv`
      (mp_tac o MATCH_MP abi_decoder_coherent_header) >> simp[]) >>
  `~is_dynamic (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
  `head_sz = mem_sz` by gvs[abi_decoder_header_def, abi_member_head_size_def] >>
  `~abi_decoder_dynamic di` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv`
       (mp_tac o MATCH_MP abi_decoder_coherent_dynamic) >> asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_static_singleton_pre_child >> strip_tac >>
  `abi_decoder_metadata ce env ty tv
     (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v` by fs[abi_decoder_pre_def] >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = head_sz` by
    (drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  simp[abi_decoder_recursive_pre_def]
QED

Theorem abi_decoder_static_singleton_setup:
  abi_decode_static_singleton_setup dst src hi head_sz st = ((child_src,child_dst),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(di,head_sz,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_recursive_pre ce env sf ty tv di av v
      st' last child_src child_dst opc hi sb d b cap t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_decoder_static_singleton_child >> strip_tac >>
  `abi_decode_static_singleton_setup_pre st src dst hi head_sz sb d s` by
    (qpat_assum `abi_decoder_recursive_pre ce env sf ty tv di
       av v st last src dst opc hi sb d b cap s` mp_tac >>
     pure_rewrite_tac [abi_decode_static_singleton_setup_pre_def,
       abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all abi_decode_static_singleton_setup_sequence >> strip_tac >>
  drule_all abi_decode_static_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  `abi_decoder_pre ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
     av v st last src dst opc hi sb d b cap s` by fs[abi_decoder_recursive_pre_def] >>
  drule_all abi_decoder_pre_pure_transport >> strip_tac >>
  drule_all abi_decoder_pre_operands >> strip_tac >>
  qexists_tac `t` >> gvs[abi_decoder_recursive_pre_def]
QED

Theorem abi_decoder_static_singleton_word_child =
  SIMP_RULE bool_ss [abi_decoder_dynamic_def]
    (Q.INST [`di` |-> `DecPrimWord NoClamp`, `head_sz` |-> `32`, `mem_sz` |-> `32`]
      abi_decoder_static_singleton_child);

Theorem abi_decoder_static_singleton_word_setup =
  Q.INST [`di` |-> `DecPrimWord NoClamp`, `head_sz` |-> `32`, `mem_sz` |-> `32`]
    abi_decoder_static_singleton_setup;

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_STATIC_SINGLETON_TYPED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI typed static singleton not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderStaticSingletonTyped");
