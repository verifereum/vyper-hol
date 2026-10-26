(* Dynamic singleton setup supplies the actual typed recursive child contract. *)
Theory abiDecoderSingletonTyped
Ancestors
  abiDecoderSingleton abiDecoderSingletonSetup abiDecoderTypedCompose
  abiDecoderTypedContract abiDecoderReservation abiDecoderCoherence abiDecoderContract
  exprLowering compileEnv emitHelperProps valueEncoding vyperABI
  venomExecSemantics venomState venomInst words list

Theorem abi_decoder_singleton_setup:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_decoder_pre ce env (TupleT [ty]) (TupleTV [tv]) di
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s /\
  is_dynamic (vyper_to_abi_type env ty) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_pre ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      av v st' last child_src child_dst opc hi (sb + 32) d b cap t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_decoder_singleton_setup_pre >> strip_tac >>
  drule_all abi_decode_singleton_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all abi_decoder_pre_pure_transport >> strip_tac >>
  drule_all abi_decoder_singleton_pre_child >> strip_tac >>
  `abi_decoder_pre ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
     av v st' last child_src child_dst opc hi (sb + 32) d b cap t` by
    (drule_all abi_decoder_pre_destination_value >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_decoder_singleton_recursive_setup:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv]) di
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s /\
  is_dynamic (vyper_to_abi_type env ty) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty)
      av v st' last child_src child_dst opc hi (sb + 32) d b cap t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by
    gvs[abi_decoder_recursive_pre_def, abi_decoder_coherent_tuple_iff] >>
  `abi_decoder_pre ce env (TupleT [ty]) (TupleTV [tv])
     (type_to_abi_dec_info ce.ce_struct_fields ce (TupleT [ty]))
     (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap s` by
    fs[abi_decoder_recursive_pre_def] >>
  drule_all abi_decoder_singleton_setup >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_recursive_pre_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_SINGLETON_TYPED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI dynamic singleton setup not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderSingletonTyped");
