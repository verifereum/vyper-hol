(* Typed decoder composition across fresh operands and pure prefixes. *)
Theory abiDecoderTypedCompose
Ancestors
  abiDecoderTypedContract abiBoundaryChecks abiDecoderFrame abiDecoderContract
  emitHelperProps exprLoweringProps valueEncoding venomState list rich_list

Theorem abi_decoder_pre_destination:
  eval_operand dst' s = eval_operand dst s ==>
  (abi_decoder_pre ce env ty tv di av v st last src dst' opc hi sb d b cap s <=>
   abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s)
Proof
  simp[abi_decoder_pre_def, abi_decoder_ranges_def]
QED

Theorem abi_decoder_pre_destination_value:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s /\
  eval_operand dst' s = SOME (n2w d) ==>
  abi_decoder_pre ce env ty tv di av v st last src dst' opc hi sb d b cap s
Proof
  rw[abi_decoder_pre_def, abi_decoder_ranges_def]
QED

Theorem abi_decoder_singleton_post:
  abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v])) st' d outsz b cap s0 s <=>
  abi_decoder_post tv v st' d outsz b cap s0 s
Proof
  simp[abi_decoder_post_def, val_in_memory_singleton_tuple]
QED

Theorem abi_decoder_post_pure_prefix:
  abi_decoder_post tv v st' d outsz b cap mid t /\
  (!op w. eval_operand op s0 = SOME w ==> eval_operand op mid = SOME w) /\
  mid.vs_memory = s0.vs_memory /\ mid.vs_call_ctx = s0.vs_call_ctx /\
  mid.vs_data_section = s0.vs_data_section ==>
  abi_decoder_post tv v st' d outsz b cap s0 t
Proof
  rw[abi_decoder_post_def, abi_decode_footprint_frame_def] >> metis_tac[]
QED

Theorem abi_decoder_inst_extends_prefix:
  isPREFIX st.cs_current_insts st'.cs_current_insts ==> inst_extends st st'
Proof
  rw[IS_PREFIX_APPEND, inst_extends_def, emitted_insts_def] >>
  simp[DROP_LENGTH_APPEND]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_TYPED_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI typed decoder composition not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderTypedCompose");
