(* Recover concrete instruction sites from the compiler's phase trace. *)
Theory bodyPtrAbiEncodeBytesSites
Ancestors
  bodyPtrAbiEncodeBytesPrefix bodyPtrAbiEncodeBytesCopy bodyPtrAbiEncodeStaticChild
  abiEncoderBytesCode abiEncoderBytesPrefix emitHelperProps exprLoweringProps
  compileEnv emitHelper list rich_list arithmetic

Theorem abi_encode_bytes_prefix_length:
  abi_encode_bytes_prefix dst src st = (ops,en) ==>
  LENGTH (emitted_insts st en) = 4
Proof
  strip_tac >> drule abi_encode_bytes_prefix_trace >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> simp[]
QED

Theorem abi_encode_bytes_copy_length:
  abi_encode_bytes_copy dst src len last st = ((),en) ==>
  LENGTH (emitted_insts st en) = 3
Proof
  strip_tac >> drule abi_encode_bytes_copy_trace >> strip_tac >>
  imp_res_tac emitted_insts_emit_void >> simp[]
QED

Theorem abi_encode_bytes_phase_sites:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,en) /\
  isPREFIX (emitted_insts st en) (DROP k code) ==>
  ?ops ready copied.
    abi_encode_bytes_prefix dst src st = (ops,ready) /\
    abi_encode_bytes_copy dst src (FST ops) (SND ops) ready = ((),copied) /\
    abi_encode_bytes_suffix (FST ops) copied = (out,en) /\
    isPREFIX (emitted_insts st ready) (DROP k code) /\
    isPREFIX (emitted_insts ready copied) (DROP (k+4) code) /\
    isPREFIX (emitted_insts copied en) (DROP (k+7) code)
Proof
  strip_tac >> drule abi_encode_bytes_trace >> strip_tac >>
  drule abi_encode_bytes_prefix_shape >> strip_tac >>
  drule abi_encode_bytes_copy_shape >> strip_tac >>
  drule abi_encode_bytes_suffix_shape >> strip_tac >>
  `emitted_insts st en = emitted_insts st ready ++
     emitted_insts ready copied ++ emitted_insts copied en` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  drule abi_encode_bytes_prefix_length >> strip_tac >>
  drule abi_encode_bytes_copy_length >> strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> strip_tac >>
  drule abi_encode_static_child_sites >> simp[] >> strip_tac >>
  drule abi_encode_static_child_sites >> simp[] >> strip_tac >>
  qexistsl_tac [`ops`, `ready`, `copied`] >> simp[]
QED
