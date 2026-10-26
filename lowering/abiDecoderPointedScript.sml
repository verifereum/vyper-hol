(* Decoder fragments tied to the actual initial state, for recursive composition. *)
Theory abiDecoderPointed
Ancestors
  fragExec abiDecoderBytesTyped abiDecoderWordTyped abiDecoderBulkFragment
  abiDecoderTypedContract abiDecoderCoherence abiDecoderContract
  abiDecoderBytes abiEncoder compileEnv exprLoweringProps valueEncoding
  venomExecSemantics venomState words
  instIdxIndep combin

Theorem frag_exec_initial_family:
  (!initial. P initial ==>
    frag_exec ctx st st' (\s. s = initial) (Q initial) R) ==>
  frag_exec ctx st st' P (\t. ?initial. P initial /\ Q initial t) R
Proof
  strip_tac >> simp_tac bool_ss [frag_exec_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!initial. _` (qspec_then `s` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (mp_tac o PURE_REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >> asm_simp_tac bool_ss [] >>
  strip_tac
  >- (rename1 `Q s reached` >> disj1_tac >> qexists_tac `reached` >>
      asm_simp_tac bool_ss [] >> qexists_tac `s` >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem frag_exec_initial_pre:
  (!initial. P initial ==>
    frag_exec ctx st st' (\s. s = initial) U R) ==>
  frag_exec ctx st st' P U R
Proof
  strip_tac >>
  `frag_exec ctx st st' P (\t. ?initial. P initial /\ U t) R` by
    (irule (SIMP_RULE bool_ss [K_THM]
       (Q.INST [`Q` |-> `K U`] frag_exec_initial_family)) >> simp[]) >>
  irule frag_exec_conseq >>
  qexistsl_tac [`P`, `\t. ?initial. P initial /\ U t`, `R`] >> simp[] >> metis_tac[]
QED

Theorem frag_exec_initial_seq:
  frag_exec ctx st middle P Q R /\
  (!initial. Q initial ==>
    frag_exec ctx middle st' (\s. s = initial) U R) /\
  cs_extends st middle /\ cs_extends middle st' ==>
  frag_exec ctx st st' P U R
Proof
  strip_tac >>
  `frag_exec ctx middle st' Q U R` by
    (irule frag_exec_initial_pre >> simp[]) >>
  irule frag_exec_seq >> qexistsl_tac [`Q`, `middle`] >> simp[]
QED

Theorem abi_decoder_pre_inst_idx:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap
    (s with vs_inst_idx := ix) <=>
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s
Proof
  simp[abi_decoder_pre_def, abi_decoder_ranges_def, abi_decoder_reservation_def,
       fresh_vars_wrt_def, lookup_var_def, eval_op_inst_idx, abi_decode_source_def]
QED

Theorem abi_decoder_recursive_pre_inst_idx:
  abi_decoder_recursive_pre ce env sf ty tv di av v st last src dst opc hi sb d b cap
    (s with vs_inst_idx := ix) <=>
  abi_decoder_recursive_pre ce env sf ty tv di av v st last src dst opc hi sb d b cap s
Proof
  simp[abi_decoder_recursive_pre_def, abi_decoder_pre_inst_idx]
QED

Theorem abi_decoder_typed_bytes_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
    (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
    st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs)
      st' d (abi_decode_bytes_copy_size n) b cap initial) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_typed_bytes_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx]
QED

Theorem abi_decoder_typed_word_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord NoClamp) av v
    st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post tv v st' d 32 b cap initial) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_word_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_typed_unclamped_word_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx]
QED

Theorem abi_decoder_typed_bulk_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
    (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
      st' d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_typed_bulk_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_POINTED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder initial-state fragment not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPointed");
