(* Valid wrapped Bytes/String input establishes the real singleton child input. *)
Theory abiValidWrappedBytesInput
Ancestors
  abiValidSingletonBytes abiValidSingletonSetup abiDecoderValidBytes abiDecoderBytes
  abiDecoderSingletonSetup abiDecoderReservation abiDecoderContract
  abiEncoder compileEnv emitHelperProps venomState contractABI vyperABI
  words list arithmetic

Definition abi_valid_wrapped_bytes_pre_def:
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s <=>
    (at = Bytes NONE \/ at = String) /\ valid_enc (Tuple [at]) bs /\
    dec (Tuple [at]) bs = ListV [contractABI$BytesV payload] /\ LENGTH payload <= n /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
    n < dimword (:256) /\ sb + LENGTH bs < dimword (:256) /\
    d + abi_decode_bytes_copy_size n < dimword (:256) /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    fresh_vars_wrt st s /\
    (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
       sb + LENGTH bs <= h /\ h < dimword (:256))
End

Theorem abi_valid_wrapped_bytes_setup_pre:
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s ==>
  abi_valid_singleton_setup_pre st src dst MLOAD hi sb d (abi_head_word bs) s
Proof
  simp_tac bool_ss [abi_valid_wrapped_bytes_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_singleton_bytes_decode >> strip_tac >>
  drule_all abi_valid_singleton_bytes_load >> strip_tac >>
  asm_simp_tac bool_ss [abi_valid_singleton_setup_pre_def,
    abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >> simp[] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `h` >> simp[] >> decide_tac
QED

Theorem abi_valid_wrapped_bytes_child_pre:
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s /\
  eval_operand child_src t = SOME (n2w (sb + abi_head_word bs)) /\
  eval_operand child_dst t = SOME (n2w d) /\ fresh_vars_wrt st' t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_memory = s.vs_memory ==>
  abi_decoder_valid_bytes_pre n at (DROP (abi_head_word bs) bs) payload
    st' child_src child_dst MLOAD hi (sb + abi_head_word bs) d t
Proof
  strip_tac >> qpat_x_assum `abi_valid_wrapped_bytes_pre _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_wrapped_bytes_pre_def]) >>
  drule_all abi_valid_singleton_bytes_decode >> strip_tac >>
  drule_all abi_valid_singleton_bytes_load >> strip_tac >>
  `sb + abi_head_word bs + LENGTH (DROP (abi_head_word bs) bs) < dimword (:256)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `mem_bytes_at (sb + abi_head_word bs) (LENGTH (DROP (abi_head_word bs) bs))
    (abi_decode_source MLOAD t) = DROP (abi_head_word bs) bs` by
    fs[abi_decode_source_def, Excl "dec_def", Excl "valid_enc_def"] >>
  asm_simp_tac bool_ss [abi_decoder_valid_bytes_pre_def, abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >> simp[] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `h` >> simp[LENGTH_DROP] >> decide_tac
QED

Theorem abi_valid_wrapped_bytes_setup:
  abi_decode_singleton_setup dst src MLOAD hi st = ((child_src,child_dst),st') /\
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_valid_bytes_pre n at (DROP (abi_head_word bs) bs) payload
      st' child_src child_dst MLOAD hi (sb + abi_head_word bs) d t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    inst_extends st st'
Proof
  strip_tac >> drule abi_valid_wrapped_bytes_setup_pre >> strip_tac >>
  drule_all abi_valid_singleton_setup_sequence >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')` by fs[listTheory.EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all abi_valid_wrapped_bytes_child_pre >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_WRAPPED_BYTES_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid wrapped bytes input not kernel closed: " ^ n)
  end) (DB.thms "abiValidWrappedBytesInput");
