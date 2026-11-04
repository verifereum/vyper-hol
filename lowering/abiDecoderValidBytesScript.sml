(* Actual Bytes/String decoder execution from valid, possibly noncanonical input.
   TOP-LEVEL: pure source contract and sequence execution with allocation frame. *)
Theory abiDecoderValidBytes
Ancestors
  abiValidBytes abiDecoderBytes abiDecoderBytesTyped abiDecoderBytesFrame
  abiDecoderString abiDecoderVarSequence abiDecoderContract abiDecoderFrame abiDecoderReservation
  valueEncoding valueEncodingProps abiEncoder emitHelper compileEnv
  venomExecSemantics venomState contractABI words list arithmetic

Definition abi_decoder_valid_bytes_pre_def:
  abi_decoder_valid_bytes_pre n at bs payload st src dst opc hi sb d s <=>
    (at = Bytes NONE \/ at = String) /\ vyper_decode_valid_enc at bs /\
    dec at bs = contractABI$BytesV payload /\ LENGTH payload <= n /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
    n < dimword (:256) /\ sb + LENGTH bs < dimword (:256) /\
    d + abi_decode_bytes_copy_size n < dimword (:256) /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decode_source_opcode opc /\ fresh_vars_wrt st s /\
    (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
       sb + LENGTH bs <= h /\ h < dimword (:256))
End

Theorem abi_decoder_valid_bytes_facts:
  abi_decoder_valid_bytes_pre n at bs payload st src dst opc hi sb d s ==>
  abi_decode_load opc (n2w sb:bytes32) s = n2w (LENGTH payload) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload)
    sb (abi_decode_source opc s) /\
  val_wf (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + 32 + LENGTH payload <= h /\ h < dimword (:256))
Proof
  simp_tac bool_ss [abi_decoder_valid_bytes_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_bytes_decode >> strip_tac >>
  `sb < dimword (:256)` by decide_tac >>
  drule_all abi_valid_bytes_count_load >> strip_tac >>
  drule_all abi_valid_bytes_source_layout >> strip_tac >>
  mp_tac (cj 3 abi_decoder_bytes_copy_size) >> strip_tac >>
  simp_tac bool_ss [val_wf_def, GSYM (cj 2 abi_decoder_bytes_copy_size)] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
  Cases_on `hi = Lit 0w` >> simp[] >>
  qpat_x_assum `_ \/ _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `h` >> simp[] >> decide_tac
QED

Theorem abi_decoder_valid_bytes_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_valid_bytes_pre n at bs payload st src dst opc hi sb d s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d t.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule abi_decoder_valid_bytes_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_bytes_pre_def]) >>
  drule_all abi_decode_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d t.vs_memory` by
    (irule val_in_memory_relocate >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`abi_decode_source opc s`, `abi_decode_bytes_copy_size n`, `sb`] >>
     asm_simp_tac bool_ss [cj 2 abi_decoder_bytes_copy_size, LESS_EQ_REFL, EQ_SYM_EQ]) >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss [abi_decoder_string_memory]
QED
