(* Source-labelled arbitrary scalar decoder execution. *)
Theory abiDecoderScalarOutcome
Ancestors
  valueEncodingDefs
  abiDecoderPrimitiveSource abiDecoderWordOutcome abiCanonicalHeadSize
  calldataReconstruction abiDecoderCoherence vyperTypeABI vyperTypeSystem
  exprLowering compileEnv vyperValue valueEncoding words list arithmetic
  abiDecoderSourceFacts abiDecoderClampOutcome

Theorem abi_decoder_primitive_is_word:
  assignable_type env ty /\ abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  is_word_type ty
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[type_to_abi_dec_info_def, is_word_type_def]
  >- (Cases_on `b` >> gvs[type_to_abi_dec_info_def, is_word_type_def] >>
      Cases_on `b'` >> gvs[type_to_abi_dec_info_def, is_word_type_def,
        assignable_type_def, well_formed_type_def, evaluate_type_def, AllCaseEqs()])
  >- (Cases_on `b` >> gvs[type_to_abi_dec_info_def]) >>
  gvs[abi_decoder_coherent_struct_iff, assignable_type_def, AllCaseEqs()]
QED

Theorem abi_decoder_primitive_memory_intro:
  LENGTH (bs:byte list) = 32 /\ assignable_type env ty /\
  abi_decode_bytes_widths env ty /\ abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
  mem_word_at d mem = word_of_bytes T (0w:bytes32) bs ==>
  val_in_memory tv v d mem
Proof
  strip_tac >>
  `is_word_type ty` by (drule_all abi_decoder_primitive_is_word >> simp[]) >>
  `evaluate_type env ty = SOME tv` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `value_has_type tv v` by (irule (cj 1 abi_to_vyper_well_typed) >> metis_tac[]) >>
  drule_all abi_decoder_primitive_source_word >> strip_tac >>
  irule calldata_word_representation >> metis_tac[]
QED

Theorem abi_decoder_scalar_source_outcome:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand hi s = SOME (n2w H) /\ pos+32 <= H /\
  B+H < dimword (:256) /\ d+32 < dimword (:256) /\
  fresh_vars_wrt st s /\ abi_decoder_clamp_wf clamp /\
  decode_site_resources ctx fn s /\ {a | d <= a /\ a < d+32} SUBSET writes /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  bs = mem_bytes_at (B+pos) 32 (abi_decode_source opc s) ==>
  ((?t v. run_inst_seq (emitted_insts st st') s = OK t /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
    val_in_memory tv v d t.vs_memory /\
    mem_word_at d t.vs_memory = abi_decode_load opc (n2w (B+pos):bytes32) s /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
   (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
      ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v)))
Proof
  strip_tac >>
  `B+pos < dimword (:256)` by decide_tac >>
  `LENGTH (bs:byte list) = 32` by simp[mem_bytes_at_def] >>
  `abi_decode_load opc (n2w (B+pos):bytes32) s =
     word_of_bytes T (0w:bytes32) bs` by (drule abi_decode_load_bytes >> simp[]) >>
  drule_all abi_decoder_primitive_source_acceptance >> strip_tac >>
  drule_all abi_decoder_word_finite_outcome >>
  disch_then (qspec_then `next` strip_assume_tac)
  >- (disj1_tac >>
      `vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
       ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v`
        by metis_tac[] >>
      `val_in_memory tv v d t.vs_memory` by
        (irule abi_decoder_primitive_memory_intro >> metis_tac[]) >>
      metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem abi_decoder_primitive_clamp_wf:
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  abi_decoder_clamp_wf clamp
Proof
  strip_tac >>
  `is_word_type ty` by (drule_all abi_decoder_primitive_is_word >> simp[]) >>
  Cases_on `ty` >> gvs[is_word_type_def, type_to_abi_dec_info_def]
  >- (drule_all abi_decode_checker_clamp_wf >>
      Cases_on `b` >> gvs[type_to_abi_dec_info_def] >>
      Cases_on `b'` >> gvs[type_to_abi_dec_info_def]) >>
  gvs[abi_decoder_coherent_flag_iff] >>
  rw[abi_decoder_clamp_wf_def]
QED
