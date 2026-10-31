(* Evaluated tuple arguments carry complete encoder sources. The owned source
   prefix is separated from the tuple temporary; unused capacity may overlap. *)
Theory abiTupleEncodeInput
Ancestors
  abiEncoderInput abiEncoderInputFrame abiBuiltinEncodeWord abiDecoderReentry abiDecoderContract
  compileEnv exprLowering venomState venomExecSemantics words list arithmetic

Definition abi_tuple_encode_input_def:
  abi_tuple_encode_input sf ce ty at av op next lo hi s <=>
    abi_decoder_operand_live next op /\ type_memory_bytes ce ty < dimword (:256) /\
    if is_word_type ty then
      ?w. eval_operand op s = SOME w /\ has_type at av /\ ~is_dynamic at /\
        static_length at = 32 /\ word_to_bytes w T = enc at av
    else
      ?sb source_cap. eval_operand op s = SOME (n2w sb) /\ sb < dimword (:256) /\
        source_cap <= type_memory_bytes ce ty /\
        abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap s.vs_memory /\
        (sb+source_cap <= lo \/ hi <= sb)
End

Theorem abi_tuple_encode_input_transport:
  abi_tuple_encode_input sf ce ty at av op next lo hi s /\ next <= later /\ lo <= hi /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\ abi_decode_frame lo (hi-lo) s t ==>
  abi_tuple_encode_input sf ce ty at av op later lo hi t
Proof
  simp_tac bool_ss [abi_tuple_encode_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live later op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [] >> Cases_on `is_word_type ty`
  >- (gvs[] >> qexists_tac `w` >> asm_simp_tac bool_ss [] >> first_x_assum irule >> simp[]) >>
  gvs[] >>
  rename1 `abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap s.vs_memory` >>
  qexistsl_tac [`sb`, `source_cap`] >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_input_mem_agree >> qexists_tac `s.vs_memory` >> asm_simp_tac bool_ss [] >>
  irule EQ_SYM >> qpat_x_assum `abi_decode_frame _ _ _ _`
    (MP_TAC o CONJUNCT1 o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  disch_then irule >> decide_tac
QED

Definition abi_tuple_encode_inputs_def:
  abi_tuple_encode_inputs sf ce [] ats avs next lo hi s = (ats = [] /\ avs = []) /\
  abi_tuple_encode_inputs sf ce ((op,ty)::xs) ats avs next lo hi s =
    ?at ts av vs. ats = at::ts /\ avs = av::vs /\
      abi_tuple_encode_input sf ce ty at av op next lo hi s /\
      abi_tuple_encode_inputs sf ce xs ts vs next lo hi s
End

Theorem abi_tuple_encode_inputs_lengths:
  !xs ats avs next lo hi s. abi_tuple_encode_inputs sf ce xs ats avs next lo hi s ==>
    LENGTH xs = LENGTH ats /\ LENGTH ats = LENGTH avs
Proof
  Induct >- simp[abi_tuple_encode_inputs_def] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_encode_inputs_def] >> rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem abi_tuple_encode_inputs_transport:
  !xs ats avs next later lo hi s t.
  abi_tuple_encode_inputs sf ce xs ats avs next lo hi s /\ next <= later /\ lo <= hi /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\ abi_decode_frame lo (hi-lo) s t ==>
  abi_tuple_encode_inputs sf ce xs ats avs later lo hi t
Proof
  Induct >- simp[abi_tuple_encode_inputs_def] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_encode_inputs_def] >> rpt gen_tac >> strip_tac >> gvs[] >> conj_tac
  >- (drule_all abi_tuple_encode_input_transport >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED
