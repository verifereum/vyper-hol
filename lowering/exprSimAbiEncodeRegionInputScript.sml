(* Empty-safe logical source separation for tuple staging. *)
Theory exprSimAbiEncodeRegionInput
Ancestors
  valueEncodingDefs
  abiTupleEncodeOpenInput abiEncoderOpenInput abiEncoderOpenInputFrame
  abiEncoderInputFrame abiDecoderReentry abiDecoderContract
  abiEncodeInputSupplier compileEnv exprLowering venomMemDefs venomState
  venomExecSemantics valueEncoding valueEncodingProps valueEncodingProofs words list arithmetic
  abiEncoderSourceAggregate abiEncoderSourceFootprint abiTupleEncodeLayout
  exprSimDefs exprSimProps valueEncodingTyping vyperTyping loweringPosts

Definition abi_encode_region_input_def:
  abi_encode_region_input sf ce ty at av op next lo hi s <=>
    abi_decoder_operand_live next op /\ type_memory_bytes ce ty < dimword (:256) /\
    if is_word_type ty then
      ?w. eval_operand op s = SOME w /\ has_type at av /\ ~is_dynamic at /\
        static_length at = 32 /\ word_to_bytes w T = enc at av
    else
      ?sb source_cap. eval_operand op s = SOME (n2w sb) /\ sb < dimword (:256) /\
        source_cap <= type_memory_bytes ce ty /\
        abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av sb source_cap s.vs_memory /\
        venomMemDefs$regions_disjoint (sb,source_cap) (lo,hi-lo)
End

Definition abi_encode_region_inputs_def:
  abi_encode_region_inputs sf ce [] ats avs next lo hi s = (ats = [] /\ avs = []) /\
  abi_encode_region_inputs sf ce ((op,ty)::xs) ats avs next lo hi s =
    ?at ts av vs. ats = at::ts /\ avs = av::vs /\
      abi_encode_region_input sf ce ty at av op next lo hi s /\
      abi_encode_region_inputs sf ce xs ts vs next lo hi s
End

Theorem abi_encode_region_input_empty_adapter:
  abi_encode_region_input sf ce ty at av op next lo hi s ==>
  abi_tuple_encode_open_input sf ce ty at av op next 0 0 s
Proof
  simp[abi_encode_region_input_def, abi_tuple_encode_open_input_def] >>
  Cases_on `is_word_type ty` >> simp[] >> metis_tac[]
QED

Theorem abi_encode_region_inputs_empty_adapter:
  !xs ats avs next lo hi s.
  abi_encode_region_inputs sf ce xs ats avs next lo hi s ==>
  abi_tuple_encode_open_inputs sf ce xs ats avs next 0 0 s
Proof
  Induct >- simp[abi_encode_region_inputs_def, abi_tuple_encode_open_inputs_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[abi_encode_region_inputs_def, abi_tuple_encode_open_inputs_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[abi_encode_region_input_empty_adapter]
QED

Theorem abi_encode_region_frame_slice:
  abi_decode_frame lo (hi-lo) s t /\ lo <= hi /\
  venomMemDefs$regions_disjoint (sb,cap) (lo,hi-lo) ==>
  mem_bytes_at sb cap s.vs_memory = mem_bytes_at sb cap t.vs_memory
Proof
  strip_tac >> Cases_on `cap = 0` >- simp[mem_bytes_at_def] >>
  fs[venomMemDefsTheory.regions_disjoint_def]
  >- (`hi = lo` by decide_tac >> gvs[] >>
      irule LIST_EQ >> simp[] >> gen_tac >> strip_tac >>
      `mem_bytes_at (sb+x) 1 s.vs_memory = mem_bytes_at (sb+x) 1 t.vs_memory` by
        (irule EQ_SYM >> fs[abi_decode_frame_def] >>
         first_x_assum irule >> decide_tac) >>
      pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >> simp[EL_mem_bytes_at]) >>
  irule EQ_SYM >> fs[abi_decode_frame_def] >> first_x_assum irule >> decide_tac
QED

Theorem abi_encode_region_input_transport:
  abi_encode_region_input sf ce ty at av op next lo hi s /\ next <= later /\ lo <= hi /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\ abi_decode_frame lo (hi-lo) s t ==>
  abi_encode_region_input sf ce ty at av op later lo hi t
Proof
  simp_tac bool_ss [abi_encode_region_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live later op` by
    (irule abi_decoder_operand_live_mono >> qexists `next` >> simp[]) >>
  Cases_on `is_word_type ty` >> gvs[]
  >- (qexists `w` >> simp[] >> first_x_assum irule >> simp[]) >>
  qexistsl [`sb`, `source_cap`] >> simp[] >>
  irule abi_encoder_open_input_mem_agree >> qexists `s.vs_memory` >> simp[] >>
  drule_all abi_encode_region_frame_slice >> simp[]
QED

Theorem abi_encode_region_inputs_transport:
  !xs ats avs next later lo hi s t.
  abi_encode_region_inputs sf ce xs ats avs next lo hi s /\ next <= later /\ lo <= hi /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\ abi_decode_frame lo (hi-lo) s t ==>
  abi_encode_region_inputs sf ce xs ats avs later lo hi t
Proof
  Induct >- simp[abi_encode_region_inputs_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[abi_encode_region_inputs_def] >> rpt strip_tac >> gvs[] >> conj_tac
  >- (drule_all abi_encode_region_input_transport >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_encode_region_nonword_supplier:
  ~is_word_type ty /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live next op /\
  (!w. eval_operand op s = SOME w ==>
    venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (lo,hi-lo)) /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty) /\
  is_abi_dynamic ce.ce_struct_fields ty =
    is_dynamic (vyper_to_abi_type (get_tenv cx) ty) ==>
  ?ct rv. source_rep (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    abi_encode_region_input sf ce ty ct rv op next lo hi s /\
    abi_tuple_encode_layout ce [(op,ty)] [ct]
Proof
  strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `val_in_memory tv v (w2n w) s.vs_memory` by metis_tac[] >>
  drule_all abi_encoder_source_footprint_rep >> strip_tac >>
  `val_wf tv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  drule val_footprint_le >> strip_tac >>
  drule_all source_rep_compiler_layout >> strip_tac >>
  qexistsl [`ct`, `rv`] >> simp[] >> conj_tac
  >- (simp[abi_encode_region_input_def] >>
      qexistsl [`w2n w`, `val_footprint tv v`] >> simp[w2n_lt] >> metis_tac[]) >>
  simp[abi_tuple_encode_layout_def] >> metis_tac[]
QED

(* Empty logical sources need not be outside the actual destination window. *)
Theorem abi_encode_region_empty_source_adapter:
  ~is_word_type ty /\ abi_decoder_operand_live next op /\
  type_memory_bytes ce ty < dimword (:256) /\
  eval_operand op s = SOME (n2w sb) /\ sb < dimword (:256) /\
  abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av sb 0 s.vs_memory /\
  lo < sb /\ sb < hi ==>
  abi_encode_region_input sf ce ty at av op next lo hi s /\
  abi_tuple_encode_open_input sf ce ty at av op next 0 0 s
Proof
  strip_tac >>
  `abi_encode_region_input sf ce ty at av op next lo hi s` by
    (simp[abi_encode_region_input_def] >> qexistsl [`sb`, `0`] >>
     simp[venomMemDefsTheory.regions_disjoint_def]) >>
  simp[] >> drule abi_encode_region_input_empty_adapter >> simp[]
QED

Theorem abi_encode_region_empty_target_adapter:
  abi_encode_region_input sf ce ty at av op next lo lo s ==>
  abi_tuple_encode_open_input sf ce ty at av op next 0 0 s
Proof
  metis_tac[abi_encode_region_input_empty_adapter]
QED
