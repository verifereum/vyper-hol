(* Canonical data inputs for the actual member setup, without compiler context. *)
Theory ctorDeployMemoryRunPtrPrefixMemberInputs
Ancestors
  abiDecoderMemberBody abiDecoderMembers abiDecoderCoherence abiDecoderContract
  abiDecoderDynamic abiDecoderOffset abiDecoderReentry
  abiEncoder contractABI compileEnv valueEncoding venomState words list

Theorem prefix_member_canonical_inputs:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) ==>
  abi_decode_load DLOAD
    (n2w (sb + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) : bytes32)
    initial =
    (n2w (abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys)) : bytes32) /\
  sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys) < dimword (:256)
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- gvs[dec_info_needs_offset_def] >>
  qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
    (mp_then Any mp_tac abi_decoder_members_child_facts) >>
  disch_then drule >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  mp_tac (Q.INST [`pre` |-> `MAP (vyper_to_abi_type env) pretys`,
    `aty` |-> `vyper_to_abi_type env ty`, `post` |-> `MAP (vyper_to_abi_type env) tys`,
    `pvs` |-> `preavs`, `opc` |-> `DLOAD`, `s` |-> `initial:venom_state`]
    abi_decoder_canonical_member_inputs) >>
  (impl_tac >- gvs[MAP_APPEND, abi_decode_source_def, Excl "enc_def"]) >>
  strip_tac >>
  simp[abi_decoder_needs_offset_iff] >> strip_tac >>
  qpat_x_assum `LENGTH pretys = LENGTH preavs` (assume_tac o SYM) >>
  fs[MAP_APPEND, Excl "enc_def"]
QED

Theorem prefix_member_source_offset_agreement:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  type_to_abi_dec_info sf ce ty <> DecComplex T [] ==>
  (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty) then
     abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
       (preavs ++ av::avs) (LENGTH pretys)
   else SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) =
  abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
    (preavs ++ av::avs) (LENGTH pretys)
Proof
  strip_tac >>
  qpat_assum `abi_decoder_members ce env sf pretys pretvs preavs prevs`
    (mp_then Any mp_tac abi_decoder_members_child_facts) >>
  disch_then drule >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  mp_tac (Q.INST [`pre` |-> `MAP (vyper_to_abi_type env) pretys`,
    `aty` |-> `vyper_to_abi_type env ty`, `post` |-> `MAP (vyper_to_abi_type env) tys`,
    `pvs` |-> `preavs`, `opc` |-> `DLOAD`, `s` |-> `initial:venom_state`]
    abi_decoder_canonical_member_inputs) >>
  (impl_tac >- gvs[MAP_APPEND, abi_decode_source_def, Excl "enc_def"]) >>
  strip_tac >>
  qpat_x_assum `LENGTH pretys = LENGTH preavs` (assume_tac o SYM) >>
  Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` >>
  fs[abi_decoder_needs_offset_iff, MAP_APPEND, Excl "enc_def"] >>
  `~is_dynamic (vyper_to_abi_type env ty)` by metis_tac[] >> simp[]
QED
