(* Uniform source values: select witnesses before varying memory. *)
Theory abiEncoderUniformValueSource
Ancestors
  abiEncoderUniformArrayConstructor
  abiEncoderUniformStaticSource abiEncoderUniformSourceMembers
  abiEncoderUniformSourceEncoding abiEncoderUniformAggregateConstructors
  abiEncoderSourceProducer abiEncoderSourcePrimitive abiEncoderSourceTransport
  abiEncoderSourceAggregate abiEncoderSourceWindow abiEncoderProps abiCallerTupleLayout
  vyperABI contractABI abiDecodeRanges abiEncoderInput list rich_list
  valueEncodingProofs vyperValueOperation abiEncoderOpenInput vyperValue
  valueEncoding vyperTyping


Theorem abi_encoder_uniform_value_source:
  (!env ty ei. abi_enc_plan env ty ei ==> ?ct.
    (!tv. evaluate_type env ty = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type env ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type env ty)) /\
    (!tv v av sb mem0.
      evaluate_type env ty = SOME tv /\ value_has_type tv v /\
      vyper_to_abi env ty v = SOME av /\ val_in_memory tv v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
        !mem. val_in_memory tv v sb mem ==>
          abi_encoder_open_input ei ct rv sb (type_memory_size tv) mem)) /\
  (!env ts infos. abi_enc_plans env ts infos ==> ?cts.
    LENGTH ts = LENGTH infos /\ LENGTH ts = LENGTH cts /\
    (!i ei abi_sz mem_sz dyn.
      i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      ((!tv. evaluate_type env (EL i ts) = SOME tv ==>
        is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type env (EL i ts)) /\
        abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type env (EL i ts))) /\
       (!tv v av sb mem0.
        evaluate_type env (EL i ts) = SOME tv /\ value_has_type tv v /\
        vyper_to_abi env (EL i ts) v = SOME av /\ val_in_memory tv v sb mem0 ==>
        ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type env (EL i ts)) av /\
          !mem. val_in_memory tv v sb mem ==>
            abi_encoder_open_input ei (EL i cts) rv sb (type_memory_size tv) mem)) /\
      abi_sz = abi_member_head_size (EL i cts) /\
      dyn = is_dynamic (EL i cts) /\
      ?tv. evaluate_type env (EL i ts) = SOME tv /\ mem_sz = type_memory_size tv))
Proof
  ho_match_mp_tac abi_enc_plan_ind >> rpt conj_tac
  >- suspend "prim"
  >- suspend "bytes"
  >- suspend "string"
  >- suspend "static"
  >- suspend "dynarray"
  >- suspend "tuple"
  >- suspend "sarray"
  >- suspend "struct"
  >- (rpt strip_tac >> qexists_tac `[]` >> simp[])
  >> suspend "cons"
QED

Resume abi_encoder_uniform_value_source[bytes]:
  gen_tac >> gen_tac >> qexists_tac `Bytes NONE` >>
  simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
  rpt strip_tac >> qexists_tac `av` >> simp[] >> rpt strip_tac >>
  irule abi_encoder_open_bytes_source >> simp[] >>
  qexistsl_tac [`env`, `v`] >> simp[]
QED

Resume abi_encoder_uniform_value_source[string]:
  gen_tac >> gen_tac >> qexists_tac `String` >>
  simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
  rpt strip_tac >> qexists_tac `av` >> simp[] >> rpt strip_tac >>
  irule abi_encoder_open_string_source >> simp[] >>
  qexistsl_tac [`env`, `v`] >> simp[]
QED

Resume abi_encoder_uniform_value_source[static]:
  rpt strip_tac >> drule_all abi_encoder_uniform_static_value_source >>
  disch_then (qx_choose_then `ct` strip_assume_tac) >>
  drule_all abi_caller_static_memory >> strip_tac >>
  qexists_tac `ct` >> simp[abi_member_head_size_def] >> metis_tac[]
QED

Resume abi_encoder_uniform_value_source[prim]:
  rpt strip_tac >> Cases_on `?tv. evaluate_type env ty = SOME tv`
  >- (pop_assum (qx_choose_then `tv` assume_tac) >>
      drule_all abi_encoder_word_source_shape >> strip_tac >>
      drule_all abi_encoder_uniform_static_value_source >>
      disch_then (qx_choose_then `ct` strip_assume_tac) >>
      drule_all abi_caller_static_memory >> strip_tac >>
      qexists_tac `ct` >> simp[abi_member_head_size_def] >>
      metis_tac[abi_encoder_copy32_word]) >>
  qexists_tac `vyper_to_abi_type env ty` >> simp[] >> metis_tac[]
QED

Resume abi_encoder_uniform_value_source[cons]:
  rpt strip_tac >> qexists_tac `ct::cts` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `i`
  >- (gvs[] >> conj_tac
      >- (rpt strip_tac >> first_assum irule >> simp[] >>
          qexists_tac `mem0` >> simp[]) >>
      simp[abi_member_head_size_def]) >>
  gvs[] >> qpat_x_assum `!i ei abi_sz mem_sz dyn. _`
    (qspec_then `n` mp_tac) >> simp[] >>
  metis_tac[]
QED

Resume abi_encoder_uniform_value_source[dynarray]:
  rpt strip_tac >> qexists_tac `Array NONE ct` >>
  drule_all abi_encoder_uniform_dynarray >>
  simp[abi_member_head_size_def] >> metis_tac[]
QED
Resume abi_encoder_uniform_value_source[tuple]:
  rpt strip_tac >> qexists_tac `Tuple cts` >>
  irule abi_encoder_uniform_tuple >> simp[] >> metis_tac[]
QED
Resume abi_encoder_uniform_value_source[sarray]:
  rpt strip_tac >> irule abi_encoder_uniform_sarray >> simp[] >>
  qexists_tac `cts` >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _` (qspec_then `i` mp_tac) >>
  simp[] >> metis_tac[]
QED
Resume abi_encoder_uniform_value_source[struct]:
  rpt strip_tac >> qexists_tac `Tuple cts` >>
  irule abi_encoder_uniform_struct >> gvs[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _` (qspec_then `i` mp_tac) >>
  simp[] >> metis_tac[]
QED

Finalise abi_encoder_uniform_value_source
