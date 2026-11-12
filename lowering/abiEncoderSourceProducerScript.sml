Theory abiEncoderSourceProducer
Ancestors
  abiEncoderSourceAggregate abiEncoderSourceWindow abiEncoderProps
  abiEncoderSourceConstructors
  vyperABI contractABI abiDecodeRanges abiEncoderSourcePrimitive abiEncoderInput list rich_list valueEncodingProofs vyperValueOperation
  abiEncoderSourceTransport abiEncoderOpenInput vyperValue valueEncoding vyperTyping

Theorem abi_encoder_uniform_source:
  (!env ty ei. abi_enc_plan env ty ei ==> ?ct. source_rep env ty ei ct) /\
  (!env ts infos. abi_enc_plans env ts infos ==> ?cts. source_reps env ts infos cts)
Proof
  ho_match_mp_tac abi_enc_plan_ind >> rpt conj_tac
  >- suspend "prim"
  >- suspend "bytes"
  >- suspend "string"
  >- (rpt strip_tac >> irule source_rep_static_copy >> simp[])
  >- suspend "dynarray"
  >- suspend "tuple"
  >- suspend "sarray"
  >- suspend "struct"
  >- (rpt strip_tac >> qexists_tac `[]` >> simp[source_reps_nil])
  >> suspend "cons"
QED

Resume abi_encoder_uniform_source[bytes]:
  gen_tac >> gen_tac >> qexists_tac `Bytes NONE` >>
  simp[source_rep_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
  rpt strip_tac >> qexists_tac `av` >> simp[] >>
  irule abi_encoder_open_bytes_source >> simp[] >>
  qexistsl_tac [`env`, `v`] >> simp[]
QED

Resume abi_encoder_uniform_source[string]:
  gen_tac >> gen_tac >> qexists_tac `String` >>
  simp[source_rep_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
  rpt strip_tac >> qexists_tac `av` >> simp[] >>
  irule abi_encoder_open_string_source >> simp[] >>
  qexistsl_tac [`env`, `v`] >> simp[]
QED

Resume abi_encoder_uniform_source[cons]:
  rpt strip_tac >> qexists_tac `ct::cts` >>
  irule source_reps_cons >> simp[] >>
  drule_all source_rep_metadata >> simp[abi_member_head_size_def]
QED

Resume abi_encoder_uniform_source[prim]:
  metis_tac[source_rep_primitive]
QED

Resume abi_encoder_uniform_source[dynarray]:
  rpt strip_tac >> qexists_tac `Array NONE ct` >>
  irule source_rep_dynamic_array >> simp[]
QED

Resume abi_encoder_uniform_source[tuple]:
  rpt strip_tac >> qexists_tac `Tuple cts` >>
  irule source_rep_tuple >> simp[]
QED

Resume abi_encoder_uniform_source[struct]:
  rpt strip_tac >> qexists_tac `Tuple cts` >>
  irule source_rep_struct >> simp[]
QED

Resume abi_encoder_uniform_source[sarray]:
  rpt strip_tac >> Cases_on `n = 0`
  >- (gvs[] >> drule source_reps_lengths >> strip_tac >> gvs[] >>
      qexists_tac `Array (SOME 0) (Bytes NONE)` >>
      irule source_rep_fixed_array_zero >> simp[]) >>
  qexists_tac `Tuple cts` >> irule source_rep_fixed_array >> simp[]
QED

Finalise abi_encoder_uniform_source

Theorem abi_encoder_source_window:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?ct rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_open_input ei ct rv sb (type_memory_size tv) mem
Proof
  rpt strip_tac >>
  drule (cj 1 abi_encoder_uniform_source) >> strip_tac >>
  drule_all source_rep_transport >> metis_tac[]
QED

(* Loaded .dat files retain oracle tags but erase upstream axiom dependencies. *)
