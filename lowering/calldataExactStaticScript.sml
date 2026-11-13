Theory calldataExactStatic
Ancestors
  calldataSourceSize calldataSourceDecisions calldataSourceWord
  calldataReconstruction abiEncoderInputFrame vyperCalldata vyperCalldataProps
  valueEncodingTyping valueEncodingDefs valueEncoding abiDecoderCoherence
  memoryValueAbiTuple exprSimAggregateLoops
  exprLowering compileEnv vyperTyping calldataWordProps entryDecodeProps abiEncoder words list arithmetic

Theorem calldata_exact_static_word[local]:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp /\
  mem_bytes_at d 32 mem = mem_bytes_at pos 32 cd ==>
  ?x. cd_word_value tv (cd_word cd pos) = SOME x /\
    value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d mem
Proof
  strip_tac >>
  `mem_word_at d mem = cd_word cd pos` by
    gvs[mem_word_at_def, mem_bytes_at_def, cd_word_def, cd_bytes_def] >>
  `cd_word_value tv (cd_word cd pos) <> NONE` by
    (drule_all calldata_coherent_word_accepts >> simp[abi_clamp_ok_def]) >>
  Cases_on `cd_word_value tv (cd_word cd pos)` >> gvs[] >>
  drule_all calldata_coherent_word_value >> strip_tac >>
  `value_has_type tv x /\ typed_val_to_w256 tv x = cd_word cd pos` by metis_tac[] >>
  simp[] >> conj_tac
  >- (irule (cj 1 value_has_type_val_wf) >> simp[]) >>
  irule calldata_word_representation >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def] >>
  metis_tac[]
QED

Theorem calldata_exact_static_elems:
  !n i d. ~tv_abi_dynamic tv /\
  (!j. j < n ==> ?x.
    cd_decode T cd tv (pos + (i+j)*type_memory_size tv) = SOME x /\
    value_has_type tv x /\
    val_in_memory tv x (d+j*type_memory_size tv) mem) ==>
  ?vs. cd_decode_elems T cd tv pos i n = SOME vs /\
    LENGTH vs = n /\ EVERY (value_has_type tv) vs /\
    elems_in_memory vs d tv mem
Proof
  Induct >> simp[cd_decode_def, val_in_memory_def] >> rpt strip_tac >>
  `?x. cd_decode T cd tv (pos+i*type_memory_size tv) = SOME x /\
    value_has_type tv x /\ val_in_memory tv x d mem` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `?vs. cd_decode_elems T cd tv pos (i+1) n = SOME vs /\
    LENGTH vs = n /\ EVERY (value_has_type tv) vs /\
    elems_in_memory vs (d+type_memory_size tv) tv mem` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC j` mp_tac) >>
     asm_simp_tac std_ss [ADD1, ADD_ASSOC, LEFT_ADD_DISTRIB,
       RIGHT_ADD_DISTRIB] >> metis_tac[ADD_COMM, ADD_ASSOC]) >>
  qexists_tac `x::vs` >>
  simp[cd_decode_def, cd_member_ptr_def, cd_at_def,
       tv_abi_size_def, tv_abi_static_memory_size, val_in_memory_def]
QED

Theorem calldata_exact_static_list[local]:
  !tvs ofs d.
  EVERY (\tv. ~tv_abi_dynamic tv /\
    !pos d. mem_bytes_at d (type_memory_size tv) mem =
      mem_bytes_at pos (type_memory_size tv) cd ==>
    ?x. cd_decode T cd tv pos = SOME x /\ value_has_type tv x /\
      val_in_memory tv x d mem) tvs /\
  mem_bytes_at d (type_memory_size_list tvs) mem =
    mem_bytes_at (pos+ofs) (type_memory_size_list tvs) cd ==>
  ?vs. cd_decode_list T cd tvs pos ofs = SOME vs /\
    LIST_REL value_has_type tvs vs /\ tuple_in_memory vs tvs d mem
Proof
  Induct >> simp[cd_decode_def, val_in_memory_def] >> rpt strip_tac >>
  `mem_bytes_at d (type_memory_size h) mem =
    mem_bytes_at (pos+ofs) (type_memory_size h) cd` by
    (drule abi_encoder_window_slice >>
     disch_then (qspecl_then [`0`,`type_memory_size h`] mp_tac) >>
     simp[type_memory_size_def]) >>
  `?x. cd_decode T cd h (pos+ofs) = SOME x /\ value_has_type h x /\
    val_in_memory h x d mem` by metis_tac[] >>
  `mem_bytes_at (d+type_memory_size h) (type_memory_size_list tvs) mem =
    mem_bytes_at (pos+(ofs+type_memory_size h)) (type_memory_size_list tvs) cd` by
    (qpat_x_assum `mem_bytes_at d (type_memory_size h) mem = _` kall_tac >>
     drule abi_encoder_window_slice >>
     disch_then (qspecl_then [`type_memory_size h`,`type_memory_size_list tvs`] mp_tac) >>
     simp_tac std_ss [type_memory_size_def, ADD_ASSOC] >> metis_tac[ADD_COMM]) >>
  `?vs. cd_decode_list T cd tvs pos (ofs+type_memory_size h) = SOME vs /\
    LIST_REL value_has_type tvs vs /\
    tuple_in_memory vs tvs (d+type_memory_size h) mem` by metis_tac[] >>
  qexists_tac `x::vs` >>
  simp[cd_decode_def, cd_member_ptr_def, cd_at_def,
       tv_abi_size_def, tv_abi_static_memory_size, val_in_memory_def] >>
  `cd_decode T cd h (ofs+pos) = SOME x` by metis_tac[ADD_COMM] >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem calldata_exact_static_slice:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  ~tv_abi_dynamic tv /\ ~tv_needs_clamp tv ==>
  !cd pos d mem.
  mem_bytes_at d (type_memory_size tv) mem =
    mem_bytes_at pos (type_memory_size tv) cd ==>
  ?x. cd_decode T cd tv pos = SOME x /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d mem
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- suspend "scalar"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume calldata_exact_static_slice[scalar]:
  rpt strip_tac >>
  `is_word_type (BaseT bt) /\
   type_to_abi_dec_info (FEMPTY : string |-> (string # type # num) list) ce (BaseT bt) = DecPrimWord NoClamp /\
   type_memory_size (BaseTV bt) = 32 /\
   (!nat cd pos. cd_decode nat cd (BaseTV bt) pos =
     cd_word_value (BaseTV bt) (cd_word cd pos))` by
    (Cases_on `bt` >>
     gvs[tv_needs_clamp_def, abi_decoder_scalar_valid_def,
         is_word_type_def, type_to_abi_dec_info_def, type_to_abi_clamp_def,
         type_memory_size_def, cd_decode_def] >>
     rename1 `BytesT b` >> Cases_on `b` >>
     gvs[tv_needs_clamp_def, abi_decoder_scalar_valid_def,
         is_word_type_def, type_to_abi_dec_info_def, type_to_abi_clamp_def,
         type_memory_size_def, cd_decode_def]) >>
  simp[] >> irule calldata_exact_static_word >>
  conj_tac >- gvs[] >> qexistsl_tac [`ce`,`env`,`FEMPTY`,`BaseT bt`] >>
  simp[abi_decoder_coherent_base_iff]
QED
Resume calldata_exact_static_slice[flag]:
  rpt strip_tac >>
  `n = 256` by gvs[tv_needs_clamp_def] >> gvs[] >>
  simp[cd_decode_def] >> irule calldata_exact_static_word >>
  conj_tac >- gvs[type_memory_size_def] >>
  qexistsl_tac [`ce`,`env`,`FEMPTY`,`FlagT nsid`] >>
  simp[is_word_type_def, type_to_abi_dec_info_def,
       abi_decoder_coherent_flag_iff]
QED
Resume calldata_exact_static_slice[array]:
  rpt strip_tac >> Cases_on `bound` >>
  gvs[tv_abi_dynamic_def, tv_needs_clamp_def] >>
  `?vs. cd_decode_elems T cd tv pos 0 n = SOME vs /\
    LENGTH vs = n /\ EVERY (value_has_type tv) vs /\
    elems_in_memory vs d tv mem` by
    (irule calldata_exact_static_elems >> simp[] >> rpt strip_tac >>
     `mem_bytes_at (d+j*type_memory_size tv) (type_memory_size tv) mem =
      mem_bytes_at (pos+j*type_memory_size tv) (type_memory_size tv) cd` by
       (drule abi_encoder_window_slice >>
        disch_then (qspecl_then [`j*type_memory_size tv`,`type_memory_size tv`] mp_tac) >>
        simp[type_memory_size_def] >> impl_tac
        >- (irule LESS_EQ_TRANS >> qexists_tac `(j+1)*type_memory_size tv` >>
            simp[RIGHT_ADD_DISTRIB] >> irule LESS_MONO_MULT >> decide_tac) >>
        metis_tac[]) >>
     first_x_assum drule >> simp[] >> metis_tac[]) >>
  qexists_tac `ArrayV (make_array_value tv (Fixed n) vs)` >>
  simp[cd_decode_def] >> irule calldata_fixed_values_typed_memory >> simp[]
QED
Resume calldata_exact_static_slice[tuple]:
  rpt strip_tac >>
  `EVERY (\tv. ~tv_abi_dynamic tv /\
    !pos d. mem_bytes_at d (type_memory_size tv) mem =
      mem_bytes_at pos (type_memory_size tv) cd ==>
    ?x. cd_decode T cd tv pos = SOME x /\ value_has_type tv x /\
      val_in_memory tv x d mem) tvs` by
    (gvs[tv_abi_dynamic_def, tv_needs_clamp_def,
         tv_abi_dynamic_list_exists, tv_needs_clamp_list_exists,
         EVERY_EL, LIST_REL_EL_EQN, EXISTS_MEM, MEM_EL] >> metis_tac[]) >>
  `?vs. cd_decode_list T cd tvs pos 0 = SOME vs /\
    LIST_REL value_has_type tvs vs /\ tuple_in_memory vs tvs d mem` by
    (irule calldata_exact_static_list >> simp[] >>
     gvs[type_memory_size_def]) >>
  qexists_tac `ArrayV (TupleV vs)` >> simp[cd_decode_def] >>
  irule calldata_tuple_values_typed_memory >> simp[]
QED
Resume calldata_exact_static_slice[struct]:
  rpt strip_tac >>
  `LENGTH args = LENGTH tvs` by gvs[LIST_REL_EL_EQN] >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by simp[MAP_ZIP] >>
  `EVERY (\tv. ~tv_abi_dynamic tv /\
    !pos d. mem_bytes_at d (type_memory_size tv) mem =
      mem_bytes_at pos (type_memory_size tv) cd ==>
    ?x. cd_decode T cd tv pos = SOME x /\ value_has_type tv x /\
      val_in_memory tv x d mem) tvs` by
    (gvs[tv_abi_dynamic_def, tv_needs_clamp_def,
         tv_abi_dynamic_fields_map, tv_needs_clamp_fields_map,
         tv_abi_dynamic_list_exists, tv_needs_clamp_list_exists,
         EVERY_EL, LIST_REL_EL_EQN, EXISTS_MEM, MEM_EL] >> metis_tac[]) >>
  `?vs. cd_decode_list T cd tvs pos 0 = SOME vs /\
    LIST_REL value_has_type tvs vs /\ tuple_in_memory vs tvs d mem` by
    (irule calldata_exact_static_list >> simp[] >>
     gvs[type_memory_size_def, type_memory_size_fields_list]) >>
  qexists_tac `StructV (ZIP (MAP FST args,vs))` >> simp[cd_decode_def, MAP_ZIP] >>
  irule calldata_struct_values_typed_memory >> conj_tac
  >- (gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP]) >>
  irule struct_tuple_memory_post >> simp[]
QED
Finalise calldata_exact_static_slice
