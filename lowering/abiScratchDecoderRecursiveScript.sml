Theory abiScratchDecoderRecursive
Ancestors
  abiScratchDecoderContract abiDecoderValidFixed abiDecoderValidContract abiDecoderFixedInputs
  abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiValidMembers abiValidAggregateHeads abiCanonicalHeadSize compileEnv valueEncoding vyperABI
  vyperValue contractABI venomState words list rich_list abiScratchDecoderTuple
  abiDecoderFixedMemory abiDecoderMemberInfos abiDecoderEffect abiDecoderReentry fragExec
  valueEncodingTyping abiDecoderStruct pair abiStaticDynarrayLayout valueEncodingProps
  vyperTyping abiScratchEncoderContract abiDecoderOffsetHead abiDecoderReadableTypes
  abiScratchDecoderArray abiDecoderLoop abiEncoder venomExecSemantics

(* ===== Inputs ===== *)

(* Fixed arrays use the actual repeated-type member view of source-valid bytes. *)

Theorem abi_scratch_decoder_fixed_array_inputs:
  abi_scratch_decoder_input ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
    bs v st src dst opc hi sb d first last b cap initial ==>
  ?vs. v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\ LENGTH vs = n /\
    abi_decoder_members ce env sf (REPLICATE n ty) (REPLICATE n tv)
      (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) bs bs) vs /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty)) bs bs /\
    type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) /\
    abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))) first last b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))`
    by simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  `vyper_decode_valid_enc (Array (SOME n) (vyper_to_abi_type env ty)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ bs` mp_tac >> simp_tac bool_ss [Once vyper_to_abi_type_def]) >>
  drule abi_decoder_valid_fixed_view >> strip_tac >>
  gvs[Once vyper_to_abi_type_def, map_replicate,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qexists_tac `vs` >> asm_simp_tac bool_ss []
QED

(* ===== Scratch Decoder Fixed ===== *)

(* Actual-source fixed arrays execute the shared member decoder and recover sparse values. *)

Theorem abi_scratch_decoder_fixed_array:
  abi_scratch_decoder ce env sf ty tv /\
  (0 < n /\ is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_scratch_decoder ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_fixed_array_inputs >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  (`LIST_REL (abi_scratch_decoder ce env sf) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)`
    by simp[LIST_REL_REPLICATE_same] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  mp_tac (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
    (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `tys` |-> `REPLICATE (LENGTH vs) ty`,
      `tvs` |-> `REPLICATE (LENGTH vs) tv`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
      abi_scratch_decoder_complex_execute)) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [EVERY_MEM, MEM_REPLICATE,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
    Cases_on `vs` >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]) >> strip_tac >>
  rename1 `tuple_in_memory vs (REPLICATE (LENGTH vs) tv) d actual.vs_memory` >>
  `val_in_memory (ArrayTV tv (Fixed (LENGTH vs)))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d actual.vs_memory`
    by (irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED

(* ===== Inputs ===== *)

(* Positional struct metadata and ranges over actual noncanonical source bytes. *)

Theorem abi_scratch_decoder_struct_inputs:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  abi_scratch_decoder_input ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    bs v st src dst opc hi sb d first last b cap initial ==>
  ?cfields fields.
    FLOOKUP sf (nsid_to_string nsid) = SOME cfields /\
    MAP (FST o SND) cfields = MAP SND args /\
    v = StructV fields /\
    value_has_type (StructTV (ZIP (MAP FST args,tvs))) (StructV fields) /\
    abi_decoder_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs
      (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs)
      (MAP SND fields) /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) bs bs /\
    type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args)) /\
    abi_scratch_decoder_ranges opc hi src dst sb
      (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (MAP SND args))) first last b cap initial /\
    mem_bytes_at sb
      (LENGTH bs)
      (abi_decode_source opc initial) =
        bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  drule abi_decoder_struct_values >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  drule_all abi_decoder_struct_members_at >> strip_tac >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule type_memory_size_fields_zip >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = SUM (MAP (type_memory_bytes ce) (MAP SND args))` by
    fs[Once type_memory_size_def, Excl "enc_def"] >>
  drule_all abi_decoder_struct_field_types >> strip_tac >>
  `vyper_decode_valid_enc (Tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ bs` mp_tac >>
     asm_simp_tac (srw_ss()) [Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
       Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  qexists_tac `cfields` >>
  gvs[Once vyper_to_abi_type_def, vyper_to_abi_types_MAP,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `vyper_decode_valid_enc (Tuple _) bs` mp_tac >> simp_tac bool_ss [Once vyper_decode_valid_enc_def]
QED

(* ===== Scratch Decoder Struct ===== *)

(* Actual-source struct correctness retains independently descending type maps. *)

Theorem abi_scratch_decoder_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (abi_scratch_decoder ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs ==>
  abi_scratch_decoder ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_struct_inputs >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  (drule abi_decoder_struct_infos >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`]
    abi_scratch_decoder_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `tuple_in_memory (MAP SND fields) tvs d actual.vs_memory` >>
  `fields_in_memory fields (ZIP (MAP FST args,tvs)) d actual.vs_memory` by
    (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [val_in_memory_struct])
QED

(* Structural decoder closure from coherent metadata and actual source validity.
   Empty dynamic fixed-array members use their inline head without a payload read. *)
Theorem abi_scratch_decoder_readable_array:
  (abi_decoder_readable_type env ty ==> abi_scratch_decoder ce env sf ty tv) /\
  abi_decoder_readable_type env (ArrayT ty bound) ==>
  abi_scratch_decoder ce env sf (ArrayT ty bound) (ArrayTV tv bound)
Proof
  simp_tac bool_ss [abi_decoder_readable_array_iff] >> strip_tac >>
  `abi_scratch_decoder ce env sf ty tv` by metis_tac[] >>
  drule abi_decoder_readable_type_head >> disch_then assume_tac >>
  Cases_on `bound` >>
  FIRST [irule abi_scratch_decoder_array, irule abi_scratch_decoder_fixed_array] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_readable_members:
  LIST_REL (\ty tv. abi_decoder_readable_type env ty ==> abi_scratch_decoder ce env sf ty tv)
    tys tvs /\ EVERY (abi_decoder_readable_type env) tys ==>
  LIST_REL (abi_scratch_decoder ce env sf) tys tvs /\
  EVERY (\ty. is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) tys
Proof
  strip_tac >> drule_all abi_decoder_readable_list_relation >> strip_tac >>
  drule abi_decoder_readable_members_head >> simp[]
QED

Theorem abi_scratch_decoder_readable_tuple:
  LIST_REL (\ty tv. abi_decoder_readable_type env ty ==> abi_scratch_decoder ce env sf ty tv)
    tys tvs /\ abi_decoder_readable_type env (TupleT tys) ==>
  abi_scratch_decoder ce env sf (TupleT tys) (TupleTV tvs)
Proof
  simp_tac bool_ss [abi_decoder_readable_tuple_iff] >> strip_tac >>
  drule_all abi_scratch_decoder_readable_members >> strip_tac >>
  irule abi_scratch_decoder_tuple >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_readable_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  LIST_REL (\ty tv. abi_decoder_readable_type (env \\ nsid) ty ==>
    abi_scratch_decoder ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv) (MAP SND args) tvs /\
  abi_decoder_readable_type env (StructT nsid) ==>
  abi_scratch_decoder ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  strip_tac >> drule abi_decoder_readable_struct_iff >> strip_tac >>
  `EVERY (abi_decoder_readable_type (env \\ nsid)) (MAP SND args)` by metis_tac[] >>
  drule_all abi_scratch_decoder_readable_members >> strip_tac >>
  irule abi_scratch_decoder_struct >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_evaluated_array:
  abi_scratch_decoder ce env sf ty tv /\
  evaluate_type env (ArrayT ty bound) = SOME (ArrayTV tv bound) ==>
  abi_scratch_decoder ce env sf (ArrayT ty bound) (ArrayTV tv bound)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_evaluated_array_head >> disch_then assume_tac >>
  Cases_on `bound` >>
  FIRST [irule abi_scratch_decoder_array, irule abi_scratch_decoder_fixed_array] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_coherent_correct:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_scratch_decoder ce env sf ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- simp[abi_scratch_decoder_base]
  >- simp[abi_scratch_decoder_flag]
  >- (rpt strip_tac >>
      rename1 `abi_decoder_header ce env (ArrayT elem bound) (ArrayTV elem_tv bound)` >>
      `evaluate_type env (ArrayT elem bound) = SOME (ArrayTV elem_tv bound)` by
        fs[abi_decoder_header_def] >>
      irule abi_scratch_decoder_evaluated_array >> asm_simp_tac bool_ss [])
  >- (rpt strip_tac >> irule abi_scratch_decoder_tuple >> asm_simp_tac bool_ss []) >>
  rpt strip_tac >> irule abi_scratch_decoder_struct >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_decode:
  compile_abi_decode_to_buf dst src opc hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf ty tv bs v start src dst opc hi sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_scratch_decoder_input_def] >>
  `abi_scratch_decoder ce env sf ty tv` by
    (drule_all abi_scratch_decoder_coherent_correct >> simp[]) >>
  qhdtm_x_assum `abi_scratch_decoder` (mp_tac o PURE_REWRITE_RULE [abi_scratch_decoder_def]) >>
  disch_then (qspecl_then [`dst`, `src`, `opc`, `hi`, `start`, `end_st`, `func`, `ctx`,
    `first`, `last`, `b`, `cap`, `limit_st`, `initial`, `bs`, `v`, `sb`, `d`] mp_tac) >>
  asm_simp_tac bool_ss []
QED
