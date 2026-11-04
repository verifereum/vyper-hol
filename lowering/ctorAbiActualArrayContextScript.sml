(* Post-setup baselines for finite actual-site constructor array loops. *)
Theory ctorAbiActualArrayContext
Ancestors
  ctorAbiActualArrayEntry ctorAbiActualArrayFinite ctorAbiActualArrayInvariant
  ctorAbiActualArrayLayout abiDecoderRecursiveLoopContext abiDecoderTypedContract
  abiDecoderReentry abiDecoderContract ctorAbiActualSites abiEncoderRegisteredEffect
  ctorAbiActualAlloc ctorAbiActualFrame allocaFrontierBound
  abiDecoderIndexInit valueEncoding valueEncodingProps vyperABI vyperValue contractABI
  ASCIInumbers pred_set
  compileEnv venomInst venomState venomMemDefs venomExecSemantics words list arithmetic

Theorem ctor_actual_array_observation_compose:
  ctor_actual_array_observation ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial 0 0 prepared /\ earlier <= next /\
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot prepared prefix cursor final ==>
  ctor_actual_array_observation ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor final
Proof
  strip_tac >> irule ctor_actual_array_observation_rebase >>
  qexistsl [`next`, `prepared`] >>
  fs[ctor_actual_array_observation_def]
QED

Theorem ctor_actual_array_setup_ranges:
  ctor_actual_array_observation ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial 0 0 prepared /\
  abi_decoder_operand_live earlier src /\ abi_decoder_operand_live earlier dst /\
  abi_decoder_operand_live earlier hi /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + len < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + len <= h /\ h < dimword (:256)) /\
  0 < outsz /\ D <= d /\ d + outsz <= D+N /\ unit_alloca_budget ctx < dimword (:256) /\
  slot_id IN ctor_actual_sites func ids ==>
  abi_decoder_ranges DLOAD hi src dst sb len d outsz slot 32 prepared /\
  slot < dimword (:256) /\ venomMemDefs$regions_disjoint (slot,32) (d,outsz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src prepared = SOME (n2w sb)` by
    (irule ctor_actual_array_observation_operand >>
     goal_assum (drule_at (Pat `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `eval_operand dst prepared = SOME (n2w d)` by
    (irule ctor_actual_array_observation_operand >>
     goal_assum (drule_at (Pat `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `hi = Lit 0w \/ ?h. eval_operand hi prepared = SOME (n2w h) /\
    sb + len <= h /\ h < dimword (:256)` by
    (Cases_on `hi = Lit 0w` >- simp[] >>
     qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
     qexists `h` >> simp[] >>
     irule ctor_actual_array_observation_operand >>
     goal_assum (drule_at (Pat `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  qpat_assum `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ctor_actual_array_observation_def]) >>
  `slot < dimword (:256)` by
    (drule_all ctor_actual_index_slot_bound >> simp[]) >>
  drule_all ctor_actual_sites_scratch >> strip_tac >>
  `venomMemDefs$regions_disjoint (d,outsz) (slot,32)` by
    (irule ctor_actual_region_contained >> qexistsl [`D`, `N`] >> simp[]) >>
  `d + outsz < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> strip_tac >>
     metis_tac[LESS_EQ_TRANS, LESS_EQ_LESS_TRANS]) >>
  asm_simp_tac (srw_ss()) [abi_decoder_ranges_def, abi_decode_source_opcode_def] >>
  gvs[venomMemDefsTheory.regions_disjoint_def] >>
  disj2_tac >> qexists `h` >> simp[]
QED

Theorem ctor_actual_array_setup_context:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs)) /\
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
    tv vs slot_id slot initial 0 0 prepared /\
  abi_decode_index_init header_st = (ip,loop_st) /\ earlier <= loop_st.cs_next_var /\
  eval_operand ip prepared = SOME (n2w slot) /\
  abi_decoder_operand_live earlier src /\ abi_decoder_operand_live earlier dst /\
  abi_decoder_operand_live earlier hi /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= h /\
    h < dimword (:256)) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  unit_alloca_budget ctx < dimword (:256) /\ slot_id IN ctor_actual_sites func ids ==>
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
    sb d slot slot 32 loop_st.cs_next_var prepared /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    prepared.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
    tv vs slot_id slot prepared 0 0 prepared /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `0 < type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[Once type_memory_bytes_def] >>
  drule_all ctor_actual_array_setup_ranges >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var ip` by
    (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac) >>
  `abi_decoder_operand_live loop_st.cs_next_var src /\
   abi_decoder_operand_live loop_st.cs_next_var dst /\
   abi_decoder_operand_live loop_st.cs_next_var hi` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
    tv vs slot_id slot prepared 0 0 prepared` by
    (irule ctor_actual_array_observation_self >>
     goal_assum (drule_at Any)) >>
  fs[ctor_actual_array_observation_def, abi_decoder_recursive_loop_data_def,
     Excl "enc_def"]
QED
