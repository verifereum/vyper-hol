(* Completed array prefixes are protected from both output and actual scratch writes. *)
Theory ctorAbiActualArrayIteration
Ancestors
  ctorAbiActualChildFrame ctorAbiActualMemory ctorAbiActualSites
  abiDecoderArrayPrefix valueEncodingProofs valueEncodingTyping valueEncoding valueEncodingDefs
  abiEncoderRegisteredEffect venomMemDefs venomState list arithmetic pred_set
  ctorAbiActualObservations ctorAbiActualWorld ctorAbiActualNarrow abiDecoderContract
  abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderDynamic abiDecoderReentry
  abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup abiDecoderVarSequence
  compileEnv emitHelper exprLoweringProps venomInst rich_list abiEncoder

Theorem ctor_actual_child_preserves_elements:
  abi_encoder_registered_effect (ctor_actual_sites fn child) [(c,k)] s t /\
  child SUBSET ids /\ ctor_actual_scratch fn ids D N t /\
  elems_in_memory vs p tv s.vs_memory /\ all_have_type tv vs /\
  D <= p /\ p + LENGTH vs * type_memory_size tv <= D+N /\
  regions_disjoint (p,LENGTH vs * type_memory_size tv) (c,k) ==>
  elems_in_memory vs p tv t.vs_memory
Proof
  strip_tac >>
  `elems_val_wf vs tv` by (drule_all (cj 4 value_has_type_val_wf) >> simp[]) >>
  `mem_bytes_at p (LENGTH vs * type_memory_size tv) t.vs_memory =
   mem_bytes_at p (LENGTH vs * type_memory_size tv) s.vs_memory` by
    (irule ctor_actual_registered_window >>
     qexistsl [`ctor_actual_sites fn child`, `[(c,k)]`] >>
     asm_simp_tac bool_ss [EVERY_DEF, pairTheory.pair_case_thm] >>
     reverse conj_tac
     >- (gvs[venomMemDefsTheory.regions_disjoint_def] >> rpt strip_tac >> decide_tac) >>
     rpt strip_tac >> irule (cj 2 ctor_actual_sites_scratch_contained) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule (cj 3 val_in_memory_mem_agree_proof) >> simp[] >>
  qexists `s.vs_memory` >> simp[]
QED

Theorem ctor_actual_child_append_element:
  abi_encoder_registered_effect (ctor_actual_sites fn child)
    [(p + LENGTH vs * type_memory_size tv,type_memory_size tv)] s t /\
  child SUBSET ids /\ ctor_actual_scratch fn ids D N t /\
  elems_in_memory vs p tv s.vs_memory /\ all_have_type tv vs /\
  D <= p /\ p + LENGTH vs * type_memory_size tv <= D+N /\
  val_in_memory tv v (p + LENGTH vs * type_memory_size tv) t.vs_memory ==>
  elems_in_memory (vs ++ [v]) p tv t.vs_memory
Proof
  strip_tac >>
  `elems_in_memory vs p tv t.vs_memory` by
    (irule ctor_actual_child_preserves_elements >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  simp[elems_in_memory_append, val_in_memory_def]
QED

Theorem ctor_actual_array_setup_opcodes:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) hi di asz msz st = (ops,st') ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `dec_info_needs_offset di` >> Cases_on `hi = Lit 0w` >>
  simp[abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
    compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  strip_tac >> gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem ctor_actual_array_setup_labels:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges DLOAD (Lit 0w) hi src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) s.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w (LENGTH pre)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [] s t
Proof
  strip_tac >>
  `abi_decode_source DLOAD s = s.vs_data_section` by simp[abi_decode_source_def] >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
      (ListV (pre ++ av::post)))) (abi_decode_source DLOAD s) =
      enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))` by
    (pure_asm_rewrite_tac [] >> REFL_TAC) >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  drule_all (SIMP_RULE bool_ss [arithmeticTheory.ADD_CLAUSES]
    (Q.INST [`B` |-> `0:num`] abi_decoder_dynarray_setup)) >> strip_tac >>
  drule ctor_actual_array_setup_opcodes >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  qexists `t` >> asm_simp_tac bool_ss [] >>
  irule ctor_actual_empty_effect >> gvs[abi_decoder_address_frame_def]
QED
