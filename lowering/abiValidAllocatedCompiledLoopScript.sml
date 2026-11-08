(* Static compiler packaging for the successful finite traversal. *)
Theory abiValidAllocatedCompiledLoop
Ancestors
  abiValidAllocatedArrayTraversal abiDecoderRecursiveArray
  abiDecoderRecursiveLoopLayout abiDecoderArraySetupCode abiDecoderLoopEmit abiDecoderLoopCode
  abiDecoderReentry abiDecoderCode abiDecoderArrayBackedge abiMalformedRecursiveInterface abiValidAllocatedMembers
  abiValidAllocatedContract abiDecoderContract abiDecoderPhi abiDecoderExecution
  exprLoweringProps compileEnv fragExec venomInst venomExecSemantics
  valueEncoding vyperABI contractABI finite_map pred_set words list arithmetic

Theorem abi_valid_allocated_compiled_loop:
  compile_abi_decode_dyn_loop dst src MLOAD base_op hi (type_to_abi_dec_info sf ce ty)
    (abi_member_head_size (vyper_to_abi_type env ty)) (type_memory_size tv)
    ip cnt loop_st = ((),final) /\
  fn_has_code loop_st final func /\ fn_inst_ids_distinct func /\
  start.cs_next_id <= loop_st.cs_next_id /\ final.cs_next_id <= outer_end.cs_next_id /\
  start.cs_next_var <= loop_st.cs_next_var /\ final.cs_next_var <= ceiling.cs_next_var /\
  inst.inst_id < loop_st.cs_next_id /\
  EVERY (abi_decoder_operand_live loop_st.cs_next_var) [ip;src;base_op] /\
  EVERY (val_wf tv) vs /\ LENGTH vs < dimword (:256) /\
  32+LENGTH vs*type_memory_size tv <= outsz /\
  abi_valid_allocated_type_contract ce env sf ty tv /\
  abi_decoder_coherent ce env sf ty tv /\
  LENGTH xs = L /\ LENGTH vs = abi_head_word (DROP p xs) /\ p+32 <= L /\
  p+32+LENGTH vs*abi_member_head_size (vyper_to_abi_type env ty) <= L /\
  vyper_decode_valid_enc_tuple (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
    (DROP (p+32) xs) (DROP (p+32) xs) /\
  abi_to_vyper_list env (REPLICATE (LENGTH vs) ty)
    (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
      (DROP (p+32) xs) (DROP (p+32) xs)) = SOME vs /\
  (!k. k < LENGTH vs ==> d+32+k*type_memory_size tv+type_memory_bytes ce ty <= d+outsz) /\
  abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
    (abi_malformed_scratch_sites start outer_end func) dstid live base_op hi src dst
    B L xs p d outsz ip slot inst q
    (fresh_label_output "dec_dyn_hdr" loop_st.cs_next_label) tv vs origin 0 s ==>
  frag_outcome ctx func s final
    (\u. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d u.vs_memory /\
      abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
        (abi_malformed_scratch_sites start outer_end func) dstid d outsz origin u /\
      fresh_vars_wrt ceiling u) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  rename1 `abi_decode_loop_prefix _ _ _ _ loop_st = (labels,body_st)` >>
  rename1 `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ body_st = (ops,child)` >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ _ child = ((),child_end)` >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  `abi_decode_loop_suffix ip (Var (STRING #"%" (toString body_st.cs_next_var)))
     (FST labels) (SND (SND labels)) child_end = ((),final)` by metis_tac[] >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `FST labels = fresh_label_output "dec_dyn_hdr" loop_st.cs_next_label` by
    (qpat_x_assum `abi_decode_loop_prefix _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_loop_prefix_shape, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >>
  drule_all abi_decoder_to_buf_code >> strip_tac >>
  `child.cs_next_id <= child_end.cs_next_id` by fs[abi_decoder_code_def] >>
  `abi_malformed_scratch_sites child child_end func SUBSET
     abi_malformed_scratch_sites start outer_end func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `inst.inst_id NOTIN abi_malformed_scratch_sites child child_end func` by
    (irule abi_malformed_scratch_sites_older >> decide_tac) >>
  `abi_decoder_operand_live body_st.cs_next_var ip /\
   abi_decoder_operand_live child.cs_next_var ip /\
   ip <> Var (STRING #"%" (toString child_end.cs_next_var))` by
    (fs[] >> rpt conj_tac
     >- (irule abi_decoder_operand_live_mono >> qexists_tac `loop_st.cs_next_var` >> simp[])
     >- (irule abi_decoder_operand_live_mono >> qexists_tac `loop_st.cs_next_var` >> simp[] >> decide_tac) >>
     irule abi_decoder_live_excludes_output >> qexists_tac `loop_st.cs_next_var` >> simp[] >> decide_tac) >>
  irule abi_valid_allocated_array_traversal >>
  qhdtm_assum `abi_valid_allocated_array_inv` (irule_at Any) >>
  goal_assum (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  simp[] >>
  qexistsl_tac [`ty`, `sf`, `child_end.cs_next_var`, `loop_st.cs_next_id+1`,
    `loop_st with <|cs_current_bb := FST labels; cs_current_insts := []|>`,
    `loop_st.cs_next_var`, `env`, `ce`, `child_end.cs_next_id`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qhdtm_x_assum `abi_valid_allocated_type_contract`
        (mp_tac o PURE_REWRITE_RULE [abi_valid_allocated_type_contract_def]) >>
      disch_then drule >> simp[]) >>
  gvs[abi_decode_position_header_insts_def, abi_decode_header_insts_def,
      phi_prefix_length_def, mk_inst_def]

QED
