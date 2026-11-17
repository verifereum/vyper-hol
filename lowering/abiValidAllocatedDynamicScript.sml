(* Dynamic constructor adapter for the allocation-backed success contract. *)
Theory abiValidAllocatedDynamic
Ancestors
  abiValidAllocatedCompiledLoop abiValidAllocatedArrayInit
  abiValidAllocatedArrayTraversal abiValidAllocatedBulkReach
  abiValidAllocatedAggregate abiValidAllocatedArraySource
  abiDecoderRecursiveArray abiDecoderRecursiveLoopLayout abiDecoderLoopSetup
  abiDecoderArraySetupCode abiDecoderArrayInit abiDecoderCoherence abiValidAllocatedMembers
  abiValidAllocatedContract abiDecoderContract abiDecoderReentry
  abiDecoderLoop abiValidAllocatedArrayPrefix
  abiMalformedRecursiveInterface abiMalformedSiteFrame abiMalformedTraversal
  exprLoweringProps exprLowering compileEnv loweringStateRelDefs fragExec
  valueEncoding valueEncodingProps vyperABI vyperValue contractABI
  abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderDynarrayPrefix
  abiDecoderArrayHeader abiEncoder context exprSimAlloc emitHelperProps emitHelper rich_list venomInst
  vyperTypeABI valueEncodingTyping vyperTyping
  finite_map pred_set words list arithmetic

Theorem abi_valid_allocated_dynamic_array:
  abi_decoder_coherent ce env sf ty tv /\
  abi_valid_allocated_type_contract ce env sf ty tv ==>
  abi_valid_allocated_type_contract ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  rewrite_tac[abi_valid_allocated_type_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (qhdtm_assum `abi_valid_allocated_entry`
        (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
      `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
      `compile_abi_decode_to_buf dst src MLOAD base_op hi
        (DecDynArray (type_to_abi_dec_info sf ce ty)
          (abi_embedded_static_size ce.ce_struct_fields ty)
          (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn)
        st = ((),en)` by fs[type_to_abi_dec_info_def] >>
      drule_all abi_decoder_recursive_array_code >> strip_tac >>
      `LENGTH xs = L` by
        ( `mem_bytes_at B L s.vs_memory = xs` by
            fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
               Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
          metis_tac[LENGTH_mem_bytes_at]) >>
      `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) (DROP p xs) /\
       abi_to_vyper env (ArrayT ty (Dynamic maxn))
         (dec (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)) = SOME v` by
        fs[vyper_to_abi_type_def] >>
      drule_all abi_valid_allocated_array_source_view >> strip_tac >>
      drule abi_decoder_coherent_array_capacity >> strip_tac >>
      `32+LENGTH vs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
       (!k. k < LENGTH vs ==> d+32+k*type_memory_size tv+type_memory_size tv <=
         d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)))` by
        (irule abi_valid_allocated_array_output_bounds >>
         qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` (irule_at Any) >> simp[]) >>
      `type_memory_bytes ce ty = type_memory_size tv /\
       abi_embedded_static_size ce.ce_struct_fields ty =
         abi_member_head_size (vyper_to_abi_type env ty)` by
        (qpat_assum `abi_decoder_coherent ce env sf ty tv`
           (mp_tac o MATCH_MP abi_decoder_coherent_header) >>
         simp[abi_decoder_header_def]) >>
      drule_all abi_decode_array_loop_init_shape >> strip_tac >>
      `MEM (mk_inst (loop_st.cs_next_id-2) ALLOCA [Lit 32w]
         [STRING #"%" (toString (loop_st.cs_next_var-1))]) (fn_insts func)` by
        (drule abi_decode_array_loop_init_trace >> strip_tac >>
         drule abi_decode_index_init_trace >> strip_tac >>
         drule abi_decode_index_init_shape >> strip_tac >>
         `fn_has_code header_st allocation_st func` by
           (`cs_extends header_st loop_st` by
              (irule cs_extends_same_block >> metis_tac[inst_extends_def, IS_PREFIX_APPEND]) >>
            `cs_extends st header_st` by
              (drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
               drule_all abi_decode_array_header_shape >> strip_tac >>
               irule cs_extends_same_block >>
               metis_tac[inst_extends_trans, inst_extends_def, IS_PREFIX_APPEND]) >>
            `fn_has_code header_st loop_st func` by metis_tac[fn_has_code_split] >>
            `inst_extends header_st allocation_st` by metis_tac[abi_decode_alloc_buffer_inst_extends] >>
            `inst_extends allocation_st loop_st` by metis_tac[inst_extends_emit_void] >>
            `allocation_st.cs_blocks = header_st.cs_blocks /\
             allocation_st.cs_current_bb = header_st.cs_current_bb` by
              (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
               simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
                 comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
               strip_tac >> gvs[]) >>
            `cs_extends header_st allocation_st /\ cs_extends allocation_st loop_st` by
              (conj_tac >> irule cs_extends_same_block >>
               metis_tac[inst_extends_def, IS_PREFIX_APPEND]) >>
            metis_tac[fn_has_code_split]) >>
         drule_all buffer_alloc_code >> strip_tac >> gvs[]) >>
      `loop_st.cs_next_id-2 IN abi_malformed_scratch_sites st en func` by
        (simp[abi_malformed_scratch_sites_def] >>
         goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
      PairCases_on `setup` >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
      `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
       LENGTH vs = abi_head_word (DROP p xs)` by decide_tac >>
      `p+32+LENGTH vs*abi_embedded_static_size ce.ce_struct_fields ty <= L` by
        (qpat_assum `abi_embedded_static_size _ _ = _`
           (fn th => pure_rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
      drule_all abi_valid_allocated_array_init_loop_entry >>
      disch_then (qspec_then `tv` strip_assume_tac) >>
      qpat_x_assum `abi_head_word _ = LENGTH vs` kall_tac >>
      `LENGTH vs < dimword (:256)` by decide_tac >>
      `EVERY (val_wf tv) vs` by
        (`evaluate_type env ty = SOME tv` by
           (qpat_assum `abi_decoder_coherent ce env sf ty tv`
             (mp_tac o MATCH_MP abi_decoder_coherent_header) >> simp[abi_decoder_header_def]) >>
         `value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))` by
           (irule (cj 1 abi_to_vyper_well_typed) >>
            qpat_assum `v = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
            qpat_assum `abi_to_vyper env (ArrayT _ _) _ = SOME (ArrayV _)` (irule_at Any) >>
            qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _`
              (mp_tac o MATCH_MP abi_decoder_coherent_header) >>
            simp[abi_decoder_header_def]) >>
         qpat_x_assum `value_has_type (ArrayTV _ _) _` mp_tac >>
         pure_rewrite_tac[value_has_type_def, all_have_type_EVERY] >>
         strip_tac >> fs[EVERY_MEM] >>
         metis_tac[cj 1 value_has_type_val_wf]) >>
      `EVERY (abi_decoder_operand_live loop_st.cs_next_var) [setup0;src;base_op]` by
        (`abi_decoder_operand_live st.cs_next_var src /\
          abi_decoder_operand_live st.cs_next_var base_op` by
           fs[abi_malformed_entry_def, Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
         simp[] >> reverse conj_tac
         >- (conj_tac >> irule abi_decoder_operand_live_mono >>
             qexists_tac `st.cs_next_var` >> simp[]) >>
         drule abi_decode_array_loop_init_trace >> strip_tac >>
         drule abi_decode_index_init_shape >> strip_tac >>
         qpat_x_assum `(setup0,setup1) = _` mp_tac >>
         simp[pairTheory.PAIR_EQ] >> strip_tac >>
         simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
           fresh_var_def, not_fresh_at_def]) >>
      `frag_outcome ctx func u en
        (\t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
          abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
            (abi_malformed_scratch_sites st en func) dstid d
            (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s t /\
          fresh_vars_wrt ceiling t) (K F)` by
        (irule abi_valid_allocated_compiled_loop >>
         qhdtm_assum `abi_valid_allocated_array_inv` (irule_at Any) >>
         qexistsl_tac [`ty`, `sf`, `env`, `setup1`, `ce`] >>
         simp[mk_inst_def] >> conj_tac
         >- (rpt strip_tac >>
             qpat_x_assum `!k. k < LENGTH vs ==> _`
               (qspec_then `k` mp_tac) >> simp[] >> decide_tac) >>
         metis_tac[]) >>
      qhdtm_x_assum `frag_outcome`
        (qx_choose_then `t` strip_assume_tac o SIMP_RULE bool_ss [frag_outcome_def, combinTheory.K_THM]) >>
      `abi_decode_sim ctx func u t` by simp[abi_decode_sim_def] >>
      `abi_decode_sim ctx func s t` by metis_tac[abi_decode_sim_trans] >>
      qexists_tac `t` >>
      fs[abi_valid_allocated_post_def, abi_valid_allocated_effect_def]) >>
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) F maxn` by
    fs[type_to_abi_dec_info_def] >>
  metis_tac[abi_valid_allocated_bulk_reach]
QED
