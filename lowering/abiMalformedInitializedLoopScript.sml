(* Initializer and traversal packaged without exposing scratch witnesses. *)
Theory abiMalformedInitializedLoop
Ancestors
  abiMalformedOutcomeLoop abiMalformedInitTotal abiMalformedInitResource
  abiMalformedZeroTraversal abiMalformedCompiledZero abiMalformedRecursiveInterface
  abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderArrayInitReentry abiDecoderArrayInit
  abiDecoderDynarrayPrefix abiDecodeRanges
  abiDecoderRecursiveArray abiDecoderLoopCode abiDecoderRecursiveLoopEntry
  abiDecoderLoopEmit abiDecoderRecursiveLoopLayout abiDecoderArraySetupCode
  abiMalformedOutcomeContract abiDecoderContract abiDecoderReentry abiEncoder
  exprSimAlloc exprLoweringProps localPtrsProps emitHelperProps emitHelper
  context fragExec compileEnv venomState venomInst words list rich_list
  finite_map pred_set arithmetic

Theorem abi_malformed_initialized_loop_outcome:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn abi_sz st = ((ip,cnt),loop_st) /\
  compile_abi_decode_dyn_loop dst src MLOAD base_op hi di abi_sz mem_sz ip cnt loop_st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    base_op hi src dst B L xs p d outsz incoming /\
  fresh_vars_wrt ceiling incoming /\ en.cs_next_var <= ceiling.cs_next_var /\
  incoming.vs_current_bb = st.cs_current_bb /\
  incoming.vs_inst_idx = LENGTH st.cs_current_insts /\ ~incoming.vs_halted /\
  maxn < dimword (:256) /\ maxn*abi_sz < dimword (:256) /\ 32 <= outsz /\
  (maxn <> 0 ==>
    abi_sz = abi_member_head_size (vyper_to_abi_type env ty) /\
    dec_info_needs_offset di = is_dynamic (vyper_to_abi_type env ty) /\
    (case di of DecPrimWord clamp =>
      ~is_dynamic (vyper_to_abi_type env ty) /\ abi_sz = 32 | _ => T) /\
    abi_sz < dimword (:256) /\
    (!j. j<maxn ==> d+32+j*mem_sz+childsz <= d+outsz) /\
    (!childsrc childdst child child_end.
      compile_abi_decode_to_buf childdst childsrc MLOAD base_op hi di child = ((),child_end) /\
      fn_has_code child child_end func ==>
      abi_malformed_constructor_outcome env ty di ctx func cenv cx es child child_end
        base_op hi childsrc childdst childsz)) ==>
  frag_outcome ctx func incoming en
    (\u. (?avs. abi_reflected_prefix env ty (DROP (p+32) xs)
                   (abi_head_word (DROP p xs)) avs) /\
      abi_head_word (DROP p xs) <= maxn /\ p+32 <= L /\
      p+32+abi_head_word (DROP p xs)*abi_sz <= L /\
      abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
        (abi_malformed_scratch_sites st en func) dstid incoming u /\
      fresh_vars_wrt ceiling u)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  drule_all abi_decoder_recursive_loop_end >> strip_tac >>
  `cs_extends st loop_st` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code st loop_st func /\ fn_has_code loop_st en func` by
    metis_tac[fn_has_code_split] >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule abi_decode_index_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `fn_has_code header_st allocation_st func` by
    (`cs_extends header_st loop_st` by
       (irule cs_extends_same_block >>
        metis_tac[inst_extends_def, IS_PREFIX_APPEND]) >>
     `cs_extends st header_st` by
       (drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
        drule_all abi_decode_array_header_shape >> strip_tac >>
        irule cs_extends_same_block >>
        metis_tac[inst_extends_trans, inst_extends_def, IS_PREFIX_APPEND]) >>
     `fn_has_code header_st loop_st func` by metis_tac[fn_has_code_split] >>
     `inst_extends header_st allocation_st` by
       metis_tac[abi_decode_alloc_buffer_inst_extends] >>
     `inst_extends allocation_st loop_st` by metis_tac[inst_extends_emit_void] >>
     `allocation_st.cs_blocks = header_st.cs_blocks /\
      allocation_st.cs_current_bb = header_st.cs_current_bb` by
       (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
        simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
     `cs_extends header_st allocation_st /\ cs_extends allocation_st loop_st` by
       (conj_tac >> irule cs_extends_same_block >>
        metis_tac[inst_extends_def, IS_PREFIX_APPEND]) >>
     metis_tac[fn_has_code_split]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `header_st.cs_next_id IN abi_malformed_scratch_sites st en func` by
    (simp[abi_malformed_scratch_sites_def] >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  gvs[] >>
  `loop_st.cs_next_var <= ceiling.cs_next_var` by decide_tac >>
  `maxn * abi_sz < dimword (:256)` by metis_tac[MULT_COMM] >>
  `MEM (mk_inst (loop_st.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (loop_st.cs_next_var-1))]) (fn_insts func) /\
   loop_st.cs_next_id-2 IN abi_malformed_scratch_sites st en func` by simp[] >>
  drule_all abi_malformed_init_fragment >> strip_tac >>
  drule frag_outcome_apply >>
  disch_then (qspecl_then [`incoming`, `func`] mp_tac) >> simp[] >> strip_tac >>
  irule frag_outcome_compose >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >>
  `abi_malformed_entry ctx func cenv cx es loop_st
     (abi_malformed_scratch_sites st en func) dstid live
     base_op hi src dst B L xs p d outsz t` by
    (`local_ptrs_reserved cenv loop_st` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
        fs[abi_malformed_entry_def]) >>
     `EVERY (abi_decoder_operand_live loop_st.cs_next_var) [base_op;hi;src;dst]` by
       (fs[abi_malformed_entry_def, EVERY_DEF] >> rpt conj_tac >>
        irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     `abi_malformed_allocated_window live B L xs incoming /\
      live NOTIN abi_malformed_scratch_sites st en func /\ live <> dstid /\
      abi_malformed_destination func cenv es.scopes dstid d outsz incoming` by
       fs[abi_malformed_entry_def] >>
     drule_all abi_malformed_resource_window >> strip_tac >>
     drule_all abi_malformed_resource_destination >> strip_tac >>
     fs[abi_malformed_entry_def, abi_malformed_resource_post_def, EVERY_DEF]) >>
  `header_st.cs_next_id <> live /\ header_st.cs_next_id <> dstid` by
    (fs[abi_malformed_entry_def] >> metis_tac[]) >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString header_st.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `header_st` >> simp[] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def] >> decide_tac) >>
  `abi_decoder_operand_live loop_st.cs_next_var buf.buf_operand` by
    (qpat_assum `Var _ = buf.buf_operand` (fn th => rewrite_tac[GSYM th]) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          ASCIInumbersTheory.toString_11]) >>
  Cases_on `maxn = 0` >- suspend "zero" >>
  fs[] >>
  drule_at (Pat `compile_abi_decode_dyn_loop _ _ _ _ _ _ _ _ _ _ _ = _`)
    (abi_malformed_outcome_compiled_loop |> SPEC_ALL |>
      Q.INST [`env` |-> `env`, `ty` |-> `ty`,
        `inst` |-> `mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
          [STRING #"%" (toString header_st.cs_next_var)]`,
        `n` |-> `abi_head_word (DROP p xs)`]) >>
  disch_then (drule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[GSYM mk_inst_def] >>
  disch_then (qspecl_then [`ty`, `slot`, `header_st`, `env`, `childsz`, `ceiling`] mp_tac) >>
  fs[mk_inst_def, GSYM abi_member_head_size_def] >>
  impl_tac
  >- (conj_tac >- (fs[] >> metis_tac[MULT_COMM]) >>
      conj_tac >- (Cases_on `di` >> gvs[]) >>
      irule abi_malformed_scratch_sites_nested >> simp[] >> decide_tac) >>
  strip_tac >>
  irule frag_outcome_compose >> goal_assum (drule_at Any) >>
  rpt strip_tac >> irule frag_outcome_refl >> fs[] >>
  conj_tac >- metis_tac[] >>
  irule abi_malformed_resource_trans >> goal_assum (drule_at Any) >>
  irule abi_malformed_resource_weaken >> goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Resume abi_malformed_initialized_loop_outcome[zero]:
  fs[] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule abi_malformed_compiled_zero >>
  disch_then (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_decode_loop_suffix _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_malformed_entry _ _ _ _ _ loop_st _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts func)`)) >>
  simp[mk_inst_def] >>
  disch_then (qspecl_then [`ty`, `env`, `ceiling`] mp_tac) >>
  simp[mk_inst_def] >>
  impl_tac >- gvs[mk_inst_def] >>
  strip_tac >>
  irule frag_outcome_compose >> goal_assum (drule_at Any) >>
  rpt strip_tac >> irule frag_outcome_refl >> fs[] >>
  conj_tac >- metis_tac[] >>
  irule abi_malformed_resource_trans >> goal_assum (drule_at Any) >>
  irule abi_malformed_resource_weaken >> goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Finalise abi_malformed_initialized_loop_outcome
