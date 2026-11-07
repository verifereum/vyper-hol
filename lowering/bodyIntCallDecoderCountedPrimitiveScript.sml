(* Counted primitive decoder bodies and finite loops. *)
Theory bodyIntCallDecoderCountedPrimitive
Ancestors
  bodyIntCallDecoderCountedControl abiDecoderPrimitiveLoopFinite
  abiDecoderPrimitiveLoopReach abiDecoderPrimitiveLoopContext
  abiDecoderPrimitiveLoopInvariant abiDecoderPrimitiveLoopFrames
  abiDecoderArrayIteration abiDecoderArrayInvariant abiDecoderPrimitiveLoopFragment
  abiDecoderLoop abiDecoderReentry abiDecoderExecution abiDecoderContract abiDecoderFrame
  fragGasSeq fragGasPath fragExec exprLoweringProps emitHelperProps compileEnv
  venomState venomInst instIdxIndep words list rich_list arithmetic entrySinkExtraction

Theorem intcall_same_block_seq_path:
  fn_has_code st st' fn /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~s.vs_halted /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  ?n. gas_path ctx fn s n (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, emitted_insts_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[emitted_insts_def, LENGTH_DROP] >>
  `LENGTH st.cs_current_insts <= LENGTH st'.cs_current_insts` by
    metis_tac[IS_PREFIX_LENGTH] >>
  `LENGTH st.cs_current_insts +
    (LENGTH st'.cs_current_insts - LENGTH st.cs_current_insts) =
    LENGTH st'.cs_current_insts` by decide_tac >> simp[] >> metis_tac[]
QED

Theorem intcall_decoder_primitive_loop_body_path:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc base_op hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp (B+sb) d slot fp /\
  abi_decoder_loop_inputs first ip src dst base_op B sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d slot
    first limit_st fp initial st0.cs_current_bb j s /\ j < LENGTH vs ==>
  ?u n. abi_decoder_primitive_body_end opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d
      first limit_st fp initial st1 iv j u /\ gas_path ctx fn s n (OK u)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_inv_def]) >>
  drule_all abi_decoder_loop_inputs_eval >> strip_tac >>
  mp_tac (Q.INST [`next` |-> `st0.cs_next_var`] abi_decoder_loop_inputs_live) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_compiled_def]) >>
  drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_code _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_code_def]) >>
  qpat_assum `abi_decoder_primitive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_data_def]) >>
  `opc = MLOAD ==> B+sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= d \/
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= B+sb` by metis_tac[] >>
  `mload (w2n (n2w slot:bytes32)) s = n2w j` by simp[w2n_n2w] >>
  `fresh_vars_wrt limit_st s` by fs[abi_decoder_loop_rel_def] >>
  drule_all abi_decoder_primitive_array_iteration >> strip_tac >>
  `s.vs_inst_idx = LENGTH st0.cs_current_insts` by simp[] >>
  drule_all intcall_same_block_seq_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path ctx fn s n (OK u)` >>
  `abi_decoder_loop_rel first limit_st fp s actual` by
    (irule abi_decoder_primitive_body_rel >> simp[] >>
     conj_tac >- (qexists_tac `st0.cs_next_var` >> simp[]) >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >>
     `d + (32*j+32) = d+32+j*32` by decide_tac >> asm_rewrite_tac[]) >>
  `abi_decoder_loop_rel first limit_st fp s u` by
    fs[Abbr `u`, abi_decoder_loop_rel_def, fresh_vars_wrt_def,
       abi_decode_footprint_frame_def, eval_op_inst_idx] >>
  `abi_decoder_loop_rel first limit_st fp initial u` by metis_tac[abi_decoder_loop_rel_trans] >>
  qexistsl_tac [`u`, `n`] >>
  simp[abi_decoder_primitive_body_end_def, Abbr `u`, eval_op_inst_idx] >>
  drule_all run_inst_seq_preserves_entry_control >> gvs[]
QED

Theorem intcall_decoder_primitive_loop_header_reach_path:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc base_op hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp (B+sb) d slot fp /\
  abi_decoder_loop_inputs first ip src dst base_op B sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d slot
    first limit_st fp initial hdr j s ==>
  ?h. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d slot
    first limit_st fp initial (if j < LENGTH vs then st0.cs_current_bb else exit_lbl) j h /\
    gas_path ctx fn s 0 (OK h)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_primitive_loop_code _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_code_def]) >>
  qpat_assum `abi_decoder_primitive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_data_def]) >>
  qpat_assum `abi_decoder_loop_inputs _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_loop_inputs_def]) >>
  drule_all intcall_decoder_primitive_loop_header_path >> simp[]
QED

Theorem intcall_decoder_primitive_loop_suffix_path:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc base_op hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp (B+sb) d slot fp /\
  abi_decoder_loop_inputs first ip src dst base_op B sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d slot
    first limit_st fp initial hdr j s /\ j <= LENGTH vs ==>
  ?t n. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d slot
    first limit_st fp initial exit_lbl (LENGTH vs) t /\ gas_path ctx fn s n (OK t)
Proof
  qid_spec_tac `s` >> completeInduct_on `LENGTH vs - j` >> rpt strip_tac >>
  Cases_on `j = LENGTH vs`
  >- (drule_all intcall_decoder_primitive_loop_header_reach_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      qexistsl_tac [`h`, `0`] >> gvs[]) >>
  `j < LENGTH vs` by decide_tac >>
  drule_all intcall_decoder_primitive_loop_header_reach_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d slot
    first limit_st fp initial st0.cs_current_bb j h` by
    (qpat_x_assum `abi_decoder_primitive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ (if _ then _ else _) _ _`
       mp_tac >> simp[]) >>
  drule_all intcall_decoder_primitive_loop_body_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all intcall_decoder_primitive_loop_backedge_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx fn u 0 (OK back)` >>
  first_x_assum (qspec_then `LENGTH vs - SUC j` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`vs`, `SUC j`] mp_tac) >>
  simp[] >> disch_then (qspec_then `back` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`t`, `n + n'`] >> simp[] >>
  metis_tac[gas_path_then, ADD_CLAUSES]
QED
