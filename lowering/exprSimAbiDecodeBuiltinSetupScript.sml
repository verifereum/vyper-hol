(* Finite setup facts for the arbitrary-input builtin decoder. *)
Theory exprSimAbiDecodeBuiltinSetup
Ancestors
  abiBuiltinSetupReach abiBuiltinAllocation abiBuiltinDecodeSetup
  abiBuiltinLengthGuard abiBuiltinBoundTests abiBuiltinDecodeHeader
  abiDecoderBytestringOutcome abiDecoderWordOutcome exprSimAbiDecodeSetupExec
  abiDecoderSequenceReach abiDecoderFiniteControl abiDecoderSiteEffect fragExec instIdxIndep
  exprSimAbiDecodeSiteProvenance
  actualDecoderSites exprLoweringProps emitHelper emitHelperProps compileEnv rich_list
  venomExecSemantics venomState venomInst finite_map pred_set words arithmetic list

Theorem abi_decode_builtin_setup_progress:
  abi_builtin_allocation_frame next site outsz s t ==>
  abi_decode_alloc_progress {site} s t
Proof
  simp_tac bool_ss [abi_builtin_allocation_frame_def] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, abi_decode_alloc_progress_def,
      FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem abi_decode_builtin_header_opcodes[local]:
  abi_builtin_decode_header data lo hi st = (ops,ready) ==>
  EVERY (\i. abi_bytes_opcode i.inst_opcode) (emitted_insts st ready)
Proof
  Cases_on `lo = hi` >>
  simp[abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def,
    abi_builtin_bound_test_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_bytes_opcode_def, abi_word_opcode_def]
QED

Theorem abi_decode_builtin_alloc_static[local]:
  compile_alloc_buffer outsz st = (buf,ready) /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  (!i. MEM i (emitted_insts st ready) ==> MEM i (fn_insts func)) ==>
  decode_site_resources ctx func t /\ decode_static_frame s t
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def, eval_operand_def,
       AllCaseEqs()] >>
  strip_tac >>
  `decode_site_resources ctx func t` by
    (irule decode_site_resources_exec_alloca >>
     goal_assum (drule_at Any) >> fs[mk_inst_def, MEM] >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[] >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  simp[exec_alloca_def, mk_inst_def, update_var_def, decode_static_frame_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), venom_state_component_equality]
QED

Theorem abi_decode_builtin_setup_static:
  abi_builtin_decode_setup data lo hi outsz st = (ops,ready) /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  (!i. MEM i (emitted_insts st ready) /\ i.inst_opcode = ALLOCA ==>
    MEM i (fn_insts func)) ==>
  decode_site_resources ctx func t /\ decode_static_frame s t
Proof
  strip_tac >> drule_all abi_decode_setup_run_split >> strip_tac >>
  drule abi_decode_builtin_header_opcodes >> strip_tac >>
  drule_all abi_bytes_sequence_static >> strip_tac >>
  `decode_site_resources ctx func u` by
    (irule decode_site_resources_fields >> qexists `s` >>
     fs[venom_state_component_equality]) >>
  `decode_static_frame s u` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `!i. MEM i (emitted_insts header ready) ==> MEM i (fn_insts func)` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule abi_builtin_decode_header_shape >> strip_tac >>
     `emitted_insts st ready =
       emitted_insts st header ++ emitted_insts header ready` by
       (irule emitted_insts_append >> simp[] >>
        metis_tac[prefix_drop_equiv, emitted_insts_def]) >>
     rpt strip_tac >> first_x_assum irule >>
     gvs[mk_inst_def]) >>
  drule_all abi_decode_builtin_alloc_static >> strip_tac >>
  metis_tac[decode_static_frame_trans]
QED

Theorem abi_decode_builtin_setup_effect:
  abi_builtin_allocation_frame next site outsz s t /\
  decode_site_resources ctx func t /\ decode_static_frame s t ==>
  decode_site_effect ctx func next EMPTY s t
Proof
  strip_tac >> drule abi_decode_builtin_setup_progress >>
  simp_tac bool_ss [abi_decode_alloc_progress_def, abi_builtin_allocation_frame_def,
    decode_site_effect_def, decode_memory_frame_def] >>
  rpt strip_tac >> gvs[abi_builtin_allocation_frame_def]
QED

Theorem abi_decode_builtin_setup_site_reach:
  abi_builtin_decode_setup data lo hi outsz st = (ops,ready) /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  lo <= cnt /\ cnt <= hi /\ hi < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st lo hi) = NONE /\
      d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st lo hi) = SOME (d,outsz)) /\
  outsz < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ decode_site_resources ctx func s /\
  fn_inst_ids_distinct func /\ fn_has_code st ready fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. Dreach ctx fn s t /\
    eval_operand (FST ops) t = SOME (n2w d) /\
    eval_operand (FST (SND ops)) t = SOME (p + 32w) /\
    eval_operand (SND (SND ops)) t = SOME (n2w cnt) /\
    fresh_vars_wrt limit_st t /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st lo hi) outsz s t /\
    decode_site_effect ctx func st.cs_next_var EMPTY s t /\
    abi_decode_alloc_progress {abi_builtin_decode_output_site st lo hi} s t /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_decode_setup_execute >> strip_tac >>
  `!i. MEM i (emitted_insts st ready) /\ i.inst_opcode = ALLOCA ==>
    MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     qpat_x_assum `fn_has_code st ready fn` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     fs[emitted_insts_def, MEM_APPEND] >> metis_tac[MEM_DROP_IMP]) >>
  drule_all abi_decode_builtin_setup_static >> strip_tac >>
  drule_all abi_decode_builtin_setup_effect >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
  rename1 `decoder_straight_prefix fn s actual` >>
  qexists `actual` >>
  `abi_decode_alloc_progress {abi_builtin_decode_output_site st lo hi} s t` by
    metis_tac[abi_decode_builtin_setup_progress] >>
  simp[Dreach_straight_prefix, fresh_vars_wrt_def, eval_op_inst_idx,
    abi_builtin_allocation_frame_def, abi_decode_alloc_progress_def] >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def,
      abi_decode_alloc_progress_def] >> metis_tac[]
QED
