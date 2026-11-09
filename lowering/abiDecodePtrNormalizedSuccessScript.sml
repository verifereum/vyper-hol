Theory abiDecodePtrNormalizedSuccess
Ancestors
  abiDecodePtrSourceOutcome abiDecodePtrComplexHeader abiDecodePtrFlatValue
  abiDecodePtrCallerMetadata abiDecodePtrMemberInterface abiDecodePtrFlatLayout
  bodyPtrBopHashSuffix fragExec fragGasSeqPtr fragGasPathPtr
  abiDecodePtrOpcode exprSimAbiDecodeResourceMutual stmtReasonLitFragMemory
  abiDecoderReentry abiDecoderCoherence abiDecoderAppend exprLoweringProps
  abiDecodePtrMemberFrame abiDecoderMemberInfos abiValidMembers emitHelperProps exprSimAccounts abiValidBytesUnwrap
  supportedTypes vyperTypeABI vyperABI abiDecodeRanges contractABI
  words list arithmetic compileEnv venomState venomExecSemantics instIdxIndep

Theorem abi_decode_normalized_success:
  abi_decode_member_live ret ctx func cenv cx es src b (LENGTH bs) dst d cap (Lit 0w) 0w hi sa G tn s /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  cap = SUM (MAP (type_memory_bytes ce) tys) /\
  evaluate_type_builtin cx (AbiDecode F) (TupleT tys) arg_tys [BytesV bs] = INL (ArrayV (TupleV vs)) /\
  LIST_REL value_has_type tvs vs /\ LIST_REL val_wf tvs vs /\
  mem_bytes_at (w2n b) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  compile_abi_decode_to_buf (Var dst) (Lit 0w) MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?u H tf. run_inst_seq (emitted_insts sa sb) s = OK u /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tf
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    abi_decode_member_live ret ctx func cenv cx es src b (LENGTH bs) dst d cap
      (Lit 0w) 0w hi sb H tf (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (!mem'. mem_agree_outside tf.t_mem u.vs_memory mem' ==>
      tuple_in_memory vs tvs (w2n d) mem')
Proof
  strip_tac >>
  drule abi_decode_member_live_resources >> strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_member_live_separation >> strip_tac >>
  rename1 `lookup_var dst s = SOME outword` >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       tuple_in_memory vs tvs (w2n outword) u.vs_memory /\ inst_extends sa sb` by
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
       (Q.INST [`B` |-> `w2n (b:256 word)`, `z` |-> `0`, `d` |-> `w2n (outword:256 word)`]
         abi_decode_physical_source_run) >>
     disch_then (qspecl_then [`vs`, `tvs`, `s`] mp_tac) >>
     simp_tac bool_ss [ADD_CLAUSES, n2w_w2n] >>
     disch_then (qspecl_then [`outword`, `cx`, `bs`, `b`] mp_tac) >>
     disch_then (qspec_then `arg_tys` mp_tac) >>
     impl_tac >- suspend "resources" >> metis_tac[]) >>
  `LIST_REL (abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields) tys tvs` by
    fs[abi_decoder_coherent_tuple_iff] >>
  `cap < dimword(:256)` by decide_tac >>
  `32 * LENGTH tys <= LENGTH bs` by
    (qpat_assum `evaluate_type_builtin _ _ _ _ _ = _`
       (assume_tac o REWRITE_RULE [abi_source_decode_wrapping_iff]) >>
     drule abi_valid_tuple_source_values >> strip_tac >>
     `SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type (get_tenv cx)) tys)) =
        32 * LENGTH tys` by suspend "head_size" >> decide_tac) >>
  `abi_decode_flat_layout (abi_decoder_member_infos ce.ce_struct_fields ce tys)
     0 0 0w (LENGTH bs) cap` by
    (irule abi_decode_supported_flat_layout >> simp[]) >>
  drule_all abi_decode_complex_bounded_split >> strip_tac >>
  rename1 `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ middle = ((),sb)` >>
  `cs_extends sa middle /\ cs_extends middle sb` by
    (conj_tac
     >- (drule emit_op_extends_next_var >> strip_tac >>
         `cs_extends sm middle` by
           metis_tac[cs_appends_def, cs_appends_abi_range_check] >>
         metis_tac[cs_extends_trans]) >>
     metis_tac[cs_appends_def, cj 2 cs_appends_abi_decode_mutual]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  drule_all abi_decode_flat_compile_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa middle ++ emitted_insts middle sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?t. run_inst_seq (emitted_insts sa middle) s = OK t /\
       run_inst_seq (emitted_insts middle sb) t = OK u` by
    metis_tac[bop_run_inst_seq_append_ok] >>
  drule_all abi_decode_complex_header_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `EVERY (\tv. type_memory_size tv < dimword(:256)) tvs` by
    (irule abi_decode_coherent_member_machine_bounds >>
     goal_assum (drule_at Any) >> simp[]) >>
  `run_inst_seq (emitted_insts middle sb)
     (t with vs_inst_idx := LENGTH middle.cs_current_insts) =
       OK (u with vs_inst_idx := LENGTH middle.cs_current_insts)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `tuple_in_memory vs tvs (w2n outword + 0)
      (u with vs_inst_idx := LENGTH middle.cs_current_insts).vs_memory` by simp[] >>
  qpat_x_assum `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sa _ _ _` kall_tac >>
  `?K tk. inst_seq_ptr D 0 ctx func PG H tf (emitted_insts middle sb)
      (t with vs_inst_idx := LENGTH middle.cs_current_insts) K tk /\
    abi_decode_member_live ret ctx func cenv cx es src b (LENGTH bs) dst outword cap
      (Lit 0w) 0w hi sb K tk (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    abi_decode_member_frame middle H tf
      (t with vs_inst_idx := LENGTH middle.cs_current_insts) K tk
      (u with vs_inst_idx := LENGTH sb.cs_current_insts)
      (w2n outword+0) (SUM (MAP (SND o SND) (abi_decoder_member_infos ce.ce_struct_fields ce tys))) /\
    (!mem'. mem_agree_outside tk.t_mem u.vs_memory mem' ==>
      tuple_in_memory vs tvs (w2n outword+0) mem')` by
    (irule (SRULE [] (Q.INST
       [`u` |-> `u with vs_inst_idx := LENGTH middle.cs_current_insts`]
       abi_decode_flat_success_robust)) >>
     simp[] >> conj_tac
     >- (qexists_tac `middle` >> simp[]) >>
     conj_tac >- (qexists_tac `get_tenv cx` >> simp[]) >>
     qexists_tac `0` >> simp[] >>
     irule abi_decode_supported_flat_layout >> simp[]) >>
  `?ex. hi <> Label ex` by
    (Cases_on `hi = Label ""`
     >- (qexists_tac `"x"` >> simp[]) >>
     qexists_tac `""` >> simp[]) >>
  `decode_framed ex (compile_abi_decode_complex_elems (Var dst) (Lit 0w) MLOAD
     (Var src) hi (abi_decoder_member_infos ce.ce_struct_fields ce tys) 0 0) (\u. T)` by
    (irule (cj 2 decode_framed_mutual) >> simp[]) >>
  `middle.cs_blocks = sb.cs_blocks` by fs[same_blocks_def] >>
  drule_all decode_framed_emitted_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts middle sb)` by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts middle sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `?bb. lookup_block middle.cs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts middle sb)
       (DROP (LENGTH middle.cs_current_insts) bb.bb_instructions)` by
    (qpat_assum `fn_has_code middle sb func` mp_tac >>
     drule fn_has_code_code >>
     fs[same_blocks_def, inst_extends_def] >> metis_tac[]) >>
  qpat_assum `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ middle _ _
      (_ with vs_inst_idx := LENGTH middle.cs_current_insts)`
    (mp_then Any strip_assume_tac abi_decode_member_live_compiler) >>
  `lookup_block (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_current_bb
      func.fn_blocks = SOME bb` by (simp[] >> metis_tac[]) >>
  `isPREFIX (emitted_insts middle sb)
      (DROP (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_inst_idx
        bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_ptr >>
  `LENGTH middle.cs_current_insts + LENGTH (emitted_insts middle sb) =
     LENGTH sb.cs_current_insts` by
    (qpat_assum `inst_extends middle sb` mp_tac >>
     simp_tac bool_ss [inst_extends_def] >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[]) >>
  simp[] >> disch_tac >>
  qexistsl_tac [`K'`, `tk`] >>
  reverse conj_tac >- (conj_tac >- metis_tac[] >> fs[] >> metis_tac[]) >>
  drule_all gas_path_ptr_then >> simp[] >> gvs[]
QED

Resume abi_decode_normalized_success[resources]:
  markerLib.RESUME_TAC >>
  `LENGTH bs < dimword(:256)` by decide_tac >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    GSYM not_fresh_at_def, eval_operand_def, abi_decode_ptr_window_def] >>
  fs[abi_decode_ptr_window_def] >>
  Cases_on `hi` >> fs[abi_decoder_older_vars_def, GSYM not_fresh_at_def] >>
  qexists_tac `LENGTH bs` >> simp[]
QED

Resume abi_decode_normalized_success[head_size]:
  markerLib.RESUME_TAC >>
  `!xs. EVERY supported_scalar_type xs ==>
    SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type (get_tenv cx)) xs)) =
      32 * LENGTH xs` suffices_by metis_tac[] >>
  Induct >> simp[] >> rpt strip_tac >>
  rename1 `supported_scalar_type ty` >>
  `abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty) = 32` by
    (Cases_on `ty` >> fs[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[supported_word_type_def, supported_string_type_def,
       abi_member_head_size_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def,
       static_length_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     fs[supported_word_type_def, supported_string_type_def,
       abi_member_head_size_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def,
       static_length_def]) >> simp[]
QED

Finalise abi_decode_normalized_success
