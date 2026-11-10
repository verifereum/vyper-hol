Theory abiDecodePtrComplexOutcomeAbort
Ancestors
  abiDecodePtrComplexAbort abiDecodePtrComplexHeader abiDecodePtrFlatRun abiDecodePtrFlatLayout
  abiDecodePtrRejectCode abiDecoderVarSequence
  emitHelper freshWrites fragExec exprSimAccounts venomInst instIdxIndep
  abiDecodePtrBytesMember abiDecodePtrMemberInterface
  abiDecoderMemberInfos abiDecoderCoherence abiDecoderAppend
  fragGasSeqPtr fragGasPathPtr abiDecodePtrOpcode
  exprSimAbiDecodeResourceMutual stmtReasonLitFragMemory
  exprLoweringProps emitHelperProps compileEnv supportedTypes
  abiEncoder contractABI words list arithmetic rich_list venomExecSemantics venomState

Theorem abi_decode_scalar_head_capacity[local]:
  !tys. EVERY supported_scalar_type tys ==>
    FOLDR (\(_,asz:num,_:num) acc. asz+acc) 0
      (abi_decoder_member_infos sf ce tys) = 32 * LENGTH tys /\
    32 * LENGTH tys <= SUM (MAP (type_memory_bytes ce) tys)
Proof
  Induct >> simp[abi_decoder_member_infos_def] >> rpt strip_tac >>
  rename1 `supported_scalar_type ty` >>
  `abi_embedded_static_size ce.ce_struct_fields ty = 32 /\
   32 <= type_memory_bytes ce ty` by
    (Cases_on `ty` >> fs[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[supported_word_type_def, supported_string_type_def,
       abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def,
       type_memory_bytes_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     fs[supported_word_type_def, supported_string_type_def,
       abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def,
       type_memory_bytes_def]) >> gvs[abi_decoder_member_infos_def]
QED

Theorem abi_decode_complex_observed_abort:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap (Lit 0w) 0w hi sa G tn s /\
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  cap = SUM (MAP (type_memory_bytes ce) tys) /\
  compile_abi_decode_to_buf (Var dst) (Lit 0w) MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) sa = ((),sb) /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?H tf n j. gas_path_ptr D 0 ctx func PG G tn s n H tf
    (Abort a (u with vs_inst_idx := j))
Proof
  strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_member_live_resources >> strip_tac >>
  `w2n b+h < dimword(:256) /\ w2n d+cap < dimword(:256)` by
    fs[abi_decode_member_live_def] >>
  drule_all abi_decode_scalar_head_capacity >> strip_tac >>
  `cap < dimword(:256)` by decide_tac >>
  `hi <> Lit 0w` by fs[abi_decode_member_live_def] >>
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
  `abi_decode_flat_layout (abi_decoder_member_infos ce.ce_struct_fields ce tys)
     0 0 0w (32*LENGTH tys) cap` by
    (irule abi_decode_supported_flat_layout >> simp[]) >>
  drule_all abi_decode_flat_compile_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa middle ++ emitted_insts middle sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  Cases_on `?t. run_inst_seq (emitted_insts sa middle) s = OK t`
  >- (pop_assum strip_assume_tac >> suspend "suffix") >>
  `run_inst_seq (emitted_insts sa middle) s = Abort a u` by
    metis_tac[run_inst_seq_append_err] >>
  drule_all abi_decode_complex_header_abort >> metis_tac[]
QED

Resume abi_decode_complex_observed_abort[suffix]:
  `32 * LENGTH tys <= cap` by metis_tac[] >>
  `32 * LENGTH tys < dimword(:256) /\ h < dimword(:256)` by decide_tac >>
  `eval_operand (Lit (n2w (FOLDR (\(_,asz:num,_:num) acc. asz+acc) 0
     (abi_decoder_member_infos ce.ce_struct_fields ce tys)))) s =
       SOME (n2w (32*LENGTH tys))` by simp[eval_operand_def] >>
  drule_all abi_decode_add_range_success_bounds >>
  simp[w2n_n2w] >> strip_tac >>
  `abi_decode_flat_layout (abi_decoder_member_infos ce.ce_struct_fields ce tys)
      0 0 0w h cap` by
    (irule abi_decode_supported_flat_layout >> simp[]) >>
  `run_inst_seq (emitted_insts middle sb) t = Abort a u` by
    metis_tac[run_inst_seq_append] >>
  drule_all abi_decode_complex_header_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts middle sb)
      (t with vs_inst_idx := LENGTH middle.cs_current_insts) =
        Abort a (u with vs_inst_idx := LENGTH middle.cs_current_insts)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  qpat_x_assum `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sa _ _ _` kall_tac >>
  qpat_x_assum `abi_decode_flat_layout _ _ _ _ (32*LENGTH tys) _` kall_tac >>
  `?K tk. inst_seq_ptr D 0 ctx func PG H tf (emitted_insts middle sb)
      (t with vs_inst_idx := LENGTH middle.cs_current_insts) K tk` by
    (irule abi_decode_flat_abort >> simp[] >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`abi_decoder_member_infos ce.ce_struct_fields ce tys`, `0`, `0`] >> simp[]
     >- (irule abi_decode_supported_flat_layout >> simp[])) >>
  suspend "path"
QED

Resume abi_decode_complex_observed_abort[path]:
  drule abi_decode_member_live_compiler >> strip_tac >>
  `sb.cs_current_bb = middle.cs_current_bb` by fs[same_blocks_def] >>
  `sb.cs_current_insts = middle.cs_current_insts ++ emitted_insts middle sb` by
    fs[inst_extends_def] >>
  `?bb. lookup_block (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_current_bb
       func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts middle sb)
      (DROP (LENGTH middle.cs_current_insts) bb.bb_instructions)` by
    (drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts middle sb)` by suspend "opcodes" >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_abort_gas_path_ptr >>
  disch_then (qspecl_then [`u with vs_inst_idx := LENGTH middle.cs_current_insts`, `a`, `bb`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  fs[] >> metis_tac[gas_path_ptr_then]
QED

Resume abi_decode_complex_observed_abort[opcodes]:
  drule_all abi_decode_flat_reentry_code >> strip_tac >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i _ ==> abi_decoder_reentry_opcode _` drule >>
  simp[abi_decoder_reentry_opcode_def] >> strip_tac >> gvs[]
QED

Finalise abi_decode_complex_observed_abort
