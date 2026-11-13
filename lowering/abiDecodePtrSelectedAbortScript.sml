Theory abiDecodePtrSelectedAbort
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrSelectedMember abiDecodePtrWord
  abiDecodePtrBytesAbort abiDecodePtrSelectionAbort abiDecodePtrContinuation
  abiEncoder compileEnv context bodyPtrDefs ptrDiscipline
  emitHelperProps exprLoweringProps freshWrites abiDecoderReentryPointer
  abiDecoderAppend abiDecoderReservation abiDecoderTypedCompose
  assignTuplePtrLocalBytesCopy fragExec externalEntryShape
  venomExecSemantics venomState venomInst words arithmetic list finite_map pred_set

(* Decoder-only failure uses precisely the replay ghosts; there is no
   successful-state invariant at an abort endpoint. *)
Theorem abi_decode_member_decode_abort:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei off q k z h cap /\
  compile_abi_decode_to_buf (Var out) v MLOAD (Var src) hi ei sa = ((),sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa out /\
  lookup_var out s = SOME (d+n2w q) /\ ptr_covers G tn out s k /\
  eval_operand v s = SOME w /\ op_prov G v = NONE /\ op_taint tn v = {} /\
  (!x. v = Var x ==> not_fresh_at sa x) /\
  (~dec_info_needs_offset ei ==> w = z+n2w off) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?H tf. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf
Proof
  strip_tac >>
  drule abi_decode_member_live_resources >> strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_member_live_separation >> strip_tac >>
  `q+k <= cap` by fs[abi_decode_member_layout_def] >>
  `w2n (d+n2w q) = w2n d+q` by
    (`w2n d+q < dimword(:256) /\ q < dimword(:256)` by decide_tac >>
     simp[word_add_def, w2n_n2w]) >>
  `w2n (d+n2w q)+k < dimword(:256) /\
   (w2n b+h <= w2n (d+n2w q) \/ w2n (d+n2w q)+k <= w2n b)` by decide_tac >>
  fs[abi_decode_member_layout_def] >> gvs[dec_info_needs_offset_def] >>
  FIRST [
    rename1 `compile_abi_decode_to_buf _ _ _ _ _ (DecPrimWord _) _ = _` >> suspend "word",
    rename1 `compile_abi_decode_to_buf _ _ _ _ _ (DecBytestring _) _ = _` >> suspend "bytes"]
QED

Resume abi_decode_member_decode_abort[word]:
  markerLib.RESUME_TAC >> (
  `w2n (z+n2w off)+32 <= h` by
    (irule LESS_EQ_TRANS >> qexists_tac `w2n z+off+32` >>
     rewrite_tac[word_add_def, w2n_n2w] >>
     `((w2n z+off MOD dimword(:256)) MOD dimword(:256)) <=
       w2n z+off MOD dimword(:256)` by simp[MOD_LESS_EQ] >>
     `off MOD dimword(:256) <= off` by simp[MOD_LESS_EQ] >> decide_tac) >>
  drule (abi_decode_word_abort_ptr |> Q.INST
    [`p` |-> `w2n (z+n2w off : bytes32)`] |> SRULE []) >>
  disch_then (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`z`, `off`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> goal_assum (drule_at Any))
QED

Resume abi_decode_member_decode_abort[bytes]:
  markerLib.RESUME_TAC >>
  drule abi_decode_bytes_member_abort_ptr >>
  disch_then (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`w2n w`, `32+contractABI$ceil32 n`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[w2n_lt]) >> strip_tac >> goal_assum (drule_at Any)
QED

Finalise abi_decode_member_decode_abort

Theorem abi_decode_selected_member_abort:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei off q k z h cap /\
  abi_decode_member_code dst pos src hi ei off q sa sb /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?H tf. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf
Proof
  strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  fs[abi_decode_member_code_def] >>
  drule_all abi_decode_member_phase_shape >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb` by
    suspend "compiler" >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `inst_extends sm sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
   emitted_insts sm sb = emitted_insts sm sn ++ emitted_insts sn sb` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  Cases_on `run_inst_seq (emitted_insts sa sm) s` >>
  FIRST [rename1 `run_inst_seq (emitted_insts sa sm) s = OK _` >> suspend "selection_ok",
    rename1 `run_inst_seq (emitted_insts sa sm) s = Abort _ _` >> suspend "selection_abort",
    (`!t. run_inst_seq (emitted_insts sa sm) s <> OK t` by simp[] >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
     simp[] >> strip_tac >> gvs[])]
QED

Resume abi_decode_selected_member_abort[compiler]:
  conj_tac
  >- (qspec_then `pos` (qspec_then `dec_info_needs_offset ei`
        (qspec_then `off` (qspec_then `MLOAD` mp_tac))) compile_getelemptr_abi_labels >>
      disch_then (qspecl_then [`Var src`, `hi`, `sa`, `\i. T`] mp_tac) >> simp[]) >>
  conj_tac
  >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  metis_tac[cs_extends_abi_decode]
QED

Resume abi_decode_selected_member_abort[selection_abort]:
  drule abi_decode_member_live_resources >> strip_tac >>
  Cases_on `dec_info_needs_offset ei`
  >- suspend "dynamic_abort" >>
  Cases_on `emit_op ADD [pos;Lit (n2w off)] sa` >>
  fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  fs[run_inst_seq_def, step_inst_base_def, eval_operands_def, eval_operand_def,
     mk_inst_def, exec_pure2_def]
QED

Resume abi_decode_selected_member_abort[selection_ok]:
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK raw` >>
  qabbrev_tac `t = raw with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `t.vs_inst_idx = LENGTH sm.cs_current_insts /\
   run_inst_seq (emitted_insts sa sm) s = OK (t with vs_inst_idx := s.vs_inst_idx)` by
    (qspec_then `emitted_insts sa sm` mp_tac run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`s`, `s.vs_inst_idx`] mp_tac) >>
     simp[Abbr `t`, instIdxIndepTheory.exec_result_map_def, venom_state_component_equality]) >>
  drule_all abi_decode_member_selection_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `q+k <= cap` by fs[abi_decode_member_layout_def] >>
  drule_all abi_decode_member_destination_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sm sn) t = OK (r with vs_inst_idx := _)` >>
  `eval_operand v r = SOME w /\ op_prov H v = NONE /\ op_taint tm v = {}` by
    (Cases_on `v` >> fs[abi_decode_member_frame_def, eval_operand_def, lookup_var_def,
      ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def,
      venom_state_component_equality] >> metis_tac[]) >>
  `sm.cs_next_var <= sn.cs_next_var` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  `!x. v = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `run_inst_seq (emitted_insts sm sb) t = Abort a (u with vs_inst_idx := t.vs_inst_idx)` by
    (irule abi_decode_run_continue_abort_normalized >>
     reverse conj_tac >- simp[EVERY_APPEND] >>
     qexistsl_tac [`s`, `emitted_insts sa sm`] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sn sb) r = Abort a (u with vs_inst_idx := r.vs_inst_idx)` by
    (mp_tac (abi_decode_run_continue_abort_normalized |> Q.INST
       [`xs` |-> `emitted_insts sm sn`, `ys` |-> `emitted_insts sn sb`,
        `s` |-> `t`, `t` |-> `r`, `u` |-> `u with vs_inst_idx := t.vs_inst_idx`]) >>
     simp[] >> metis_tac[]) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
    abi_decode_member_decode_abort >>
  disch_then (drule_at (Pat `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `run_inst_seq (emitted_insts sn sb) r = _`)) >>
  disch_then (qspecl_then [`w`, `q`, `off`, `k`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG J tj (emitted_insts sm sb) t H' tf` by
    (irule (cj 2 abi_decode_compile_continue_abort_ptr) >>
     conj_tac >- simp[] >>
     qexistsl_tac [`H`, `a`, `sn`, `r`, `tm`, `u with vs_inst_idx := r.vs_inst_idx`] >>
     fs[inst_extends_def] >> metis_tac[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H' tf` by
    (irule (cj 2 abi_decode_compile_continue_abort_ptr) >>
     conj_tac >- simp[] >>
     qexistsl_tac [`J`, `a`, `sm`, `t`, `tj`, `u with vs_inst_idx := t.vs_inst_idx`] >>
     fs[inst_extends_def] >> metis_tac[]) >>
  qexistsl_tac [`H'`, `tf`] >> simp[]
QED

Resume abi_decode_selected_member_abort[dynamic_abort]:
  `w2n (z+n2w off)+32 <= h` by
    (`w2n z+off+32 <= h` by fs[abi_decode_member_layout_def] >>
     irule LESS_EQ_TRANS >> qexists_tac `w2n z+off+32` >>
     rewrite_tac[word_add_def, w2n_n2w] >>
     `((w2n z+off MOD dimword(:256)) MOD dimword(:256)) <=
       w2n z+off MOD dimword(:256)` by simp[MOD_LESS_EQ] >>
     `off MOD dimword(:256) <= off` by simp[MOD_LESS_EQ] >> decide_tac) >>
  `w2n b+h < dimword(:256)` by
    (drule abi_decode_member_live_separation >> simp[]) >>
  fs[] >> drule abi_decode_getelemptr_abort_ptr >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = Abort _ _`)) >>
  disch_then (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`z`, `w2n (z+n2w off)`, `func`, `ctx`, `PG`, `D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (irule (cj 2 abi_decode_compile_abort_suffix_ptr) >>
     qexistsl_tac [`a'`, `sm`, `v'`] >> fs[inst_extends_def] >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`] >> metis_tac[]
QED

Finalise abi_decode_selected_member_abort

Theorem abi_decode_selected_member_abort_path:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei off q k z h cap /\
  abi_decode_member_code dst pos src hi ei off q sa sb /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?H tf n j. gas_path_ptr D 0 ctx func PG G tn s n H tf
    (Abort a (u with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all abi_decode_selected_member_abort >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  fs[abi_decode_member_code_def] >>
  drule_all abi_decode_member_phase_shape >> strip_tac >>
  `inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def] >>
  `sb.cs_current_bb = sa.cs_current_bb` by suspend "blocks" >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by suspend "opcodes" >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_abort_gas_path_ptr >>
  strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Resume abi_decode_selected_member_abort_path[blocks]:
  `sm.cs_current_bb = sa.cs_current_bb` by
    (Cases_on `dec_info_needs_offset ei`
     >- (fs[] >> drule abiDecodePtrSelectionFrameTheory.abi_decode_selection_shape >>
         simp[same_blocks_def]) >>
     Cases_on `emit_op ADD [pos;Lit (n2w off)] sa` >>
     fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >> gvs[] >>
     drule emit_op_extends >> simp[same_blocks_def]) >>
  `sn.cs_current_bb = sm.cs_current_bb` by
    (drule emit_op_extends >> simp[same_blocks_def]) >>
  fs[abi_decode_member_layout_def] >> gvs[]
  >- (drule abiDecoderClampedWordTheory.abi_decoder_clamped_word_shape >>
      simp[abiDecoderContractTheory.abi_decode_source_opcode_def]) >>
  drule abiDecoderBytesPhasesTheory.abi_decode_bytes_position_shape >>
  simp[abiDecoderContractTheory.abi_decode_source_opcode_def]
QED

Resume abi_decode_selected_member_abort_path[opcodes]:
  `inst_extends sm sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sn ++ emitted_insts sn sb` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts sa sm)` by
    (Cases_on `dec_info_needs_offset ei`
     >- (fs[] >> drule abiDecodePtrSelectionFrameTheory.abi_decode_selection_shape >>
         strip_tac >> fs[EVERY_MEM] >> rpt strip_tac >>
         first_x_assum drule >> simp[fresh_write_op_def] >> metis_tac[]) >>
     Cases_on `emit_op ADD [pos;Lit (n2w off)] sa` >>
     fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >> gvs[] >>
     drule emitted_insts_emit_op >> strip_tac >> gvs[] >> simp[mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts sm sn)` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[] >> simp[mk_inst_def]) >>
  fs[abi_decode_member_layout_def] >> gvs[]
  >- (drule abiDecoderClampedWordTheory.abi_decoder_clamped_word_shape >>
      simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >> strip_tac >> fs[EVERY_MEM]) >>
  drule abiDecoderBytesPhasesTheory.abi_decode_bytes_position_shape >>
  simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >> strip_tac >> fs[EVERY_MEM]
QED

Finalise abi_decode_selected_member_abort_path
