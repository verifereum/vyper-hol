Theory decoderMemberValidEndpoint
Ancestors
  abiDecoderValidMemberCons abiDecoderReentryPointer abiDecoderVarExtend
  abiDecoderReentry abiDecoderVarSequence
  abiDecoderReservation abiDecoderMemberSetup abiDecoderDynamicLoopSetup
  abiValidMember abiValidDecodedMetadata abiDecoderDynamic abiDecoderArraySetupInputs
  abiDecoderValidContract abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiEncoder fragExec
  compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomState venomInst instIdxIndep finite_map words list arithmetic

(* This is ordinary observation transport only: no ghost is transported through
   pruning. The supplied sequence fixes the original-state endpoint. *)
Theorem member_pointer_endpoint_observations[local]:
  compile_getelemptr_abi src dyn off opc (Lit 0w) hi st = (member_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  (dyn ==> abi_decode_load opc (n2w (sb + off):bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  run_inst_seq (emitted_insts st st') initial = OK actual ==>
  eval_operand member_op actual = SOME (n2w (sb + if dyn then payload_off else off)) /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ inst_extends st st'
Proof
  strip_tac >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w sb)` by
    simp[abi_decoder_prune_eval] >>
  `dyn ==> abi_decode_load opc (n2w (sb + off):bytes32)
      (abi_decoder_prune_vars st.cs_next_var initial) = n2w payload_off /\
      sb + payload_off < dimword (:256)` by
    fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)` by
    irule abi_decoder_prune_fresh >>
  drule_all abi_decoder_member_pointer_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  `abi_decoder_vars_extend initial.vs_vars
     (abi_decoder_prune_vars st.cs_next_var initial) initial` by
    irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  gvs[] >>
  `eval_operand member_op actual = SOME (n2w (sb + if dyn then payload_off else off))` by
    (irule abi_decoder_vars_extend_eval >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decoder_sequence_halted >> strip_tac >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w` by
    (rpt strip_tac >>
     `eval_operand op (abi_decoder_prune_vars st.cs_next_var initial) = SOME w` by
       simp[abi_decoder_prune_eval] >>
     `eval_operand op clean = SOME w` by
       (qpat_x_assum `!op w. eval_operand op (abi_decoder_prune_vars _ _) = _ ==> _`
          drule >> simp[]) >>
     drule_all abi_decoder_vars_extend_eval >> simp[]) >>
  `dyn ==> abi_decode_source_opcode opc` by simp[] >>
  drule_all abi_decode_member_pointer_allocation_shape >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  fs[abi_decoder_prune_vars_def, abi_decoder_address_frame_def]
QED

Theorem add_endpoint_observations[local]:
  emit_op ADD [left;right] st = (out,st') /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  eval_operand out t = SOME (a + b) /\
  abi_decoder_address_frame st.cs_next_var s t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def] >>
  strip_tac >> gvs[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    abi_decoder_address_frame_def] >>
  rpt strip_tac >> Cases_on `op` >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem member_setup_endpoint_observations[local]:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w) dyn ao vo st = (ops,ready) /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (sb + ao):bytes32) initial = n2w off /\
    sb + off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  run_inst_seq (emitted_insts st ready) initial = OK actual ==>
  eval_operand (FST ops) actual = SOME (n2w (sb + if dyn then off else ao)) /\
  eval_operand (SND ops) actual = SOME (n2w (d + vo)) /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ inst_extends st ready
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) st = (ep,mid)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] mid = (childdst,ready)` >>
  `inst_extends st mid /\ inst_extends mid ready` by
    (conj_tac >-
      (Cases_on `dyn` >>
       qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
       simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
       rpt (pairarg_tac >> gvs[]) >>
       metis_tac[inst_extends_emit_op, inst_extends_trans]) >>
     metis_tac[inst_extends_emit_op]) >>
  `emitted_insts st ready = emitted_insts st mid ++ emitted_insts mid ready` by
    (qspecl_then [`st`,`mid`,`ready`] mp_tac emitted_insts_append >> fs[inst_extends_def]) >>
  `?prepared. run_inst_seq (emitted_insts st mid) initial = OK prepared` by
    (spose_not_then assume_tac >>
     qspecl_then [`emitted_insts st mid`,`emitted_insts mid ready`,`initial`]
       mp_tac run_inst_seq_append_err >> gvs[]) >>
  `run_inst_seq (emitted_insts mid ready) prepared = OK actual` by
    (qpat_assum `run_inst_seq (emitted_insts st mid) initial = _`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts mid ready` mp_tac) >> fs[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule member_pointer_endpoint_observations >>
  disch_then (qspecl_then [`sb`,`off`,`initial`,`prepared`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> strip_tac >>
  `eval_operand dst prepared = SOME (n2w d)` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w vo)) prepared = SOME (n2w vo)` by simp[eval_operand_def] >>
  drule_all add_endpoint_observations >> strip_tac >>
  drule abi_decoder_member_pointer_counters >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var` by (Cases_on `dyn` >> gvs[]) >>
  `eval_operand ep actual = SOME (n2w (sb + if dyn then off else ao))` by
    (qpat_x_assum `abi_decoder_address_frame _ prepared actual` mp_tac >>
     simp[abi_decoder_address_frame_def] >> strip_tac >>
     first_x_assum irule >> gvs[]) >>
  `abi_decoder_address_frame st.cs_next_var initial actual` by
    (irule abi_decoder_address_frame_trans >> qexistsl_tac [`mid.cs_next_var`,`prepared`] >> simp[]) >>
  simp[word_add_n2w] >> metis_tac[inst_extends_trans]
QED

Theorem calldata_member_valid_pre_endpoint:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size pre)) vo st = (ops,ready) /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ vyper_to_abi_type env ty::ats) bs bs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
        (DROP (SUM (MAP abi_member_head_size pre)) bs))) = SOME v /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st ready) initial = OK actual ==>
  abi_decoder_valid_pre ce env sf ty tv
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs)) v ready
    (FST ops) (SND ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    0 (sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre))) (d + vo) b cap
    (actual with vs_inst_idx := LENGTH ready.cs_current_insts)
Proof
  strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_valid_member_window >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  drule_all abi_decoder_valid_member_readable >> strip_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
    abi_decode_load CALLDATALOAD (n2w (sb + SUM (MAP abi_member_head_size pre)):bytes32) initial =
      n2w (abi_decode_member_offset (vyper_to_abi_type env ty) bs
        (SUM (MAP abi_member_head_size pre))) /\
    sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre)) < dimword (:256)` by
    (strip_tac >> asm_simp_tac bool_ss []) >>
  drule_all member_setup_endpoint_observations >> strip_tac >>
  qmatch_goalsub_abbrev_tac `abi_decoder_valid_pre ce env sf ty tv childbs` >>
  qabbrev_tac `ao = SUM (MAP abi_member_head_size pre)` >>
  qabbrev_tac `off = abi_decode_member_offset (vyper_to_abi_type env ty) bs ao` >>
  `eval_operand (FST ops) actual = SOME (n2w (sb + off))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     fs[Abbr `off`, abi_decode_member_offset_def]) >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by simp[abi_decoder_operand_live_def] >>
  drule_all abi_valid_member_child_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_source >>
  disch_then (qspec_then `CALLDATALOAD` assume_tac) >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  simp[abi_decoder_valid_pre_def, abi_decoder_operand_live_def] >>
  conj_tac
  >- (qpat_x_assum `abi_decoder_ranges _ _ _ (FST ops) _ _ _ _ _ _ _ _ actual` mp_tac >>
      simp[abi_decoder_ranges_def, eval_op_inst_idx,
        arithmeticTheory.ADD_COMM]) >>
  simp[abi_decode_source_def, arithmeticTheory.ADD_COMM] >>
  fs[abi_decode_source_def]
QED
