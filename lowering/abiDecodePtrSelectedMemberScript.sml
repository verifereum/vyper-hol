Theory abiDecodePtrSelectedMember
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrNormalized abiDecodePtrMemberDecode
  abiDecoderClampedWord abiDecoderBytesPhases abiDecoderTypedCompose abiDecoderContract
  abiDecoderReservation freshWrites fragExec externalEntryShape abiDecoderAppend
  abiDecodePtrMember ptrDiscipline bodyPtrDefs abiDecoderReentryPointer
  assignTuplePtrLocalBytesCopy
  bodyPtrBopHashSuffix abiDecodePtrSelectionFrame abiDecodePtrWord
  emitHelperProps exprLoweringProps abiEncoder compileEnv
  venomExecSemantics venomState venomInst words arithmetic list

(* Keep the compiler witnesses internal to a whole observed member run. *)
Theorem abi_decode_member_run_phases:
  abi_decode_member_code dst pos src hi ei off q sa sb /\
  abi_decode_member_layout ei off q k z h cap /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?sm sn v out t r.
    compile_getelemptr_abi pos (dec_info_needs_offset ei) off MLOAD
      (Var src) hi sa = (v,sm) /\
    emit_op ADD [Var dst;Lit (n2w q)] sm = (Var out,sn) /\
    compile_abi_decode_to_buf (Var out) v MLOAD (Var src) hi ei sn = ((),sb) /\
    inst_extends sa sm /\ inst_extends sm sn /\ inst_extends sn sb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    r.vs_inst_idx = LENGTH sn.cs_current_insts /\
    run_inst_seq (emitted_insts sa sm) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq (emitted_insts sm sn) t = OK (r with vs_inst_idx := t.vs_inst_idx) /\
    run_inst_seq (emitted_insts sn sb) r = OK (u with vs_inst_idx := r.vs_inst_idx)
Proof
  strip_tac >> fs[abi_decode_member_code_def] >>
  `inst_extends sm sn` by metis_tac[inst_extends_emit_op] >>
  `inst_extends sa sm /\ inst_extends sn sb /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sb)` by suspend "shape" >>
  `inst_extends sm sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
   emitted_insts sm sb = emitted_insts sm sn ++ emitted_insts sn sb` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  `?t. t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sm) /\
    run_inst_seq (emitted_insts sa sm) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq (emitted_insts sm sb) t = OK (u with vs_inst_idx := t.vs_inst_idx)` by
    (irule abi_decode_run_split_normalized >> metis_tac[EVERY_APPEND]) >>
  `?r. r.vs_inst_idx = t.vs_inst_idx + LENGTH (emitted_insts sm sn) /\
    run_inst_seq (emitted_insts sm sn) t = OK (r with vs_inst_idx := t.vs_inst_idx) /\
    run_inst_seq (emitted_insts sn sb) r = OK (u with vs_inst_idx := r.vs_inst_idx)` by
    (mp_tac (abi_decode_run_split_normalized |> Q.INST
      [`xs` |-> `emitted_insts sm sn`, `ys` |-> `emitted_insts sn sb`,
       `s` |-> `t`, `u` |-> `u with vs_inst_idx := t.vs_inst_idx`]) >>
     simp[] >> metis_tac[]) >>
  qexistsl [`t`, `r`] >> simp[] >>
  fs[inst_extends_def] >>
  qpat_x_assum `_ ++ emitted_insts sm sn = sn.cs_current_insts` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
  simp[]
QED

Resume abi_decode_member_run_phases[shape]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule abi_decode_member_pointer_allocation_shape >>
     simp[abi_decode_source_opcode_def] >> strip_tac >> fs[EVERY_MEM]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
     simp[mk_inst_def, is_terminator_def]) >>
  fs[abi_decode_member_layout_def] >> gvs[dec_info_needs_offset_def]
  >- (`inst_extends sa sm` by
        (Cases_on `emit_op ADD [pos;Lit (n2w off)] sa` >>
         fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >>
         metis_tac[inst_extends_emit_op]) >>
      drule abi_decoder_clamped_word_shape >>
      simp[abi_decode_source_opcode_def] >> strip_tac >>
      `inst_extends sn sb` by (irule abi_decoder_inst_extends_prefix >> simp[]) >>
      fs[EVERY_MEM]) >>
  drule abi_decode_bytes_position_shape >>
  simp[abi_decode_source_opcode_def] >> strip_tac >>
  drule abi_decode_selection_shape >> strip_tac >> fs[EVERY_MEM]
QED

Finalise abi_decode_member_run_phases


Theorem abi_decode_member_selection_success:
  compile_getelemptr_abi pos (dec_info_needs_offset ei) off MLOAD
    (Var src) hi sa = (v,sm) /\
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei off q k z h cap /\ fn_has_code sa sm func /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
  ?J tj w.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sm) s J tj /\
    abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sm J tj t /\
    abi_decode_member_frame sa G tn s J tj t (w2n d+q) k /\
    eval_operand v t = SOME w /\ op_prov J v = NONE /\ op_taint tj v = {} /\
    (!x. v = Var x ==> not_fresh_at sm x) /\
    (~dec_info_needs_offset ei ==> w = z+n2w off)
Proof
  strip_tac >>
  drule abi_decode_member_live_resources >> strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_member_live_separation >> strip_tac >>
  (fs[abi_decode_member_layout_def] >> gvs[dec_info_needs_offset_def]
  >- (drule_all abi_decode_static_selection_framed >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      suspend "static_frame") >>
  `w2n (z+n2w off)+32 <= h` by
    (irule LESS_EQ_TRANS >> qexists_tac `w2n z+off+32` >>
     rewrite_tac[word_add_def, w2n_n2w] >>
     `((w2n z + off MOD dimword(:256)) MOD dimword(:256)) <=
       w2n z + off MOD dimword(:256)` by simp[MOD_LESS_EQ] >>
     `off MOD dimword(:256) <= off` by simp[MOD_LESS_EQ] >> decide_tac) >>
  `w2n b+h < dimword(:256)` by
    (fs[abi_decode_member_live_def] >> decide_tac) >>
  mp_tac (Q.INST [`p` |-> `w2n (z+n2w off)`, `sb` |-> `sm`,
    `u` |-> `t with vs_inst_idx := s.vs_inst_idx`]
    abi_decode_selection_success_framed) >>
  (impl_tac >- simp[]) >> strip_tac >> suspend "dynamic_frame")
QED

Resume abi_decode_member_selection_success[static_frame]:
  markerLib.RESUME_TAC >>
  (fs[assignTuplePtrCopyEndpointTheory.ghost_inv_inst_idx, stmt_state_rel_inst_idx,
      lookup_var_def, fresh_vars_wrt_def] >>
   `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)` by
     simp[stateFrameTheory.state_frame_def, venom_state_component_equality] >>
   `abi_decode_member_frame sa G tn s H tf t (w2n d+q) 32` by
     (irule abi_decode_member_frame_readonly >> simp[lookup_var_def]) >>
   `t.vs_current_bb = sm.cs_current_bb` by
     (qpat_x_assum `compile_getelemptr_abi pos F _ _ _ _ _ = _` mp_tac >>
      simp[compile_getelemptr_abi_def, comp_bind_def, comp_return_def,
           emitHelperTheory.emit_op_def, fresh_var_def,
           fresh_id_def, emit_def, comp_ignore_bind_def, LET_THM] >>
      strip_tac >> gvs[]) >>
   `abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sm H tf t` by
     (irule abi_decode_member_live_transport >>
      simp[fresh_vars_wrt_def] >>
      qexistsl_tac [`G`, `w2n d+q`, `32`, `s`, `sa`, `tn`] >>
      simp[] >>
      qpat_x_assum `compile_getelemptr_abi pos F _ _ _ _ _ = _` mp_tac >>
      simp[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >>
      Cases_on `emit_op ADD [pos; Lit (n2w off)] sa` >> simp[] >>
      strip_tac >> gvs[] >>
      qpat_x_assum `emit_op ADD [pos; Lit (n2w off)] sa = _`
        (mp_tac o MATCH_MP exprSimAccountsTheory.emit_op_extends_next_var) >> simp[]) >>
   qexistsl_tac [`H`, `tf`] >> simp[eval_operand_def, lookup_var_def] >> gvs[])
QED

Resume abi_decode_member_selection_success[dynamic_frame]:
  markerLib.RESUME_TAC >>
  (fs[assignTuplePtrCopyEndpointTheory.ghost_inv_inst_idx, stmt_state_rel_inst_idx,
      lookup_var_def, fresh_vars_wrt_def] >>
   `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)` by
     simp[stateFrameTheory.state_frame_def, venom_state_component_equality] >>
   `abi_decode_member_frame sa G tn s H tf t (w2n d+q) (contractABI$ceil32 n+32)` by
     (irule abi_decode_member_frame_readonly >> simp[lookup_var_def]) >>
   `sa.cs_next_var <= sm.cs_next_var` by
     (drule abi_decode_selection_shape >> simp[]) >>
   `abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sm H tf t` by
     (irule abi_decode_member_live_transport >> simp[fresh_vars_wrt_def] >>
      qexistsl_tac [`G`, `w2n d+q`, `contractABI$ceil32 n+32`, `s`, `sa`, `tn`] >> simp[]) >>
   qexistsl_tac [`H`, `tf`] >> simp[eval_operand_def, lookup_var_def] >> gvs[])
QED

Finalise abi_decode_member_selection_success

Theorem abi_decode_member_destination_success:
  emit_op ADD [Var dst;Lit (n2w q)] sm = (Var out,sn) /\
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sm J tj t /\
  q+k <= cap /\ fn_has_code sm sn func ==>
  ?r H tm.
    run_inst_seq (emitted_insts sm sn) t = OK (r with vs_inst_idx := t.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG J tj (emitted_insts sm sn) t H tm /\
    r.vs_inst_idx = LENGTH sn.cs_current_insts /\
    abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sn H tm r /\
    abi_decode_member_frame sm J tj t H tm r (w2n d+q) k /\
    ptr_covers H tm out r k /\ lookup_var out r = SOME (d+n2w q) /\
    not_fresh_at sn out
Proof
  strip_tac >>
  drule abi_decode_member_live_resources >> strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_member_live_separation >> strip_tac >>
  drule_all abi_decode_member_destination_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sm sn) t = OK (r with vs_inst_idx := _)` >>
  `abi_decode_member_frame sm J tj t H tm r (w2n d+q) k` by
    (fs[stateFrameTheory.state_frame_def, venom_state_component_equality] >>
     irule abi_decode_member_frame_readonly >> simp[]) >>
  `sm.cs_next_var <= sn.cs_next_var` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  `sm.cs_current_bb = sn.cs_current_bb` by
    (qpat_x_assum `emit_op ADD [Var dst; Lit (n2w q)] sm = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def,
          emit_def, comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
     strip_tac >> gvs[]) >>
  `abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sn H tm r` by
    (`r.vs_current_bb = t.vs_current_bb` by
       fs[stateFrameTheory.state_frame_def, venom_state_component_equality] >>
     irule abi_decode_member_live_transport >> simp[] >>
     qexistsl_tac [`J`, `w2n d+q`, `k`, `t`, `sm`, `tj`] >> simp[]) >>
  qexistsl_tac [`r`, `H`, `tm`] >> simp[]
QED

Theorem abi_decode_selected_member_success:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei off q k z h cap /\
  abi_decode_member_code dst pos src hi ei off q sa sb /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?H tf t. t = u with vs_inst_idx := LENGTH sb.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
    abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sb H tf t /\
    abi_decode_member_frame sa G tn s H tf t (w2n d+q) k /\
    ?sm sn v out m.
      compile_getelemptr_abi pos (dec_info_needs_offset ei) off MLOAD
        (Var src) hi sa = (v,sm) /\
      emit_op ADD [Var dst;Lit (n2w q)] sm = (Var out,sn) /\
      compile_abi_decode_to_buf (Var out) v MLOAD (Var src) hi ei sn = ((),sb) /\
      32 <= m /\ m <= k /\
      abi_decode_ptr_window H tf t out (d+n2w q) m
Proof
  strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule_all abi_decode_member_run_phases >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK (t with vs_inst_idx := _)` >>
  rename1 `run_inst_seq (emitted_insts sm sn) t = OK (r with vs_inst_idx := _)` >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb` by
    suspend "code_frames" >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all abi_decode_member_selection_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sm) s J tj` >>
  suspend "destination"
QED

Resume abi_decode_selected_member_success[code_frames]:
  conj_tac
  >- (qspec_then `pos` (qspec_then `dec_info_needs_offset ei`
        (qspec_then `off` (qspec_then `MLOAD` mp_tac))) compile_getelemptr_abi_labels >>
      disch_then (qspecl_then [`Var src`, `hi`, `sa`, `\i. T`] mp_tac) >> simp[]) >>
  conj_tac
  >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  metis_tac[cs_extends_abi_decode]
QED

Resume abi_decode_selected_member_success[destination]:
  markerLib.RESUME_TAC >>
  `q+k <= cap` by fs[abi_decode_member_layout_def] >>
  drule_all abi_decode_member_destination_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sm sn) t = OK (r' with vs_inst_idx := _)` >>
  `r' = r` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sn) t = OK (r' with vs_inst_idx := _)` mp_tac >>
     simp[] >> simp[venom_state_component_equality]) >> gvs[] >>
  suspend "decode"
QED

Resume abi_decode_selected_member_success[decode]:
  markerLib.RESUME_TAC >>
  (`eval_operand v r = SOME w /\ op_prov H v = NONE /\ op_taint tm v = {}` by
     (Cases_on `v` >> fs[abi_decode_member_frame_def, eval_operand_def, lookup_var_def,
       ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def,
       venom_state_component_equality] >> metis_tac[]) >>
   `sm.cs_next_var <= sn.cs_next_var` by
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
   `!x. v = Var x ==> not_fresh_at sn x` by
     (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
   drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
     abi_decode_member_decode_success >>
   disch_then (drule_at (Pat `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
   disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
   disch_then (qspecl_then [`w`, `q`, `off`, `k`, `PG`, `D`] mp_tac) >>
   (impl_tac >- simp[]) >> strip_tac >>
   gvs[] >>
   `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
     (drule abi_decoder_member_pointer_counters >> strip_tac >> simp[]) >>
   `abi_decode_member_frame sa G tn s H tm r (w2n d+q) k` by
     (irule abi_decode_member_frame_compose >>
      qexistsl_tac [`J`, `w2n d+q`, `w2n d+q`, `k`, `k`, `sm`, `t`, `tj`] >> simp[]) >>
   `abi_decode_member_frame sa G tn s H' tf
      (u with vs_inst_idx := LENGTH sb.cs_current_insts) (w2n d+q) k` by
     (irule abi_decode_member_frame_compose >>
      qexistsl_tac [`H`, `w2n d+q`, `w2n d+q`, `k`, `k`, `sn`, `r`, `tm`] >> simp[] >> decide_tac) >>
   qexistsl_tac [`H'`, `tf`] >> simp[ADD_COMM] >>
   `inst_extends sm sb` by metis_tac[inst_extends_trans] >>
   `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
    emitted_insts sm sb = emitted_insts sm sn ++ emitted_insts sn sb` by
     metis_tac[emitted_insts_append, inst_extends_def] >>
   `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
     (drule abi_decode_member_pointer_allocation_shape >>
      simp[abi_decode_source_opcode_def] >> strip_tac >> fs[EVERY_MEM]) >>
   `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
     (drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
      simp[mk_inst_def, is_terminator_def]) >>
   `s.vs_inst_idx + LENGTH (emitted_insts sa sm) = t.vs_inst_idx /\
    t.vs_inst_idx + LENGTH (emitted_insts sm sn) = r.vs_inst_idx` by
     (fs[inst_extends_def] >>
      qpat_x_assum `sm.cs_current_insts = _ ++ emitted_insts sa sm`
        (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
      qpat_x_assum `_ ++ emitted_insts sm sn = sn.cs_current_insts`
        (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
   `inst_seq_ptr D 0 ctx func PG J tj (emitted_insts sm sb) t H' tf` by
     (asm_rewrite_tac[] >> irule inst_seq_ptr_append_run >> simp[] >>
      qexistsl_tac [`H`, `tm`] >> simp[] >>
      `r with vs_inst_idx := LENGTH sn.cs_current_insts = r` by
        (simp[venom_state_component_equality]) >> simp[]) >>
   reverse conj_tac
   >- (conj_tac >- metis_tac[ADD_COMM] >> qexists_tac `m` >> simp[]) >>
   asm_rewrite_tac[] >> irule inst_seq_ptr_append_run >> simp[] >>
   qexistsl_tac [`J`, `tj`] >> simp[] >>
   `t with vs_inst_idx := LENGTH sm.cs_current_insts = t` by
     simp[venom_state_component_equality] >> simp[] >>
   qpat_x_assum `inst_seq_ptr _ _ _ _ _ J tj (emitted_insts sm sb) t H' tf`
     mp_tac >> simp[])
QED

Finalise abi_decode_selected_member_success
