Theory abiDecodePtrTwoMember
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrSelectedMember abiDecodePtrSelectedAbort
  abiDecodePtrContinuation abiEncoder abiDecoderAppend abiDecoderTypedCompose
  abiDecoderReentryPointer abiDecoderCounters loweringShapeRules freshWrites
  exprLoweringProps emitHelperProps context
  bodyPtrDefs venomState venomExecSemantics ptrDiscipline
  assignTuplePtrLocalBytesCopy fragExec instSeqComposePtr words arithmetic list

(* The consumer uses only member endpoints, never the word/bytes cases. *)
Theorem abi_decode_two_member_success:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei1 off q k1 z h cap /\
  abi_decode_member_layout ei2 (off+abi_sz) (q+mem_sz) k2 z h cap /\
  k1 <= mem_sz /\
  abi_decode_member_code dst pos src hi ei1 off q sa sm /\
  abi_decode_member_code dst pos src hi ei2 (off+abi_sz) (q+mem_sz) sm sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  run_inst_seq (emitted_insts sa sm) s = OK u1 /\
  run_inst_seq (emitted_insts sm sb)
    (u1 with vs_inst_idx := LENGTH sm.cs_current_insts) = OK u2 ==>
  ?J tj H tf t r x m.
    t = u1 with vs_inst_idx := LENGTH sm.cs_current_insts /\
    r = u2 with vs_inst_idx := LENGTH sb.cs_current_insts /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sm) s J tj /\
    inst_seq_ptr D 0 ctx func PG J tj (emitted_insts sm sb) t H tf /\
    abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sb H tf r /\
    abi_decode_member_frame sa G tn s H tf r (w2n d+q) (mem_sz+k2) /\
    32 <= m /\ m <= k1 /\ not_fresh_at sm x /\
    abi_decode_ptr_window J tj t x (d+n2w q) m /\
    abi_decode_ptr_window H tf r x (d+n2w q) m /\
    mem_bytes_at (w2n d+q) m r.vs_memory = mem_bytes_at (w2n d+q) m t.vs_memory
Proof
  strip_tac >>
  drule_all abi_decode_selected_member_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
  rename1 `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sm) s J tj` >>
  `not_fresh_at sm out` by
    (drule emit_op_facts >> strip_tac >> gvs[] >>
     drule abi_decoder_variable_counter >> strip_tac >>
     irule not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_decode_selected_member_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `compile_getelemptr_abi _ _ _ _ _ _ sa = _` mp_tac >>
     disch_then (mp_tac o MATCH_MP abi_decoder_member_pointer_counters) >>
     strip_tac >>
     qpat_assum `emit_op _ _ sm' = _` (mp_tac o MATCH_MP emit_op_facts) >> strip_tac >>
     qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = ((),sm)`
       (mp_tac o MATCH_MP abi_decoder_variable_counter) >> strip_tac >>
     gvs[] >> Cases_on `dec_info_needs_offset ei1` >>
     Cases_on `hi = Lit 0w` >> gvs[] >> decide_tac) >>
  `w2n (d+n2w q) = w2n d+q` by
    (drule abi_decode_member_live_separation >> strip_tac >>
     `q <= cap` by fs[abi_decode_member_layout_def] >>
     simp[word_add_def, w2n_n2w] >>
     `q < dimword(:256) /\ w2n d+q < dimword(:256)` by decide_tac >>
     simp[]) >>
  qexistsl_tac [`J`, `tj`, `H`, `tf`, `out`, `m`] >> simp[] >>
  conj_tac >- (irule abi_decode_member_frame_compose >>
    goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
    simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (irule abi_decode_member_frame_window >>
    goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `abi_decode_member_frame sm _ _ _ _ _ _ _ _`
    (mp_tac o GEN_ALL o MATCH_MP (cj 1 (REWRITE_RULE [GSYM AND_IMP_INTRO] abi_decode_member_frame_bytes))) >>
  disch_then (qspecl_then [`m`, `q+w2n d`] mp_tac) >> simp[]
QED

Theorem abi_decode_two_member_second_abort:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_layout ei1 off q k1 z h cap /\
  abi_decode_member_layout ei2 (off+abi_sz) (q+mem_sz) k2 z h cap /\
  abi_decode_member_code dst pos src hi ei1 off q sa sm /\
  abi_decode_member_code dst pos src hi ei2 (off+abi_sz) (q+mem_sz) sm sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  run_inst_seq (emitted_insts sa sm) s = OK u1 /\
  run_inst_seq (emitted_insts sm sb)
    (u1 with vs_inst_idx := LENGTH sm.cs_current_insts) = Abort a u2 ==>
  ?H tf. inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa sm ++ emitted_insts sm sb) s H tf
Proof
  strip_tac >>
  drule_all abi_decode_selected_member_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
  drule_all abi_decode_selected_member_abort >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm) /\
   inst_extends sa sm` by suspend "shape" >>
  qpat_assum `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sa _ _ _`
    (mp_tac o MATCH_MP abi_decode_member_live_compiler) >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sm) = LENGTH sm.cs_current_insts` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND]) >>
  qexistsl_tac [`H'`, `tf'`] >>
  irule inst_seq_ptr_append_run >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Resume abi_decode_two_member_second_abort[shape]:
  drule_all abi_decode_member_phase_shape >> strip_tac >>
  `inst_extends sm' sm` by metis_tac[inst_extends_trans] >>
  `inst_extends sa sm` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sm = emitted_insts sa sm' ++ emitted_insts sm' sn ++ emitted_insts sn sm` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  simp[EVERY_APPEND]
QED

Finalise abi_decode_two_member_second_abort
