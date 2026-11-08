Theory abiDecodePtrSelectedMember
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrNormalized
  abiDecoderClampedWord abiDecoderBytesPhases abiDecoderTypedCompose abiDecoderContract
  abiDecoderReservation freshWrites
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

(* Restore the original iteration operands, not the generated temporaries. *)
Theorem abi_decode_member_live_transport[local]:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_member_frame sa G tn s H tf t a k /\
  sa.cs_next_var <= sb.cs_next_var /\
  w2n d <= a /\ a+k <= w2n d+cap /\
  ghost_inv ret cenv cx es H tf t /\ stmt_state_rel ctx func cenv cx es t /\
  fresh_vars_wrt sb t /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  t.vs_current_bb = sb.cs_current_bb ==>
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sb H tf t
Proof
  strip_tac >>
  `abi_decode_ptr_window H tf t src b h /\ ptr_covers H tf dst t cap` by
    (conj_tac
     >- (irule abi_decode_member_frame_window >>
         goal_assum (drule_at (Pat `abi_decode_member_frame _ _ _ _ _ _ _ _ _`)) >>
         fs[abi_decode_member_live_def] >> decide_tac) >>
     irule abi_decode_member_frame_covers >>
     goal_assum (drule_at (Pat `abi_decode_member_frame _ _ _ _ _ _ _ _ _`)) >>
     fs[abi_decode_member_live_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!name b n. local_region cenv es.scopes t name b n <=>
               local_region cenv es.scopes s name b n` by
    (rpt gen_tac >> irule bodyPtrBopHashFrameTheory.bop_local_region_readonly_frame >>
     qexists_tac `sa` >> fs[abi_decode_member_live_def, abi_decode_member_frame_def]) >>
  fs[abi_decode_member_live_def, abi_decode_member_frame_def] >>
  suspend "operands"
QED

Resume abi_decode_member_live_transport[operands]:
  markerLib.RESUME_TAC >>
  `t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels` by
    (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand pos t = SOME z /\ eval_operand hi t = SOME (n2w h)` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[eval_operand_def] >> metis_tac[]) >>
  `op_prov H pos = NONE /\ op_prov H hi = NONE /\
   op_taint tf pos = {} /\ op_taint tf hi = {}` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  simp[] >> metis_tac[local_ptrs_reserved_next_var]
QED

Finalise abi_decode_member_live_transport
