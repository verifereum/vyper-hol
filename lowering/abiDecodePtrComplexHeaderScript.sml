(* The scalar prefix of a bounded complex decoder, before member iteration. *)
Theory abiDecodePtrComplexHeader
Ancestors
  abiDecodePtrMemberInterface abiDecodePtrScalarFrame abiDecodePtrPrims
  abiDecoderRange abiEncoder bodyPtrBopScalarCompile bodyPtrBopScalarSeq
  stmtReasonLitFragMemory fragGasSeqPtr stateFrame
  bodyPtrBopScalarOutcome abiEncoderWindowLookup freshWrites
  exprSimPtrProps assignTuplePtrLoadStep emitHelper emitHelperProps
  exprLoweringProps compileEnv bodyPtrDefs ptrDiscipline fragExec
  venomState venomInst venomExecSemantics words arithmetic list rich_list pred_set

Theorem abi_decode_complex_bounded_split:
  hi <> Lit 0w /\
  compile_abi_decode_to_buf dst pos opc src hi (DecComplex dyn infos) sa = ((),last) ==>
  ?e sm sb.
    emit_op ADD [pos;Lit (n2w (FOLDR (\(_,asz:num,_:num) acc. asz+acc) 0 infos))]
      sa = (e,sm) /\
    compile_abi_decode_range_check pos e hi sm = ((),sb) /\
    compile_abi_decode_complex_elems dst pos opc src hi infos 0 0 sb = ((),last)
Proof
  strip_tac >>
  gvs[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  ` (\(_:abi_dec_info,asz:num,_:num) acc. acc + asz) =
    (\(_:abi_dec_info,asz:num,_:num) acc. asz + acc)` by
    (simp[FUN_EQ_THM, pairTheory.FORALL_PROD, ADD_COMM]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> metis_tac[]
QED

Theorem abi_decode_complex_header_shape:
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
    EVERY (not_fresh_at sb) i.inst_outputs) (emitted_insts sa sb)
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def] >>
  strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, fresh_write_op_def,
       not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_complex_header_scalar:
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) /\
  pos IN A /\ hi IN A /\ Lit (n2w static_sz) IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  strip_tac >>
  `bop_scalar_seq R A (emitted_insts sa sm) (e INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos;Lit (n2w static_sz)]`] >> simp[]) >>
  `!x. x IN R ==> not_fresh_at sm x` by
    (drule emitted_insts_emit_op >> strip_tac >> fs[not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `?B. bop_scalar_seq R (e INSERT A) (emitted_insts sm sb) B` by
    (irule abi_decode_range_scalar >> simp[] >> metis_tac[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >>
     drule compile_abi_decode_range_check_shape >>
     drule inst_extends_emit_op >> simp[inst_extends_def]) >>
  qexists_tac `B` >> simp[] >> irule bop_scalar_seq_append >>
  qexists_tac `e INSERT A` >> simp[]
QED

Theorem abi_decode_complex_header_success:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H tf.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tf
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi
      sb H tf (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  drule abi_decode_member_live_compiler >> strip_tac >>
  drule abi_decode_member_live_resources >> strip_tac >>
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x}
    {pos;hi;Lit (n2w static_sz)} (emitted_insts sa sb) B` by
    (irule abi_decode_complex_header_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {pos;hi;Lit (n2w static_sz)} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac[IN_INSERT, NOT_IN_EMPTY] >> rpt strip_tac >>
     gvs[] >> simp[op_prov_def, op_taint_def]) >>
  drule_all abi_decode_scalar_success_frame >>
  disch_then (qspecl_then [`LENGTH sb.cs_current_insts`, `func`, `PG`, `D`]
    strip_assume_tac) >>
  fs[IN_GSPEC_IFF] >>
  qexistsl_tac [`H`, `tm`] >>
  conj_tac >- suspend "path" >>
  reverse conj_tac
  >- (qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  suspend "live"
QED

Resume abi_decode_complex_header_success[path]:
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def, emitted_insts_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
    (qpat_x_assum `sb.cs_current_insts = _ ++ _` mp_tac >>
     disch_then (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Resume abi_decode_complex_header_success[live]:
  qmatch_goalsub_abbrev_tac `abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sb H tm u` >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   u.vs_memory = s.vs_memory /\ u.vs_current_bb = sb.cs_current_bb` by
    (unabbrev_all_tac >>
     qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> fs[Abbr `u`] >>
     first_x_assum (qspec_then `Var x` mp_tac) >> simp[]) >>
  `abi_decode_member_frame sa G tn s H tm u (w2n d) 0` by
    (irule abi_decode_member_frame_readonly >> simp[] >> gvs[]) >>
  `ghost_inv ret cenv cx es H tm u` by
    (irule ghost_inv_old_vars_frame_ptr >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> simp[] >> gvs[]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (irule stmt_state_rel_old_vars_frame_ptr >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> simp[] >> gvs[Abbr `u`]) >>
  `fresh_vars_wrt sb s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[]) >>
  `fresh_vars_wrt sb t` by
    (irule abi_window_seq_fresh >>
     qexistsl_tac [`sb`, `emitted_insts sa sb`, `s`] >> simp[] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> _` drule >>
     strip_tac >> gvs[fresh_write_op_simple]) >>
  irule abi_decode_member_live_transport >>
  simp[Abbr `u`] >>
  conj_tac >- fs[fresh_vars_wrt_def] >>
  goal_assum (drule_at (Pat `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`w2n d`, `0`] >> simp[]
QED

Finalise abi_decode_complex_header_success
