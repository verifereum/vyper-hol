(* The immutable copy uses the same straight-line band in both modes. *)
Theory createCtorImmutableCopyBand
Ancestors
  createCtorStraightBand exprSimAbiEncodeObliviousCode exprPtrUnwrapCodeCopySemantic
  exprPtrUnwrapCodeCopyShape exprPtrUnwrapCode immutableCopyExecution
  loweringHalt fragExec instIdxIndep context compileEnv exprLowering
  exprSimCopy exprLoweringProps exprPtrUnwrapAllocation createSizeLocationCode
  createSizeCutCode abiEncoderProps
  venomState venomInst venomExecSemantics list rich_list relation words arithmetic

Theorem immutable_copy_range_action[local]:
  !n off. code_action (\opc. opc <> INVOKE /\ ~is_terminator opc)
    (compile_imm_copy_to_memory is_ctor imm src dst n off)
Proof
  `!base pos. code_action (\opc. opc <> INVOKE /\ ~is_terminator opc)
    (compile_lit_byte_offset base pos)` by
    (qx_gen_tac `src_operand` >> gen_tac >> simp[compile_lit_byte_offset_def] >>
     IF_CASES_TAC >> Cases_on `src_operand` >>
     simp[code_action_return, code_action_emit_op, is_terminator_def]) >>
  Induct >> gen_tac >> simp[compile_imm_copy_to_memory_def, code_action_return] >>
  irule code_action_bind >> simp[] >>
  gen_tac >> irule code_action_bind >> reverse conj_tac
  >- (Cases_on `is_ctor` >> Cases_on `imm` >> simp[compile_imm_load_word_def, code_action_emit_op,
         code_action_bind, is_terminator_def]) >>
  gen_tac >> BETA_TAC >> irule code_action_bind >>
  simp[code_action_ignore_bind, code_action_emit_void,
       is_terminator_def]
QED

Theorem immutable_copy_band:
  compile_alloc_buffer nb sb = (buf,mid) /\ buf.buf_operand = Var root /\
  compile_imm_copy_to_memory is_ctor imm src buf.buf_operand n 0 mid = ((),sc) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ copy_runtime_frame mid a sc z /\
  fn_has_code sb sc func /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  RTC (\r t. ?i. ctor_segment_fetch func r = SOME i /\
                  sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
                  i.inst_opcode <> INVOKE /\ ctor_segment_next func r i = SOME t)
      s (z with vs_inst_idx := LENGTH sc.cs_current_insts)
Proof
  strip_tac >>
  `code_step (\opc. opc <> INVOKE /\ ~is_terminator opc) sb mid /\
   code_step (\opc. opc <> INVOKE /\ ~is_terminator opc) mid sc` by
    (conj_tac
     >- (mp_tac (Q.SPEC `\opc. opc <> INVOKE /\ ~is_terminator opc`
                 code_action_alloc_buffer) >>
         simp[is_terminator_def, code_action_def] >> metis_tac[]) >>
     mp_tac (Q.SPECL [`n`, `0`] (Q.INST [`dst` |-> `buf.buf_operand`] immutable_copy_range_action)) >>
     simp[code_action_def] >> metis_tac[]) >>
  drule_all code_step_trans >> strip_tac >>
  drule_all unwrap_code_copy_shifted_run >> strip_tac >>
  `sc.cs_blocks = sb.cs_blocks /\ sc.cs_current_bb = sb.cs_current_bb /\
   sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc` by
    (drule compile_alloc_buffer_insts >> strip_tac >>
     fs[copy_runtime_frame_def, same_blocks_def] >>
     qpat_assum `sc.cs_current_insts = _` (fn th =>
       CONV_TAC (RAND_CONV (REWR_CONV emitted_insts_def)) >>
       CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV th)))) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `frag_code sb sc = emitted_insts sb sc` by simp[frag_code_open] >>
  fs[code_step_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by fs[EVERY_MEM] >>
  `?r. run_inst_seq (emitted_insts sb sc) s = OK r /\ z = r with vs_inst_idx := k` by
    (qpat_x_assum `run_inst_seq _ (s with vs_inst_idx := k) = OK z` mp_tac >>
     simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sb sc) s` >> simp[exec_result_map_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sb sc) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code sb sc func` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
     qexists_tac `bb` >> gvs[IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  drule_all ctor_straight_band_run >> simp[]
QED

Theorem unwrap_code_copy_layout:
  unwrap_value ce (LocatedValue ty p) a = (op,b) /\
  p.ptr_location = LocCode /\ ~is_word_type ty ==>
  same_blocks a b /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;ILOAD;DLOAD;MSTORE])
    (emitted_insts a b)
Proof
  strip_tac >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ a = (buf,mid)` >>
  `same_blocks a mid` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def, same_blocks_def,
          fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  Cases_on `ce.ce_is_ctor` >> fs[] >>
  FIRST [drule code_ctor_copy_insts, drule code_copy_insts] >> strip_tac >>
  `emitted_insts mid b = is` by
    (qpat_assum `b.cs_current_insts = _` (fn th =>
       pure_rewrite_tac[emitted_insts_def, th, DROP_LENGTH_APPEND]) >> REFL_TAC) >>
  `emitted_insts a b = emitted_insts a mid ++ emitted_insts mid b` by
    (irule emitted_insts_append >> simp[]) >>
  (conj_tac >- metis_tac[same_blocks_trans] >>
   conj_tac >- (pure_rewrite_tac[APPEND_ASSOC] >> simp[]) >>
   fs[EVERY_MEM, mk_inst_def] >> rpt strip_tac >> gvs[] >>
   qpat_x_assum `!j. MEM j (emitted_insts _ _) ==> _`
     (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> simp[])
QED

(* The recorded list execution is over the actual fetched instruction band. *)
Theorem immutable_unwrap_run_band:
  unwrap_value ce (LocatedValue ty p) a = (op,b) /\
  p.ptr_location = LocCode /\ ~is_word_type ty /\ fn_has_code a b func /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a b) s = OK r ==>
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
                  i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
      s (r with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all unwrap_code_copy_layout >> strip_tac >>
  `frag_code a b = emitted_insts a b` by fs[same_blocks_def,frag_code_open] >>
  `create_cut_code {} a b` by
    (mp_tac (Q.INST [`vv` |-> `LocatedValue ty p`] create_unwrap_cut_code) >> simp[]) >>
  `EVERY (\i. a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id)
     (emitted_insts a b)` by fs[create_cut_code_def,EVERY_MEM,frag_ids_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts a b)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!i. MEM i _ ==> i.inst_opcode = ALLOCA \/ _`
       (drule_then strip_assume_tac) >> fs[is_terminator_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts a b) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code a b func` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
     qexists_tac `bb` >> gvs[same_blocks_def,IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  drule_all ctor_straight_band_run >> simp[]
QED
