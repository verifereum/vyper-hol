(* The exact emitted keyword store gives a zero-mark prefix up to its cut. *)
Theory entryCreateKeywordStoreRun
Ancestors
  bytesCopyCode fragExec emitHelperProps
  createSizePrefixReplay venomExecSemantics venomInst venomState
  fragGasSeqAbort exprLoweringProps venomInstProps fragGasOrigin gasEvents
  relation createMarkedPath entryCreatePathScope instIdxIndep
  createSizeCutCode createSizeTypedCopyCode abiEncoderProps context compileEnv
  emitHelper arithmetic list rich_list pair pred_set

(* A completed scalar or byte-copy store takes only the emitted sequence.
   Convert that exact run, not an unrestricted zero-GAS path, to the cut. *)
Theorem grouped_store_sequence_prefix[local]:
  !code s t bb.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                 i.inst_opcode <> GAS /\ i.inst_id IN frag_ids a b) code /\
    s.vs_inst_idx + LENGTH code = LENGTH b.cs_current_insts /\
    run_inst_seq code s = OK t ==>
    create_expr_prefix a b explicit ctx fn s []
      (t with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  Induct >> simp[run_inst_seq_def, Excl "IS_PREFIX"] >> rpt gen_tac >> strip_tac
  >- (`s with vs_inst_idx := LENGTH b.cs_current_insts = s` by
        simp[venom_state_component_equality] >> simp[]) >>
  `isPREFIX (h::code) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> fs[]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  `step_inst 0 ctx h s = step_inst_base h s` by simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `gas_origin_edge F explicit ctx fn s [] (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[gas_origin_edge_def] >>
     qexists_tac `0` >> simp[step_inst_non_invoke, gas_events_step_def]) >>
  `create_prefix_step a b explicit ctx fn s [] (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[create_prefix_step_def] >> qexistsl_tac [`bb`,`h`] >> simp[] >> decide_tac) >>
  `create_expr_prefix a b explicit ctx fn s [] (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >> simp[create_marked_edge_def]) >>
  drule_then irule (SIMP_RULE bool_ss [APPEND_NIL] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    (SPEC_ALL create_expr_prefix_append))) >>
  qpat_assum `!s t bb. _ ==> _` (qspecl_then
    [`u with vs_inst_idx := SUC s.vs_inst_idx`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `bb`]
    mp_tac) >>
  impl_tac >-
    (simp[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES] >>
     `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
     simp[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES] >> decide_tac) >>
  simp[venom_state_fupdfupds]
QED

Theorem grouped_keyword_store_layout:
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))])
    a = ((),b) ==>
  create_cut_code {} a b /\
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  emitted_insts a b <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS /\ i.inst_id IN frag_ids a b)
    (emitted_insts a b)
Proof
  Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >> simp[] >>
  TRY (strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
       drule emit_void_same_blocks >> simp[same_blocks_def] >> strip_tac >>
       conj_tac >-
         (qpat_assum `emit_void _ _ a = ((),b)`
            (SUBST1_TAC o SYM o REWRITE_RULE[SND] o AP_TERM ``SND:unit # compile_state -> compile_state``) >>
          simp[create_cut_code_emit_void, create_cut_targets_def]) >>
       simp[mk_inst_def, is_terminator_def, frag_ids_def] >> NO_TAC) >>
  strip_tac >> drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
  `b.cs_next_id = a.cs_next_id + 6` by
    gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
        emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  conj_tac >-
    (`compile_store_memory ce src dst ty ty a = ((),b)` by simp[compile_store_memory_def] >>
     metis_tac[create_store_memory_cut_code, SND]) >>
  fs[same_blocks_def, bytes_copy_insts_def, mk_inst_def, is_terminator_def, frag_ids_def]
QED

Theorem grouped_keyword_store_run_prefix:
  (if is_word_type ty then emit_void MSTORE [dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src dst
   else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))])
    mid = ((),last) /\
  fn_has_code mid last fn /\
  ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
  t.vs_inst_idx = LENGTH mid.cs_current_insts /\
  run_inst_seq (emitted_insts mid last) t = OK (u with vs_inst_idx := t.vs_inst_idx) /\
  u.vs_inst_idx = LENGTH last.cs_current_insts ==>
  create_expr_prefix mid last explicit ctx fn t [] u
Proof
  strip_tac >> drule grouped_keyword_store_layout >> strip_tac >>
  `?bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts mid last) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `t.vs_inst_idx + LENGTH (emitted_insts mid last) = LENGTH last.cs_current_insts` by simp[] >>
  drule_all grouped_store_sequence_prefix >>
  disch_then (qspecl_then [`explicit`,`ctx`] mp_tac) >>
  simp[venom_state_fupdfupds] >>
  `u with vs_inst_idx := LENGTH mid.cs_current_insts + LENGTH (emitted_insts mid last) = u` by
    simp[venom_state_component_equality] >> simp[]
QED
