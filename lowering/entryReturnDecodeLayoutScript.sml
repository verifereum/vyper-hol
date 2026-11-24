(* Code and cursor layout of the non-default external-call return stage. *)
Theory entryReturnDecodeLayout
Ancestors
  createSizeCutCode createSizeCutOpens createSizeDecodeCode extcallReturnDecoderCode
  exprSimAbiDecodeResourceMutual exprSimAbiDecodeFramed exprSimAbiDecodeResource
  exprSimAbiDecodeShape exprSimAbiDecodeTraceSafe exprSimAbiDecodeTrace
  exprSimAbiGasBridge exprSimAbiDecodeSiteCoverage
  abiDecoderVarSequence abiEncoder builtinSimple exprLowering emitHelperProps
  emitHelper context compileEnv fragExec venomInst list rich_list pair pred_set string

val linear_code = [compile_alloc_buffer_def, compile_return_value_decode_def,
  compile_select_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
  emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def];

Theorem return_decode_prefix_layout[local]:
  compile_alloc_buffer nbytes sr = (buf,ar) /\
  compile_return_value_decode mn mx ar = (hi,hs) ==>
  create_cut_code {} sr hs /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sr hs) /\
  hs.cs_blocks = sr.cs_blocks /\ hs.cs_current_bb = sr.cs_current_bb /\
  hs.cs_next_label = sr.cs_next_label
Proof
  strip_tac >> conj_tac
  >- (irule create_cut_code_join >> qexists_tac `ar` >> conj_tac
      >- metis_tac[create_alloc_buffer_cut_code, SND] >>
      `create_cut_code {} ar (SND (compile_return_value_decode mn mx ar))` by
        (rewrite_tac[compile_return_value_decode_def, compile_select_def] >>
         rpt (FIRST [irule create_cut_code_bind_all >> BETA_TAC,
           irule create_cut_code_ignore_bind >> BETA_TAC,
           conj_tac, gen_tac,
           CHANGED_TAC (simp[create_cut_code_emit_op, create_cut_code_emit_void,
                             create_cut_targets_def])])) >>
      qpat_x_assum `create_cut_code _ _ (SND _)` mp_tac >> simp[]) >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp linear_code >> strip_tac >>
  qpat_x_assum `compile_return_value_decode _ _ _ = _` mp_tac >>
  simp linear_code >> strip_tac >>
  `hs.cs_blocks = sr.cs_blocks` by gvs[] >>
  simp[frag_code_same_blocks] >>
  rpt (qpat_x_assum `(_ : compile_state) = _` (SUBST1_TAC o SYM)) >>
  simp_tac (srw_ss()) [Excl "APPEND_ASSOC"] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

(* The decoder starts with no pending labels, so every switch is supplied
   by a fresh_label in that decoder, not by the surrounding function. *)
Theorem return_decoder_labels[local]:
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD src hi info a = ((),b) /\
  (!suffix k. a.cs_next_label <= k ==> a.cs_current_bb <> fresh_label_output suffix k) ==>
  ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b))
Proof
  strip_tac >>
  `?ex. dst <> Label ex /\ src <> Label ex /\ hi <> Label ex` by
    (`FINITE {l | dst = Label l \/ src = Label l \/ hi = Label l}` by
       (irule SUBSET_FINITE >>
        qexists_tac `IMAGE (\opd. @l. opd = Label l) {dst;src;hi}` >>
        simp[SUBSET_DEF, IN_IMAGE] >> rpt strip_tac >>
        qexists_tac `Label x` >> gvs[]) >>
     drule (REWRITE_RULE [NOT_IN_FINITE] INFINITE_STR_UNIV) >> simp[] >>
     metis_tac[]) >>
  `decode_framed ex (compile_abi_decode_to_buf dst (Lit 0w) MLOAD src hi info)
       (\u. T)` by simp[decode_framed_to_buf] >>
  `?Q. decode_resource_run ex {} (compile_abi_decode_to_buf dst (Lit 0w) MLOAD src hi info)
         a () b Q` by
    (drule (REWRITE_RULE [EMPTY_SUBSET] (Q.INST [`P` |-> `{}`] decode_framed_run)) >>
     disch_then (fn th => irule (SIMP_RULE (srw_ss()) [] th)) >> simp[]) >>
  drule decode_resource_run_trace >> simp[] >> strip_tac >>
  `~MEM a.cs_current_bb (decode_switches es)` by
    (fs[SUBSET_DEF, decode_label_range_def] >> metis_tac[]) >>
  `ALL_DISTINCT (decode_switches es)` by fs[decode_trace_safe_def] >>
  `emitted_blocks a (decode_history b (decode_replay es a)) =
   emitted_blocks a (decode_replay es a)` by
    simp[emitted_blocks_def, decode_history_def] >>
  qpat_assum `b = decode_history _ _` (fn th => pure_once_rewrite_tac [th]) >>
  qpat_assum `emitted_blocks _ (decode_history _ _) = _` (fn th =>
    pure_once_rewrite_tac [th]) >>
  pure_rewrite_tac[decode_history_def] >>
  `(decode_replay es a).cs_current_bb ::
      MAP (\bb. bb.bb_label) (emitted_blocks a (decode_replay es a)) =
    REVERSE (decode_switches es) ++ [a.cs_current_bb]` by
    simp[decode_replay_labels] >>
  `ALL_DISTINCT (REVERSE (decode_switches es) ++ [a.cs_current_bb])` by
    simp[ALL_DISTINCT_APPEND, MEM_REVERSE] >>
  simp[] >> metis_tac[ALL_DISTINCT]
QED

Theorem extcall_decode_return_layout:
  compile_alloc_buffer nbytes sr = (buf,ar) /\
  compile_return_value_decode mn mx ar = (hi,hs) /\
  compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD src hi info hs = ((),sb) /\
  (!suffix k. sr.cs_next_label <= k ==> sr.cs_current_bb <> fresh_label_output suffix k) ==>
  create_cut_code {} sr sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sr sb) /\
  ALL_DISTINCT (sb.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks sr sb)) /\
  (emitted_blocks sr sb = [] ==>
   sr.cs_current_bb = sb.cs_current_bb /\
   LENGTH sr.cs_current_insts <= LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all return_decode_prefix_layout >> strip_tac >>
  `create_cut_code {} hs sb` by
    (mp_tac (Q.INST [`load` |-> `MLOAD`, `dst` |-> `buf.buf_operand`,
        `src` |-> `Lit 0w`, `bop` |-> `src`] create_decode_to_buf_cut_code) >>
     simp[create_cut_targets_def] >> disch_then (qspec_then `hs` mp_tac) >> simp[]) >>
  `create_cut_code {} sr sb` by metis_tac[create_cut_code_join] >> simp[] >>
  conj_tac
  >- (`!i. MEM i (frag_code sr sb) <=>
         MEM i (frag_code sr hs) \/ MEM i (frag_code hs sb)` by
        (irule abi_decode_frag_code_compose >> fs[create_cut_code_def]) >>
      simp[EVERY_MEM] >> gen_tac >> strip_tac
      >- fs[EVERY_MEM] >>
      drule return_decoder_frag_code >> simp[EVERY_MEM] >>
      disch_then drule >> simp[abi_decoder_reentry_opcode_def] >>
      strip_tac >> simp[]) >>
  conj_tac
  >- (`emitted_blocks sr sb = emitted_blocks hs sb` by simp[emitted_blocks_def] >>
      `!suffix k. hs.cs_next_label <= k ==>
         hs.cs_current_bb <> fresh_label_output suffix k` by simp[] >>
      drule_all return_decoder_labels >> simp[]) >>
  fs[create_cut_code_def] >> drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks sr sb = []` >> simp[IS_PREFIX_LENGTH]
QED

(* The call's continuation was allocated before the return decoder's labels. *)
Theorem extcall_return_cursor_fresh:
  comp_bind (fresh_label "extcall_fail") (\fail_lbl.
    comp_bind (fresh_label "extcall_cont") (\cont_lbl.
    comp_ignore_bind (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
      (comp_ignore_bind (new_block fail_lbl)
      (comp_bind (emit_op RETURNDATASIZE []) (\rds.
      comp_bind (compile_alloc_buffer 0) (\fail_buf.
      comp_ignore_bind (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
        (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
          (new_block cont_lbl)))))))) sc = (u,sr) ==>
  !suffix k. sr.cs_next_label <= k ==>
    sr.cs_current_bb <> fresh_label_output suffix k
Proof
  simp (linear_code @ [fresh_label_def, emit_inst_def, new_block_def]) >>
  strip_tac >> gvs[] >> rpt strip_tac >>
  drule fresh_label_output_inj >> simp[] >> decide_tac
QED
