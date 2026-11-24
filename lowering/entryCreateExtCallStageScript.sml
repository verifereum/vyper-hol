(* The selected external-call check and dispatch, without ABI decoding. *)
Theory entryCreateExtCallStage
Ancestors
  entryCreateEffectFocus bodyFullExtCallCallStage createSizeCutCode
  externalEntryShape exprSimAbiGasBridge exprLowering emitHelper compileEnv
  fragExec venomInst context list pred_set arithmetic rich_list
  loweringShapeDefs abiEncoderProps

Theorem extcall_stage_inventory:
  comp_ignore_bind
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
     else comp_return ())
    (comp_bind
      (if stat then emit_op STATICCALL [gas;addr;off;len;buf;Lit (n2w cap)]
       else emit_op CALL [gas;addr;value;off;len;buf;Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand;Lit 0w;rds])
         (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand;rds] [])
           (new_block cont_lbl)))))))))) sp = (u,sr) ==>
  create_cut_code {} sp sr /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sp sr)
Proof
  disch_then (strip_assume_tac o MATCH_MP extcall_call_layout) >>
  Cases_on `ret_type = NoneT /\ ~skip` >> Cases_on `stat` >>
  qpat_x_assum `(if ret_type = NoneT /\ ~skip then _ else _) sp = _` mp_tac >>
  simp[compile_extcodesize_check_def, comp_return_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> disch_then (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `emit_op _ _ _ = (success,s2)` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  disch_then (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS) >>
  gvs[fresh_label_def] >>
  gvs[emit_op_def, emit_inst_def, emit_void_def, compile_alloc_buffer_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
      fresh_id_def, emit_def, new_block_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[create_cut_code_def, cs_extends_def, frag_code_def, emitted_blocks_def,
       added_labels_def, all_blocks_def, frag_ids_def, mk_inst_def,
       create_cut_targets_def, DROP_LENGTH_APPEND, DROP_APPEND,
       REVERSE_APPEND, DROP_LENGTH_TOO_LONG,
       DECIDE ``SUC (SUC n) - (n + 2) = 0n``,
       DECIDE ``n + 1 - (n + 2) = 0n``,
       DECIDE ``n - (n + m) = 0n``] >>
  rpt strip_tac >> gvs[create_cut_targets_def]
QED

Theorem extcall_stage_cut:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  fn_has_code sp sr func /\
  comp_ignore_bind
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
     else comp_return ())
    (comp_bind
      (if stat then emit_op STATICCALL [gas;addr;off;len;buf;Lit (n2w cap)]
       else emit_op CALL [gas;addr;value;off;len;buf;Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand;Lit 0w;rds])
         (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand;rds] [])
           (new_block cont_lbl)))))))))) sp = (u,sr) ==>
  create_operand_cut sp sr explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule_then strip_assume_tac extcall_stage_inventory >>
  irule create_effect_suffix_cut >> simp[] >> goal_assum drule
QED
