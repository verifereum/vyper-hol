Theory entryCreateAbiSavedHeadAddressScope
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateCompletedCut
  abiEncodeValuesPhases entryCreatePathScope emitHelperProps abiEncoderProps
  loweringShapeRules
  abiEncoderWindowPhase abiEncoderWindowSequence exprLoweringProps
  compileEnv venomState venomInst words list finite_map pred_set arithmetic pair

Theorem create_abi_saved_head_address_confined:
  emit_op ADD [Var dst;Lit (n2w off)] st = (head,en) /\
  eval_operand (Var dst) s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  off + n <= cap /\ b + cap <= s.vs_alloca_next /\ fn_has_code st en func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?p t G' tn'.
    head = Var p /\ not_fresh_at en p /\ ptr_covers G' tn' p t n /\
    eval_operand head t = SOME (n2w (b+off)) /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\ t.vs_memory = s.vs_memory /\
    create_expr_prefix st en explicit ctx func s [] t /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_values_head_address_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`t`,`G'`,`tn'`] strip_assume_tac)) >>
  `create_operand_at st s` by simp[create_operand_at_def] >>
  `en.cs_current_bb = st.cs_current_bb` by
    (qpat_assum `emit_op ADD _ st = _` (fn th =>
       mp_tac (MATCH_MP emit_op_facts th) >>
       disch_then (qx_choose_then `out` strip_assume_tac) >>
       first_assum ACCEPT_TAC)) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_id IN frag_ids st en /\ i.inst_opcode <> INVOKE /\
      i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by
    (simp[frag_ids_def, mk_inst_def, is_terminator_def]) >>
  `create_operand_full_scope st en explicit ctx func s [] (OK t)` by
    (qpat_assum `t = raw with vs_inst_idx := LENGTH en.cs_current_insts`
       (fn eq => PURE_REWRITE_TAC [eq]) >>
     irule create_admin_sequence_scope >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_assum `create_operand_full_scope _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [create_operand_full_scope_def]) >>
  qpat_assum `en.cs_current_insts = _` (fn th =>
    PURE_REWRITE_TAC [GSYM th]) >>
  qpat_assum `t = raw with vs_inst_idx := LENGTH en.cs_current_insts`
    (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  qexistsl_tac [`STRING #"%" (toString st.cs_next_var)`,`t`,`G'`,`tn'`] >>
  asm_rewrite_tac[]
  >> (gvs[])
QED
