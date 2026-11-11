(* Read-only topic list composition and the counted endpoint boundary. *)
Theory logTopicsRunPtr
Ancestors
  logTopicScalarPtr logTopicFramePtr logInstSeqPtr logValueFramePtr stmtSimLogTopics
  bodyPtrDefs stmtLowering context compileEnv loweringStateRelDefs contextCodegenRel contextCodegenRelProps
  emitHelper emitHelperProps exprLoweringProps venomInst venomState venomExecSemantics
  ptrDiscipline finite_map words list rich_list arithmetic valueEncoding stmtSimLogTopicFresh
  stmtSimLogArgs loweringPosts ghostPcTransportPtr codegenRel fragGasSeqPtr vyperEvent exprSimHash exprSimHashBoundary stmtFragPtr

Theorem log_topic_opcode_shape:
  compile_encode_log_topic x flag sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `flag` >>
  simp[compile_encode_log_topic_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem log_topics_opcode_shape:
  !raw sa ops sb. compile_log_topic_ops raw sa = (ops,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct >- simp[compile_log_topic_ops_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >> simp[compile_log_topic_ops_cons] >> strip_tac >> gvs[] >>
  drule log_topic_inst_extends >> strip_tac >>
  drule log_topics_inst_extends >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  simp[EVERY_APPEND] >> drule log_topic_opcode_shape >> simp[]
QED

Theorem log_readonly_ptr_args:
  !xs vs. LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn s) xs vs /\
  EVERY (\arg. (!p. FST arg = Var p ==> not_fresh_at sm p) /\
               (!l. FST arg <> Label l)) xs /\
  t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
  (!p. not_fresh_at sm p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint tm (Var p) = op_taint tn (Var p)) ==>
  LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) H tm t) xs vs
Proof
  Induct >> Cases_on `vs` >> simp[] >> rpt gen_tac >> strip_tac >>
  suspend "head"
QED
Resume log_readonly_ptr_args[head]:
  rename1 `ptr_val_ok cx (SND arg) v (FST arg) H tm t` >>
  PairCases_on `arg` >> Cases_on `arg0` >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def, op_taint_def, op_prov_def] >>
  metis_tac[]
QED
Finalise log_readonly_ptr_args

Theorem log_arg_rel_inst_idx[simp]:
  log_arg_rel cenv cx sa sb es (s with vs_inst_idx := k) arg v <=>
  log_arg_rel cenv cx sa sb es s arg v
Proof
  Cases_on `arg` >>
  simp[log_arg_rel_def, expr_val_rel_def, expr_val_at_def, local_region_def,
       lookup_var_def]
QED

Theorem ptr_val_ok_inst_idx[simp]:
  ptr_val_ok cx ty v op G tn (s with vs_inst_idx := k) <=>
  ptr_val_ok cx ty v op G tn s
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def]
QED

Theorem compile_log_topic_ops_seq_ptr:
  !xs vs sm ops sb s topics G tn.
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p))) xs) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics (REPLICATE (LENGTH xs) T) (MAP SND xs) vs = SOME topics /\
  LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn s) xs vs /\
  ~ctx_has_dalloca ctx ==>
  ?t Gf tnf. run_inst_seq (emitted_insts sm sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sb) s Gf tnf /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    EVERY (\op. op_taint tnf op = {}) ops /\
    (t with vs_vars := s.vs_vars) = s /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  Induct_on `xs`
  >- (simp[compile_log_topic_ops_def, comp_return_def, encode_indexed_event_topics_def] >>
      rpt strip_tac >> gvs[emitted_insts_def, run_inst_seq_def, inst_seq_ptr_def]) >>
  rpt gen_tac >> Cases_on `vs` >> simp[] >>
  simp[compile_log_topic_ops_cons] >> strip_tac >> gvs[] >>
  rename1 `log_arg_rel cenv cx sa sm es s arg v` >>
  Cases_on `arg` >> gvs[] >>
  drule_all compile_encode_log_topic_scalar_seq_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all log_topic_frontier >> strip_tac >> suspend "tail"
QED
Resume compile_log_topic_ops_seq_ptr[tail]:
  rename1 `compile_encode_log_topic x (is_bytestring_type ty) sm = (op,sc)` >>
  rename1 `run_inst_seq (emitted_insts sm sc) s = OK u` >>
  qpat_x_assum `encode_indexed_event_topics (T::_) _ _ = _` mp_tac >>
  simp[Once encode_indexed_event_topics_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx es u` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >>
     qexists_tac `sm` >> simp[]) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `!p. not_fresh_at sm p ==> lookup_var p u = lookup_var p s` by simp[] >>
  drule_all log_readonly_args >> strip_tac >>
  `u.vs_memory = s.vs_memory` by
    (qpat_assum `u with vs_vars := s.vs_vars = s`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  drule_all log_readonly_ptr_args >> strip_tac >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sc z) /\
              (!l. FST p <> Label l)) xs` by
    (gvs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  qabbrev_tac `ua = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sc)` >>
  suspend "shift"
QED
Resume compile_log_topic_ops_seq_ptr[shift]:
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`log_arg_rel _ _ _ _ _ _ _ _`, `ptr_val_ok _ _ _ _ _ _ _`,
     `supported_scalar_type _`, `evaluate_type _ _ = _`, `value_has_type _ _`,
     `encode_event_topic _ _ = _`, `stmt_state_rel _ _ _ _ _ s`,
     `local_ptrs_reserved cenv sm`, `!z. x = Var z ==> _`, `!l. x <> Label l`,
     `LIST_REL (\arg v. ptr_val_ok _ _ _ _ G tn s) xs t`,
     `LIST_REL (\arg v. log_arg_rel _ _ _ sm _ s _ _ /\ _) xs t`] >>
  `stmt_state_rel ctx func cenv cx es ua` by simp[Abbr `ua`, stmt_state_rel_inst_idx] >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sc es ua arg v /\
      supported_scalar_type (SND arg) /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs t` by
    simp[Abbr `ua`] >>
  `LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) Gf tnf ua) xs t` by
    simp[Abbr `ua`] >>
  first_x_assum drule_all >> strip_tac >> suspend "compose"
QED
Resume compile_log_topic_ops_seq_ptr[compose]:
  rename1 `run_inst_seq (emitted_insts sc sb) ua = OK w` >>
  rename1 `inst_seq_ptr D 0 ctx func PG Gf tnf (emitted_insts sc sb) ua H tm` >>
  rpt (qpat_x_assum `LIST_REL _ xs _` kall_tac) >>
  rpt (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` kall_tac) >>
  qpat_x_assum `encode_indexed_event_topics _ _ _ = _` kall_tac >>
  drule log_topic_inst_extends >> strip_tac >>
  drule log_topics_inst_extends >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sc) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sc sb)` by
    (drule log_topic_opcode_shape >> drule log_topics_opcode_shape >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sm sb) s = OK (w with vs_inst_idx := u.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sb) s H tm` by
    (once_asm_rewrite_tac[] >> irule successful_seq_ptr_append >>
     simp[Abbr `ua`] >> qexistsl_tac [`Gf`, `tnf`] >> simp[] >>
     metis_tac[ADD_COMM]) >>
  qexistsl_tac [`w with vs_inst_idx := u.vs_inst_idx`, `H`, `tm`] >>
  simp[] >> suspend "post"
QED
Resume compile_log_topic_ops_seq_ptr[post]:
  `eval_operand op w = eval_operand op u /\ op_taint tm op = op_taint tnf op` by
    (Cases_on `op` >> gvs[eval_operand_def, op_taint_def, lookup_var_def, Abbr `ua`]) >>
  simp[] >> conj_tac
  >- (`w with <|vs_vars := s.vs_vars; vs_inst_idx := u.vs_inst_idx|> =
        (w with vs_vars := ua.vs_vars) with
          <|vs_vars := s.vs_vars; vs_inst_idx := u.vs_inst_idx|>` by simp[] >>
      pop_assum SUBST1_TAC >>
      qpat_assum `w with vs_vars := ua.vs_vars = ua` (fn th => rewrite_tac[th]) >>
      simp[Abbr `ua`]) >>
  rpt strip_tac >>
  `not_fresh_at sc p` by metis_tac[not_fresh_at_mono] >>
  gvs[Abbr `ua`, lookup_var_def]
QED
Finalise compile_log_topic_ops_seq_ptr

Theorem compile_split_log_topics_seq_ptr:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  LENGTH flags = LENGTH xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn s) xs vs /\
  ~ctx_has_dalloca ctx ==>
  ?t Gf tnf. run_inst_seq (emitted_insts sm sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sb) s Gf tnf /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    EVERY (\op. op_taint tnf op = {}) ops /\
    (t with vs_vars := s.vs_vars) = s /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    stmt_state_rel ctx func cenv cx es t /\
    LIST_REL (log_arg_rel cenv cx sa sb es t)
      (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) /\
    LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) Gf tnf t)
      (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) /\
    wb_frame cenv es es sm s t /\
    EVERY (\op. (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) ops
Proof
  strip_tac >>
  drule_all compile_split_log_topics_run >> strip_tac >>
  `LENGTH vs = LENGTH xs` by metis_tac[LIST_REL_LENGTH] >>
  drule_all log_indexed_selection_rel >> strip_tac >>
  qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ _ _ /\ _) xs vs`
    (mp_then Any mp_tac log_indexed_selection_rel) >>
  disch_then drule >> strip_tac >>
  drule_all log_indexed_selection_every >> strip_tac >>
  drule_all log_indexed_encoding_select >> strip_tac >>
  drule_all split_log_ops_select >> strip_tac >>
  `compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p)))
     (MAP FST (FILTER SND (ZIP (xs,flags))))) sm = (ops,sb)` by
    (qpat_x_assum `compile_log_topic_ops (FST _) _ = _` mp_tac >>
     simp[MAP_MAP_o, combinTheory.o_DEF]) >>
  `encode_indexed_event_topics
     (REPLICATE (LENGTH (MAP FST (FILTER SND (ZIP (xs,flags))))) T)
     (MAP SND (MAP FST (FILTER SND (ZIP (xs,flags)))))
     (MAP FST (FILTER SND (ZIP (vs,flags)))) = SOME topics` by metis_tac[] >>
  drule_all compile_log_topic_ops_seq_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "post"
QED
Resume compile_split_log_topics_seq_ptr[post]:
  gvs[] >>
  rpt (qpat_x_assum `LIST_REL _ (MAP FST _) _` kall_tac) >>
  rpt (qpat_x_assum `encode_indexed_event_topics _ _ _ = _` kall_tac) >>
  qpat_x_assum `EVERY _ (MAP FST _)` kall_tac >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with vs_vars := s.vs_vars = s`
      (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  `!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s` by simp[] >>
  drule_all log_readonly_ptr_args >> strip_tac >>
  drule_all split_log_ops_data_rel >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[] >> gvs[]
QED
Finalise compile_split_log_topics_seq_ptr

Theorem compile_split_log_topics_path_ptr:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  LENGTH flags = LENGTH xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) G tn s) xs vs /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ghost_kept cenv es sa0 G0 tn0 s0 G tn /\ sa0.cs_next_var <= sm.cs_next_var ==>
  ?t Gf tnf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    EVERY (\op. op_taint tnf op = {}) ops /\
    stmt_state_rel ctx func cenv cx es t /\
    LIST_REL (log_arg_rel cenv cx sa sb es t)
      (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) /\
    LIST_REL (\arg v. ptr_val_ok cx (SND arg) v (FST arg) Gf tnf t)
      (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) /\
    EVERY (\op. (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) ops /\
    ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sa0 G0 tn0 s0 Gf tnf /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sm sb) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_memory = s.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. not_fresh_at sm p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!limit_st. sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
      fresh_vars_wrt limit_st t)
Proof
  strip_tac >> drule_all compile_split_log_topics_seq_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_inv d cenv cx es Gf tnf t` by
    (irule ghost_inv_readonly_transport >> goal_assum (drule_at Any) >> simp[] >>
     qpat_x_assum `t with vs_vars := s.vs_vars = s`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  `ghost_kept cenv es sa0 G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_readonly_transport >> goal_assum (drule_at Any) >>
     qexistsl_tac [`G`, `sm`] >> simp[]) >>
  suspend "path"
QED
Resume compile_split_log_topics_path_ptr[path]:
  drule log_topics_opcode_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sb)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  `!limit_st. sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
    fresh_vars_wrt limit_st t` by metis_tac[log_topics_fresh] >>
  rpt (qpat_x_assum `LIST_REL _ xs vs` kall_tac) >>
  qpat_x_assum `encode_indexed_event_topics _ _ _ = _` kall_tac >>
  qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)`,
                 `Gf`, `tnf`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  suspend "endpoint"
QED
Resume compile_split_log_topics_path_ptr[endpoint]:
  conj_tac >- gvs[] >>
  conj_tac
  >- (qpat_x_assum `LIST_REL (\arg v. ptr_val_ok _ _ _ _ _ _ _) _ _` kall_tac >>
      irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_readonly_transport >> goal_assum (drule_at Any) >>
      qexists_tac `sm` >> gvs[lookup_var_def]) >>
  conj_tac
  >- (qpat_x_assum `t with vs_vars := s.vs_vars = s`
        (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t with vs_vars := s.vs_vars = s`
        (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  conj_tac
  >- (`t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> =
       (t with vs_vars := s.vs_vars) with vs_inst_idx := s.vs_inst_idx` by simp[] >>
      pop_assum SUBST1_TAC >> asm_rewrite_tac[] >> simp[]) >>
  gvs[lookup_var_def] >>
  simp[fresh_vars_wrt_def] >> metis_tac[fresh_vars_wrt_def]
QED
Finalise compile_split_log_topics_path_ptr
