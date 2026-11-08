Theory stmtSimLogTopics
Ancestors
  exprBopSimProps
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogArgs stmtSimLogSource stmtLowering compileEnv context
  exprSimHash  exprSimWordArgs vyperEvent valueEncoding
  emitHelper emitHelperProps exprLoweringProps venomExecSemantics venomState
  venomInst freshWrites words string finite_map list ASCIInumbers supportedTypes
  vyperTyping vyperValue exprSimLiteralBuffer byte exprSimOps

Theorem split_log_ops_select:
  !xs flags. LENGTH flags = LENGTH xs ==>
    FST (split_log_ops xs flags) =
      MAP (\p. (FST (FST p), is_bytestring_type (SND (FST p))))
        (FILTER SND (ZIP (xs,flags))) /\
    SND (split_log_ops xs flags) =
      MAP FST (FILTER (\p. ~SND p) (ZIP (xs,flags)))
Proof
  Induct_on `xs`
  >- (Cases_on `flags` >> simp[split_log_ops_def]) >>
  Cases_on `h` >> Cases_on `flags` >> simp[] >>
  rename1 `split_log_ops _ (flag::flags)` >> Cases_on `flag` >>
  simp[split_log_ops_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> pairarg_tac >> gvs[]
QED

Theorem split_log_ops_lengths:
  !xs flags. LENGTH flags = LENGTH xs ==>
    LENGTH (FST (split_log_ops xs flags)) = LENGTH (FILTER I flags) /\
    LENGTH (SND (split_log_ops xs flags)) = LENGTH (FILTER ($~) flags)
Proof
  Induct_on `xs`
  >- (Cases_on `flags` >> simp[split_log_ops_def]) >>
  Cases_on `h` >> Cases_on `flags` >> simp[] >>
  rename1 `split_log_ops _ (flag::flags)` >> Cases_on `flag` >>
  simp[split_log_ops_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> pairarg_tac >> gvs[]
QED

Theorem split_log_ops_data_types:
  !xs flags. LENGTH flags = LENGTH xs ==>
    MAP SND (SND (split_log_ops xs flags)) =
      log_non_indexed_types flags (MAP SND xs)
Proof
  Induct_on `xs`
  >- (Cases_on `flags` >> simp[split_log_ops_def, log_non_indexed_types_def]) >>
  Cases_on `h` >> Cases_on `flags` >> simp[] >>
  rename1 `split_log_ops _ (flag::flags)` >> Cases_on `flag` >>
  simp[split_log_ops_def, log_non_indexed_types_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> pairarg_tac >> gvs[]
QED

Theorem log_split_data_every:
  !xs flags. LENGTH flags = LENGTH xs /\ EVERY P xs ==>
    EVERY P (SND (split_log_ops xs flags))
Proof
  Induct >- (Cases_on `flags` >> simp[split_log_ops_def]) >>
  gen_tac >> PairCases_on `h` >> Cases_on `flags` >> simp[] >>
  rename1 `split_log_ops _ (flag::flags)` >> Cases_on `flag` >>
  simp[split_log_ops_def] >> rpt strip_tac >> pairarg_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem split_log_ops_data_rel:
  !xs vs flags. LIST_REL P xs vs /\ LENGTH flags = LENGTH xs ==>
    LIST_REL P (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)
Proof
  Induct_on `xs`
  >- (Cases_on `vs` >> Cases_on `flags` >>
      simp[split_log_ops_def, log_non_indexed_values_def]) >>
  Cases_on `h` >> Cases_on `vs` >> Cases_on `flags` >> simp[] >>
  rename1 `split_log_ops _ (flag::flags)` >> Cases_on `flag` >>
  simp[split_log_ops_def, log_non_indexed_values_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> pairarg_tac >> gvs[]
QED

Theorem compile_encode_log_topic_bytes_run:
  compile_encode_log_topic ptr_op T sa = (op,sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[compile_encode_log_topic_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, bind_outputs_def] >>
  `eval_operand ptr_op
     (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w b + 32w) s) =
     SOME (n2w b)` by
    (Cases_on `ptr_op` >> gvs[eval_operand_def, lookup_var_update_var] >>
     gvs[not_fresh_at_def]) >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def] >>
  `b < dimword (:256)` by decide_tac >>
  `mload b s = n2w (LENGTH bs)` by gvs[mload_def, mem_word_at_def] >>
  simp[Once run_inst_seq_def] >>
  simp[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `step_inst_base ins u` >>
  `step_inst_base ins u = OK
     (update_var (STRING #"%" (toString (sa.cs_next_var + 2)))
       (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) u)` by
    (simp[Abbr `ins`] >> irule step_SHA3_bytes >>
     simp[Abbr `u`, eval_operand_def, lookup_var_update_var, toString_inj,
       word_add_n2w, mload_def, update_var_def, GSYM mem_word_at_def]) >>
  simp[run_inst_seq_def, Abbr `u`, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_assum (qspec_then `sa.cs_next_var + 2` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var + 1` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var` assume_tac) >> gvs[]
QED

Theorem log_arg_footprint_bound:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sb es s (op,ty) v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ eval_operand op s = SOME p ==>
  w2n p + val_footprint tv v < dimword (:256)
Proof
  simp[log_arg_rel_def] >> strip_tac >>
  Cases_on `val_footprint tv v = 0` >- simp[w2n_lt] >>
  drule_all expr_val_at_footprint >> strip_tac
  >- (irule hash_live_footprint_bound >> goal_assum (drule_at Any) >> metis_tac[])
  >- (irule hash_live_footprint_bound >> goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[]
QED

Theorem compile_encode_log_topic_word_run:
  compile_encode_log_topic ptr_op F sa = (op,sb) /\
  eval_operand ptr_op s = SOME w ==>
  run_inst_seq (emitted_insts sa sb) s = OK s /\ eval_operand op s = SOME w
Proof
  simp[compile_encode_log_topic_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem log_topic_count_exact:
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 ==>
  LENGTH (h::FST (split_log_ops xs flags)) <= 4 /\
  w2n (n2w (LENGTH (h::FST (split_log_ops xs flags))) : 256 word) =
    LENGTH (h::FST (split_log_ops xs flags))
Proof
  strip_tac >> drule split_log_ops_lengths >> strip_tac >> simp[] >>
  `4 < dimword (:256)` by simp[dimword_def] >> simp[]
QED

Theorem log_bytestring_arg_view:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sb es s (op,ty) v /\
  supported_scalar_type ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  ?b bs. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    encode_event_topic ty v = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs))
Proof
  Cases_on `ty` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def, is_bytestring_type_def]
  >~ [`BaseT (BytesT bd)`]
  >- (Cases_on `bd` >>
      simp[supported_word_type_def, supported_string_type_def, is_bytestring_type_def] >>
      suspend "bytes") >>
  suspend "string"
QED

Resume log_bytestring_arg_view[bytes]:
  simp[evaluate_type_def] >> strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def] >>
  rename1 `log_arg_rel cenv cx sa sb es s (op,BaseT (BytesT (Dynamic cap))) (BytesV bs)` >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
     SOME (BaseTV (BytesT (Dynamic cap))) /\
   ~is_word_type (BaseT (BytesT (Dynamic cap)))` by
    simp[evaluate_type_def, is_word_type_def] >>
  `?p. eval_operand op s = SOME p` by gvs[log_arg_rel_def, expr_val_rel_def] >>
  `expr_val_rel cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) op s` by
    gvs[log_arg_rel_def] >>
  drule_all expr_val_rel_memory >>
  disch_then (strip_assume_tac o SRULE [val_in_memory_def, LET_THM]) >>
  drule_all log_arg_footprint_bound >> simp[val_footprint_def] >> strip_tac >>
  qexistsl_tac [`w2n p`, `bs`] >>
  simp[encode_event_topic_def, is_event_bytestring_type_def, word_of_bytes_be_def] >> decide_tac
QED

Resume log_bytestring_arg_view[string]:
  simp[evaluate_type_def] >> strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def] >>
  rename1 `log_arg_rel cenv cx sa sb es s (op,BaseT (StringT cap)) (StringV str)` >>
  `evaluate_type (get_tenv cx) (BaseT (StringT cap)) = SOME (BaseTV (StringT cap)) /\
   ~is_word_type (BaseT (StringT cap))` by simp[evaluate_type_def, is_word_type_def] >>
  `?p. eval_operand op s = SOME p` by gvs[log_arg_rel_def, expr_val_rel_def] >>
  `expr_val_rel cx (BaseT (StringT cap)) (StringV str) op s` by gvs[log_arg_rel_def] >>
  drule_all expr_val_rel_memory >>
  disch_then (strip_assume_tac o SRULE [val_in_memory_def, LET_THM]) >>
  drule_all log_arg_footprint_bound >> simp[val_footprint_def] >> strip_tac >>
  qexistsl_tac [`w2n p`, `MAP (n2w o ORD) str`] >>
  simp[encode_event_topic_def, is_event_bytestring_type_def, word_of_bytes_be_def] >>
  decide_tac
QED
Finalise log_bytestring_arg_view

Theorem log_scalar_topic_shape:
  supported_scalar_type ty ==>
  (is_event_bytestring_type ty = is_bytestring_type ty) /\
  (~is_bytestring_type ty ==> supported_word_type ty /\ is_word_type ty)
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def, is_event_bytestring_type_def, is_bytestring_type_def,
    is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
    is_event_bytestring_type_def, is_bytestring_type_def, is_word_type_def] >>
  rename1 `BaseT (BytesT bd)` >> Cases_on `bd` >>
  simp[supported_word_type_def, supported_string_type_def,
    is_event_bytestring_type_def, is_bytestring_type_def, is_word_type_def]
QED

Theorem compile_encode_log_topic_scalar_run:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sm es s (x,ty) v /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  compile_encode_log_topic x (is_bytestring_type ty) sm = (op,sb) ==>
  ?t topic. run_inst_seq (emitted_insts sm sb) s = OK t /\
    encode_event_topic ty v = SOME topic /\
    eval_operand op t = SOME topic /\
    (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s)
Proof
  strip_tac >> drule_all log_scalar_topic_shape >> strip_tac >>
  Cases_on `is_bytestring_type ty`
  >- (drule_all log_bytestring_arg_view >> strip_tac >>
      gvs[] >> drule_all compile_encode_log_topic_bytes_run >> strip_tac >>
      qexists_tac `t` >> simp[]) >>
  gvs[] >>
  `supported_word_type ty /\ is_word_type ty` by simp[] >>
  `eval_operand x s = SOME (typed_val_to_w256 tv v)` by
    gvs[log_arg_rel_def, expr_val_rel_def] >>
  drule_all log_word_topic >> strip_tac >>
  drule_all compile_encode_log_topic_word_run >> strip_tac >>
  qexistsl_tac [`s`, `typed_val_to_w256 tv v`] >> simp[]
QED

(* The generic shape theorem is local to loweringShapeProps; expose the
   frontier facts needed by read-only topic composition here. *)
Theorem log_topic_frontier:
  compile_encode_log_topic x flag sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ (!l. x <> Label l) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)
Proof
  Cases_on `flag` >>
  simp[compile_encode_log_topic_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[not_fresh_at_def, cs_extends_def, toString_inj] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >> simp[]
QED

Theorem log_readonly_frame:
  (t with vs_vars := s.vs_vars) = s /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) ==>
  wb_frame cenv es sa s t
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. z with vs_vars := t.vs_vars`) >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  simp[wb_frame_def, locals_kept_def]
QED

Theorem log_readonly_arg:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sm.cs_next_id <= sb.cs_next_id /\
  (t with vs_vars := s.vs_vars) = s /\
  (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
  (!z. FST arg = Var z ==> not_fresh_at sm z) /\ (!l. FST arg <> Label l) /\
  supported_scalar_type (SND arg) /\ log_arg_rel cenv cx sa sm es s arg v ==>
  log_arg_rel cenv cx sa sb es t arg v
Proof
  strip_tac >>
  `wb_frame cenv es sm s t` by (irule log_readonly_frame >> simp[]) >>
  irule log_arg_rel_frame >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem compile_log_topic_ops_cons:
  compile_log_topic_ops (x::xs) sa = (ops,sb) <=>
  ?op sm rest. compile_encode_log_topic (FST x) (SND x) sa = (op,sm) /\
    compile_log_topic_ops xs sm = (rest,sb) /\ ops = op::rest
Proof
  simp[Once compile_log_topic_ops_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compile_log_topic_ops_frontier:
  !raw sa ops sb.
    compile_log_topic_ops raw sa = (ops,sb) /\
    EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sa z) /\
                (!l. FST p <> Label l)) raw ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\op. (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) ops
Proof
  Induct_on `raw`
  >- simp[compile_log_topic_ops_def, comp_return_def, cs_extends_refl] >>
  rpt gen_tac >> simp[compile_log_topic_ops_cons] >> strip_tac >> gvs[] >>
  drule_all log_topic_frontier >> strip_tac >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) raw` by
    (gvs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  metis_tac[cs_extends_trans, not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem log_readonly_args:
  !xs vs.
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sm.cs_next_id <= sb.cs_next_id /\
  (t with vs_vars := s.vs_vars) = s /\
  (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs ==>
  LIST_REL (\arg v. log_arg_rel cenv cx sa sb es t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs
Proof
  Induct_on `xs` >> Cases_on `vs` >> simp[] >> rpt strip_tac
  >- (drule_all log_readonly_arg >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_topic_inst_extends:
  compile_encode_log_topic x flag sa = (op,sb) ==> inst_extends sa sb
Proof
  Cases_on `flag` >>
  simp[compile_encode_log_topic_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[] >- (imp_res_tac inst_extends_emit_op >> metis_tac[inst_extends_trans]) >>
  simp[inst_extends_refl]
QED

Theorem log_topics_inst_extends:
  !raw sa ops sb.
    compile_log_topic_ops raw sa = (ops,sb) ==> inst_extends sa sb
Proof
  Induct_on `raw`
  >- simp[compile_log_topic_ops_def, comp_return_def, inst_extends_refl] >>
  simp[compile_log_topic_ops_cons] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> drule log_topic_inst_extends >>
  metis_tac[inst_extends_trans]
QED

Theorem compile_log_topic_ops_run:
  !xs vs sm ops sb s topics.
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p))) xs) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics (REPLICATE (LENGTH xs) T) (MAP SND xs) vs = SOME topics ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s)
Proof
  Induct_on `xs`
  >- (simp[compile_log_topic_ops_def, comp_return_def, encode_indexed_event_topics_def] >>
      rpt strip_tac >> gvs[emitted_insts_def, run_inst_seq_def]) >>
  rpt gen_tac >> Cases_on `vs` >> simp[] >>
  simp[compile_log_topic_ops_cons] >> strip_tac >> gvs[] >>
  rename1 `log_arg_rel cenv cx sa sm es s arg v` >>
  Cases_on `arg` >> gvs[] >>
  drule_all compile_encode_log_topic_scalar_run >> strip_tac >>
  drule_all log_topic_frontier >> strip_tac >>
  suspend "compose"
QED

Resume compile_log_topic_ops_run[compose]:
  rename1 `compile_encode_log_topic x (is_bytestring_type ty) sm = (op,sc)` >>
  rename1 `run_inst_seq (emitted_insts sm sc) s = OK u` >>
  qpat_x_assum `encode_indexed_event_topics (T::_) _ _ = _` mp_tac >>
  simp[Once encode_indexed_event_topics_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx es u` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all log_readonly_args >> strip_tac >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sc z) /\
              (!l. FST p <> Label l)) xs` by
    (gvs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]) >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sc sb) u = OK w` >>
  `eval_operand op w = SOME topic` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sc`, `u`] >> simp[]) >>
  `w with vs_vars := s.vs_vars = s` by
    (qpat_x_assum `w with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. z with vs_vars := s.vs_vars`) >> simp[]) >>
  drule log_topic_inst_extends >> strip_tac >>
  drule log_topics_inst_extends >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm sc ++ emitted_insts sc sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  qexists_tac `w` >> simp[] >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sm sc) s = OK u`
        (mp_then Any (qspec_then `emitted_insts sc sb` mp_tac) run_inst_seq_append) >> simp[]) >>
  qx_gen_tac `key` >> strip_tac >>
  `not_fresh_at sc key` by (irule not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
  simp[]
QED
Finalise compile_log_topic_ops_run

Theorem log_indexed_selection_rel:
  !xs vs flags. LIST_REL P xs vs /\ LENGTH flags = LENGTH xs ==>
    LIST_REL P (MAP FST (FILTER SND (ZIP (xs,flags))))
               (MAP FST (FILTER SND (ZIP (vs,flags))))
Proof
  Induct_on `xs`
  >- (Cases_on `vs` >> Cases_on `flags` >> simp[]) >>
  Cases_on `vs` >> Cases_on `flags` >> simp[] >> rpt strip_tac >>
  rename1 `if flag then _ else _` >> Cases_on `flag` >> simp[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_indexed_selection_every:
  !xs flags. LENGTH flags = LENGTH xs /\ EVERY P xs ==>
    EVERY P (MAP FST (FILTER SND (ZIP (xs,flags))))
Proof
  Induct_on `xs`
  >- (Cases_on `flags` >> simp[]) >>
  Cases_on `flags` >> simp[] >> rpt strip_tac >>
  rename1 `if flag then _ else _` >> Cases_on `flag` >> simp[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_indexed_encoding_select:
  !xs vs flags. LENGTH flags = LENGTH xs /\ LENGTH vs = LENGTH xs ==>
    encode_indexed_event_topics flags (MAP SND xs) vs =
    encode_indexed_event_topics
      (REPLICATE (LENGTH (MAP FST (FILTER SND (ZIP (xs,flags))))) T)
      (MAP SND (MAP FST (FILTER SND (ZIP (xs,flags)))))
      (MAP FST (FILTER SND (ZIP (vs,flags))))
Proof
  Induct_on `xs`
  >- (Cases_on `vs` >> Cases_on `flags` >> simp[encode_indexed_event_topics_def]) >>
  Cases_on `vs` >> Cases_on `flags` >> simp[] >> rpt strip_tac >>
  rename1 `if flag then _ else _` >> Cases_on `flag` >>
  simp[Once encode_indexed_event_topics_def] >>
  first_x_assum drule_all >> strip_tac >> simp[Once encode_indexed_event_topics_def]
QED

Theorem compile_split_log_topics_run:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  LENGTH flags = LENGTH xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    stmt_state_rel ctx func cenv cx es t /\
    LIST_REL (log_arg_rel cenv cx sa sb es t)
      (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) /\
    wb_frame cenv es sm s t /\
    EVERY (\op. (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) ops
Proof
  strip_tac >>
  `LENGTH vs = LENGTH xs` by metis_tac[LIST_REL_LENGTH] >>
  drule_all log_indexed_selection_rel >> strip_tac >>
  drule_all log_indexed_selection_every >> strip_tac >>
  drule_all log_indexed_encoding_select >> strip_tac >>
  drule_all split_log_ops_select >> strip_tac >>
  qpat_x_assum `compile_log_topic_ops _ _ = _` mp_tac >>
  simp[] >> strip_tac >>
  `compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p)))
     (MAP FST (FILTER SND (ZIP (xs,flags))))) sm = (ops,sb)` by
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
  `encode_indexed_event_topics
     (REPLICATE (LENGTH (MAP FST (FILTER SND (ZIP (xs,flags))))) T)
     (MAP SND (MAP FST (FILTER SND (ZIP (xs,flags)))))
     (MAP FST (FILTER SND (ZIP (vs,flags)))) = SOME topics` by metis_tac[] >>
  drule_all compile_log_topic_ops_run >> strip_tac >>
  suspend "post"
QED

Resume compile_split_log_topics_run[post]:
  qpat_x_assum `encode_indexed_event_topics flags _ _ = _` kall_tac >>
  qpat_x_assum `encode_indexed_event_topics flags _ _ = _` kall_tac >>
  qpat_x_assum `encode_indexed_event_topics (REPLICATE _ _) _ _ = _` kall_tac >>
  qpat_x_assum `LIST_REL _ (MAP FST _) _` kall_tac >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l))
    (MAP (\p. (FST p,is_bytestring_type (SND p)))
      (MAP FST (FILTER SND (ZIP (xs,flags)))))` by gvs[EVERY_MAP] >>
  drule_all compile_log_topic_ops_frontier >> strip_tac >>
  drule_all (Q.SPECL [`xs`, `vs`] log_readonly_args) >> strip_tac >>
  `LIST_REL (log_arg_rel cenv cx sa sb es t) xs vs` by
    (irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all split_log_ops_data_rel >> strip_tac >>
  qexists_tac `t` >> gvs[] >> conj_tac
  >- (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  irule log_readonly_frame >> simp[]
QED
Finalise compile_split_log_topics_run

Theorem compile_log_topic_ops_length:
  !raw sa ops sb. compile_log_topic_ops raw sa = (ops,sb) ==>
    LENGTH ops = LENGTH raw
Proof
  Induct_on `raw`
  >- simp[compile_log_topic_ops_def, comp_return_def] >>
  simp[compile_log_topic_ops_cons] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem log_emitted_topic_count_exact:
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sa = (ops,sb) ==>
  LENGTH (h::ops) <= 4 /\
  w2n (n2w (LENGTH (h::ops)) : 256 word) = LENGTH (h::ops)
Proof
  strip_tac >> drule compile_log_topic_ops_length >> strip_tac >>
  drule_all split_log_ops_lengths >> strip_tac >>
  `4 < dimword (:256)` by simp[dimword_def] >> simp[]
QED
