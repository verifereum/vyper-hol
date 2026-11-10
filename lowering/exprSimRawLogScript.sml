(* Common RawLog source/compiler and LOG execution interfaces. *)
Theory exprSimRawLog
Ancestors
  list exprSimDefs exprSimStack loweringPosts exprSimHypsDefs exprSimHyps exprSimPrecompiles exprSimWordArgs exprSimSend exprSimAggregateSource compileEnv loweringStateRelDefs extCallOracleStep allocLimits
  vyperAST vyperTypeSystem vyperInterpreter vyperContext vyperValue vyperState
  vyperEvent venomExecSemantics venomInst venomState venomMemDefs exprLowering exprLoweringProps
  exprSimHash builtinSystem emitHelper fragExec emitHelperProps venomExecProofs
Libs
  pairLib

Theorem raw_log_topic_word:
  value_has_type (BaseTV (BytesT (Fixed 32))) v ==>
  typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) v = event_value_to_word v
Proof
  Cases_on `v` >>
  simp[vyperTypingTheory.value_has_type_def,
       valueEncodingTheory.typed_val_to_w256_def, event_value_to_word_def] >>
  strip_tac >> simp[]
QED

Theorem raw_log_topics_post_words:
  typed_args_post ctx func cenv cx es sa s0 es1 topics ops vs t /\
  EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
  EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs ==>
  eval_operands ops t = SOME (MAP event_value_to_word vs)
Proof
  simp[typed_args_post_def] >> strip_tac >>
  qpat_x_assum `_ ==> pure_frame _ _ _ _ _ _` kall_tac >>
  rpt (pop_assum mp_tac) >>
  map_every qid_spec_tac [`vs`, `ops`, `topics`] >>
  Induct >> rpt gen_tac >> Cases_on `vs` >> Cases_on `ops` >>
  simp[eval_operands_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`t''`, `t'`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[vyperValueTheory.evaluate_type_def, raw_log_topic_word]
QED

Theorem typed_args_ready_success:
  !args es vs es'.
  typed_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
  eval_exprs cx args es = (INL vs,es') ==> Inv es'
Proof
  Induct >- simp[eval_exprs_nil] >> rpt strip_tac >>
  drule_all typed_args_ready_head >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >> first_x_assum irule >>
  metis_tac[typed_args_ready_tail]
QED

Theorem raw_log_eval_operands_words[local]:
  !ops vs. eval_operands ops t = SOME (MAP event_value_to_word vs) ==>
  LIST_REL (\op v. eval_operand op t = SOME (val_to_w256 v)) ops vs
Proof
  Induct >> Cases_on `vs` >>
  simp[eval_operands_def, AllCaseEqs(),
       e2eDefsTheory.event_value_to_word_eq_val_to_w256] >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >> simp[]
QED

Theorem raw_log_topics_post_wb:
  typed_args_post ctx func cenv cx es sa s0 es1 topics ops vs t /\
  EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
  EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs ==>
  wb_args_post ctx func cenv cx es sa s0 es1 ops vs t
Proof
  strip_tac >> drule_all raw_log_topics_post_words >> strip_tac >>
  drule raw_log_eval_operands_words >>
  fs[wb_args_post_def, typed_args_post_def]
QED

Theorem raw_log_state_rel:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx
    (es with logs := es.logs ++ [ev])
    (s with vs_logs := s.vs_logs ++ [ev])
Proof
  strip_tac >>
  gvs[stmt_state_rel_def, state_rel_def, immutable_base_zero_alt, logs_rel_eq,
      local_ptrs_rel_def, local_region_def, local_backed_def,
      storage_rel_def, transient_rel_def, accounts_rel_def,
      immutables_rel_def, immutable_alloca_sep_def,
      alloca_room_def, fmp_room_def, pending_alloca_size_def, alloca_inv_def,
      lookup_var_def, contract_storage_def, contract_transient_def,
      allocas_non_overlapping_def, alloca_next_valid_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem raw_log_core_step:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [sz; pop]) /\
  LENGTH ops < dimword (:256) /\
  eval_operand pop s = SOME off /\ eval_operand sz s = SOME len /\
  eval_operands ops s = SOME topics /\ ~s.vs_call_ctx.cc_static ==>
  step_inst_base inst s =
    OK (s with vs_logs := s.vs_logs ++
      [<| logger := w2w s.vs_call_ctx.cc_address; topics := topics;
          data := TAKE (w2n len)
            (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n len) 0w) |>])
Proof
  strip_tac >>
  simp[step_inst_base_def, rich_listTheory.REVERSE_APPEND,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem raw_log_step:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [sz; pop]) /\
  LENGTH ops <= 4 /\
  eval_operand pop s = SOME off /\ eval_operand sz s = SOME len /\
  eval_operands ops s = SOME topics /\ ~s.vs_call_ctx.cc_static ==>
  step_inst_base inst s =
    OK (s with vs_logs := s.vs_logs ++
      [<| logger := w2w s.vs_call_ctx.cc_address; topics := topics;
          data := TAKE (w2n len)
            (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n len) 0w) |>])
Proof
  strip_tac >> irule raw_log_core_step >> simp[wordsTheory.dimword_def]
QED

Theorem raw_log_wb_frame:
  wb_frame cenv es sa s0 s ==>
  wb_frame cenv es sa s0 (s with vs_logs := logs)
Proof
  simp[wb_frame_def, locals_kept_def, lookup_var_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem raw_log_topics_lowering_bridge:
  !topics.
    compile_multi_exprs compile_expr cenv topics = lower_word_args cenv expr_type topics
Proof
  Induct >> simp[compile_multi_exprs_def, lower_word_args_def, comp_return_def]
QED

Theorem compile_raw_log_stages:
  compile_expr cenv ty
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics; data_e] dflt) sa =
  (let (topic_ops, s1) = lower_word_args cenv expr_type topics sa in
   if expr_type data_e = BaseT (BytesT (Fixed 32)) then
     let (tmp, s2) = compile_alloc_buffer 32 s1 in
     let (v, s3) = lower_value compile_expr cenv (expr_type data_e) data_e s2 in
     let (_, s4) = emit_void MSTORE [tmp.buf_operand; v] s3 in
     let (_, s5) = emit_inst LOG
       (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++
         [Lit 32w; tmp.buf_operand]) [] s4 in
     (StackValue ann (Lit 0w), s5)
   else
     let (data, s2) = lower_value compile_expr cenv (expr_type data_e) data_e s1 in
     let (len, s3) = emit_op MLOAD [data] s2 in
     let (ptr, s4) = emit_op ADD [data; Lit 32w] s3 in
     let (_, s5) = emit_inst LOG
       (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len; ptr]) [] s4 in
     (StackValue ann (Lit 0w), s5))
Proof
  simp[compile_expr_call, compile_call_def, raw_log_topic_exprs_def,
       raw_log_topics_lowering_bridge]
QED

Theorem raw_log_words_step:
  LENGTH ops < dimword (:256) /\
  eval_operands ops s = SOME (MAP event_value_to_word vs) /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  w2w s.vs_call_ctx.cc_address = logger /\
  TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w) = bs /\
  ~s.vs_call_ctx.cc_static ==>
  step_inst_base
    (mk_inst id LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op; ptr_op]) []) s =
  OK (s with vs_logs := s.vs_logs ++ [encode_raw_event_values logger vs bs])
Proof
  strip_tac >>
  `step_inst_base (mk_inst id LOG
    (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op; ptr_op]) []) s =
    OK (s with vs_logs := s.vs_logs ++
      [<| logger := w2w s.vs_call_ctx.cc_address;
          topics := MAP event_value_to_word vs;
          data := TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++
            REPLICATE (w2n sz) 0w) |>])` by
    (irule raw_log_core_step >> simp[mk_inst_def] >>
     qexistsl_tac [`ops`, `ptr_op`, `len_op`] >> simp[]) >>
  gvs[encode_raw_event_values_def, encode_raw_event_def]
QED

Theorem raw_log_literal_eval_cases:
  LENGTH topics <= n /\ eval_exprs cx topics es = (rr, es') ==>
  eval_expr cx
    (Builtin ann (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics)
    es =
    ((case rr of INL vs => INL (Value (ArrayV (DynArrayV vs)))
      | INR exc => INR exc), es')
Proof
  strip_tac >>
  irule (SRULE [make_array_value_def, evaluate_type_def]
    (Q.INST [`bnd` |-> `Dynamic n`, `et` |-> `BaseT (BytesT (Fixed 32))`]
      aggregate_eval_make_array)) >>
  simp[compatible_bound_def]
QED

Theorem raw_log_literal_read_success:
  LENGTH topics <= n /\ eval_exprs cx topics es = (INL vs, es') ==>
  (do tv <- eval_expr cx
       (Builtin ann (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics);
      read_result cx tv od) es = (INL (ArrayV (DynArrayV vs)), es')
Proof
  strip_tac >> drule_all raw_log_literal_eval_cases >>
  simp[bind_def, read_result_def, return_def]
QED

Theorem raw_log_eval_exprs_cons[local]:
  eval_exprs cx (e::args) =
  do tv <- eval_expr cx e;
     v <- read_result cx tv;
     vs <- eval_exprs cx args;
     return (v::vs)
  od
Proof
  simp[Once evaluate_def]
QED

Theorem raw_log_source_eval:
  LENGTH topics <= n /\ ~cx.txn.is_static ==>
  eval_expr cx
    (Call ann RawLog
      [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
       data] dflt) es =
  (do vs <- eval_exprs cx topics;
      dv <- (do tv <- eval_expr cx data; read_result cx tv od);
      bs <- lift_option_type (dest_BytesV dv) "raw_log data";
      type_check (LENGTH vs <= 4) "raw_log too many topics";
      push_log (encode_raw_event_values cx.txn.target vs bs);
      return (Value NoneV)
   od) es
Proof
  strip_tac >>
  Cases_on `eval_exprs cx topics es` >>
  rename1 `eval_exprs cx topics es = (rr, es1)` >>
  drule_all raw_log_literal_eval_cases >> strip_tac >>
  simp[Once evaluate_def] >>
  simp[raw_log_eval_exprs_cons, exprSimWordArgsTheory.eval_exprs_nil,
       bind_def, ignore_bind_def, read_result_def, return_def,
       type_check_def, assert_def, lift_option_type_def, dest_ArrayV_def] >>
  Cases_on `rr` >> simp[bind_def, read_result_def, return_def] >>
  Cases_on `eval_expr cx data es1` >> rename1 `eval_expr cx data es1 = (dr, ds)` >>
  Cases_on `dr` >> simp[] >>
  rename1 `read_result cx tv ds` >>
  Cases_on `read_result cx tv ds` >> rename1 `read_result cx tv ds = (vr, ds')` >>
  Cases_on `vr` >>
  simp[dest_ArrayV_def, lift_option_type_def, return_def, bind_def]
QED

Theorem raw_log_dynamic_data_view:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mload b s = n2w (LENGTH bs) /\
    TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++
      REPLICATE (LENGTH bs) 0w) = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256)
Proof
  strip_tac >> drule hash_dynamic_post_view >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  qexists_tac `b` >>
  fs[venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def,
     valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem raw_log_dynamic_prepare_run:
  emit_op MLOAD [data_op] sa = (len_op, sm) /\
  emit_op ADD [data_op; Lit 32w] sm = (ptr_op, sb) /\
  (!x. data_op = Var x ==> not_fresh_at sa x) /\
  eval_operand data_op s = SOME (n2w b) /\
  mload b s = n2w (LENGTH bs) /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
    eval_operand ptr_op t = SOME (n2w (b + 32)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `mem_word_at b s.vs_memory = n2w (LENGTH bs)` by
    gvs[venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def] >>
  `b < dimword (:256)` by decide_tac >>
  drule_all hash_data_prefix_run >> metis_tac[]
QED

Theorem raw_log_mstore_frame:
  wb_frame cenv es0 sa s0 s /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!aid b sz. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint a 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint a 32 b sz) ==>
  wb_frame cenv es0 sa s0 (mstore a w s)
Proof
  strip_tac >> irule wb_frame_allocating_tail >> simp[] >>
  qexistsl_tac [`s`, `es.scopes`, `sa`] >>
  `(!x. lookup_var x (mstore a w s) = lookup_var x s) /\
   (mstore a w s).vs_allocas = s.vs_allocas` by
    simp[venomStateTheory.mstore_def, lookup_var_def] >>
  simp[] >> rpt strip_tac >> irule mstore_region_frame >>
  qexistsl_tac [`a`, `32`] >> simp[] >> metis_tac[]
QED

Theorem raw_log_operands_readonly:
  !ops. EVERY (\op. !x. op = Var x ==> not_fresh_at sa x) ops /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  eval_operands ops t = eval_operands ops s
Proof
  Induct >- simp[eval_operands_def] >>
  gen_tac >> simp[eval_operands_def] >> strip_tac >>
  `eval_operand h t = eval_operand h s` by
    (Cases_on `h` >> gvs[eval_operand_def] >>
     qpat_x_assum `_ with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  simp[]
QED

Theorem raw_log_dynamic_prepare_frame:
  emit_op MLOAD [data_op] sm = (len_op, s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op, sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME topics /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++
    REPLICATE (LENGTH bs) 0w) = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 sa s0 s /\ sa.cs_next_var <= sm.cs_next_var ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
    eval_operand ptr_op t = SOME (n2w (b + 32)) /\
    eval_operands ops t = SOME topics /\
    TAKE (LENGTH bs) (DROP (b + 32) t.vs_memory ++
      REPLICATE (LENGTH bs) 0w) = bs /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 sa s0 t
Proof
  strip_tac >> drule_all raw_log_dynamic_prepare_run >> strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_memory, z.vs_allocas)`) >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  `eval_operands ops t = eval_operands ops s` by
    (irule raw_log_operands_readonly >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule hash_readonly_state_rel >> metis_tac[]) >>
  irule wb_frame_readonly_tail >>
  qexistsl_tac [`sm`, `s`] >> simp[]
QED

Theorem raw_log_core_frame:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [sz; pop]) /\ LENGTH ops < dimword (:256) /\
  eval_operand pop s = SOME off /\ eval_operand sz s = SOME len /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  TAKE (w2n len) (DROP (w2n off) s.vs_memory ++
    REPLICATE (w2n len) 0w) = bytes /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s ==>
  ?t. step_inst_base inst s = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bytes]) t /\
    wb_frame cenv es0 sa s0 t
Proof
  strip_tac >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all raw_log_core_step >>
  disch_then SUBST1_TAC >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  simp[encode_raw_event_values_def, encode_raw_event_def] >>
  conj_tac >- (irule raw_log_state_rel >> simp[]) >>
  irule raw_log_wb_frame >> simp[]
QED

Theorem raw_log_dynamic_tail_core:
  expr_has_effect e /\
  emit_op MLOAD [data_op] sm = (len_op, s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op, s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [len_op; ptr_op])) [] s2 = (u, sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\
  LENGTH ops < dimword (:256) /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++
    REPLICATE (LENGTH bs) 0w) = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  frag_exec ctx sm sb ($= s)
    (expr_post ctx func cenv cx e es0 sa sb s0
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w))
    (expr_exit (INL NoneV))
Proof
  strip_tac >> drule_all raw_log_dynamic_prepare_frame >> strip_tac >>
  `sb.cs_blocks = sm.cs_blocks /\ sb.cs_current_bb = sm.cs_current_bb /\
   s2.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm s2 /\
   sb.cs_current_insts = s2.cs_current_insts ++
    [mk_inst s2.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: (REVERSE ops ++ [len_op; ptr_op])) []]` by
    gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        fresh_var_def, fresh_id_def, emit_def, comp_return_def,
        emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `emitted_insts sm sb = emitted_insts sm s2 ++
    [mk_inst s2.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: (REVERSE ops ++ [len_op; ptr_op])) []]` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `s2.cs_current_insts = _` SUBST1_TAC >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_APPEND1,
          rich_listTheory.DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm s2)` by
    (qpat_x_assum `s2.cs_current_insts = _` kall_tac >>
     qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
     qpat_x_assum `emitted_insts sm sb = _` kall_tac >>
     gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, comp_return_def,
         emitted_insts_def] >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  irule frag_exec_run_inst_seq >>
  simp[rich_listTheory.IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  drule run_inst_seq_append >> disch_then (fn th => rewrite_tac[th]) >>
  `?t'. step_inst_base (mk_inst s2.cs_next_id LOG
     (Lit (n2w (LENGTH ops)) :: (REVERSE ops ++ [len_op; ptr_op])) []) t = OK t' /\
    stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) t' /\
    wb_frame cenv es0 sa s0 t'` by
    (irule raw_log_core_frame >>
     simp[mk_inst_def] >>
     qexistsl_tac [`ops`, `len_op`, `ptr_op`,
                  `n2w (b + 32)`, `n2w (LENGTH bs)`] >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  fs[mk_inst_def, run_inst_seq_def] >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  fs[wb_frame_def, locals_kept_def, lookup_var_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem raw_log_fixed_store_run:
  emit_void MSTORE [ptr_op; data_op] sm = (u, sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs ==>
  run_inst_seq (emitted_insts sm sb) s = OK (mstore (w2n p) w s) /\
  TAKE 32 (DROP (w2n p) (mstore (w2n p) w s).vs_memory ++
    REPLICATE 32 0w) = bs
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
           fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
      simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
           run_inst_seq_def, step_inst_base_def, mk_inst_def,
           exec_write2_def]) >>
  `mem_bytes_at (w2n p) (LENGTH bs) (mstore (w2n p) w s).vs_memory = bs` by
    (irule hash_mstore_prefix >> simp[]) >>
  gvs[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem raw_log_fixed_store_frame:
  emit_void MSTORE [ptr_op; data_op] sm = (u, sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz) ==>
  run_inst_seq (emitted_insts sm sb) s = OK (mstore (w2n p) w s) /\
  TAKE 32 (DROP (w2n p) (mstore (w2n p) w s).vs_memory ++
    REPLICATE 32 0w) = bs /\
  stmt_state_rel ctx func cenv cx es (mstore (w2n p) w s) /\
  wb_frame cenv es0 sa s0 (mstore (w2n p) w s)
Proof
  strip_tac >> drule_all raw_log_fixed_store_run >> strip_tac >> simp[] >>
  conj_tac
  >- (irule exprSimAllocTheory.literal_mstore_state_rel >>
      simp[] >> qexistsl_tac [`w2n p`, `inst`, `32`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule raw_log_mstore_frame >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `es` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem raw_log_fixed_tail_core:
  expr_has_effect e /\
  emit_void MSTORE [ptr_op; data_op] sm = (u, s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [Lit 32w; ptr_op])) [] s1 = (u', sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  LENGTH ops < dimword (:256) /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz) /\ post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  frag_exec ctx sm sb ($= s)
    (expr_post ctx func cenv cx e es0 sa sb s0
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w))
    (expr_exit (INL NoneV))
Proof
  strip_tac >> drule_all raw_log_fixed_store_frame >> strip_tac >>
  `sb.cs_blocks = sm.cs_blocks /\ sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
    [mk_inst sm.cs_next_id MSTORE [ptr_op; data_op] [];
     mk_inst s1.cs_next_id LOG (Lit (n2w (LENGTH ops)) ::
       (REVERSE ops ++ [Lit 32w; ptr_op])) []]` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
        fresh_id_def, emit_def] >>
  `emitted_insts sm sb =
    [mk_inst sm.cs_next_id MSTORE [ptr_op; data_op] [];
     mk_inst s1.cs_next_id LOG (Lit (n2w (LENGTH ops)) ::
       (REVERSE ops ++ [Lit 32w; ptr_op])) []]` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `eval_operand ptr_op (mstore (w2n p) w s) = SOME p /\
   eval_operands ops (mstore (w2n p) w s) = SOME (MAP event_value_to_word vals)` by
    (`eval_operands ops (mstore (w2n p) w s) = eval_operands ops s` by
       (rpt (pop_assum kall_tac) >> Induct_on `ops` >>
        simp[eval_operands_def] >>
        Cases_on `h` >> simp[eval_operand_def, mstore_def, lookup_var_def]) >>
     simp[] >> Cases_on `ptr_op` >>
     gvs[eval_operand_def, mstore_def, lookup_var_def]) >>
  irule frag_exec_run_inst_seq >>
  simp[rich_listTheory.IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  `?t. step_inst_base (mk_inst s1.cs_next_id LOG
      (Lit (n2w (LENGTH ops)) :: (REVERSE ops ++ [Lit 32w; ptr_op])) [])
      (mstore (w2n p) w s) = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) t /\
    wb_frame cenv es0 sa s0 t` by
    (irule raw_log_core_frame >> simp[mk_inst_def] >>
     qexists_tac `32w` >> simp[eval_operand_def, wordsTheory.dimword_def]) >>
  fs[mk_inst_def] >>
  simp[run_inst_seq_def, Once step_inst_base_def, exec_write2_def] >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  fs[wb_frame_def, locals_kept_def, lookup_var_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
