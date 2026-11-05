(*
 * The piece of exprSimCalls's compile_raw_log_sim: raw_log (#636).
 * raw_log_expr_vv_ok is compile_raw_log_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallRawLog
Ancestors
  list exprSimDefs exprSimStack loweringPosts exprSimHypsDefs exprSimSource exprSimHyps exprSimSend vyperAST vyperTypeSystem
  vyperTypeCallGraph allocLimits supportedExprTraverse exprLowering
  vyperInterpreter vyperContext vyperValue vyperState exprCallbackContracts exprCallBounds
  vyperTypeExprSoundness exprSimWordArgs exprSimPrecompiles compileEnv
  vyperEvent venomExecSemantics venomInst venomState exprLoweringProps
  extCallOracleStep venomMemDefs exprSimHash builtinSystem emitHelper fragExec
  emitHelperProps venomExecProofs exprSimOperators exprSimRawLog exprSimRawLogSimCompose
Libs
  pairLib

Theorem raw_log_typed_shape[local]:
  well_typed_expr env (Call ann RawLog args dflt) ==>
  ?topics data n.
    ann = NoneT /\ dflt = NONE /\ n <= 4 /\
    args = [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
                    (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
            data] /\
    LENGTH topics <= 4 /\ compatible_bound (Dynamic n) (LENGTH topics) /\
    well_typed_exprs env topics /\ well_typed_expr env data /\
    EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
    (expr_type data = BaseT (BytesT (Fixed 32)) \/
     ?m. expr_type data = BaseT (BytesT (Dynamic m)))
Proof
  Cases_on `args` >> simp[well_typed_expr_def] >>
  Cases_on `t` >> simp[well_typed_expr_def] >>
  Cases_on `t'` >> simp[well_typed_expr_def] >>
  Cases_on `h` >> simp[] >>
  rename1 `Builtin topic_ann blt topics` >>
  Cases_on `blt` >> simp[] >>
  rename1 `MakeArray elem_ty bnd` >>
  Cases_on `elem_ty` >>
  simp[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raw_log_child_pre[local]:
  expr_sim_pre cenv cx env (Call ann RawLog args dflt) es /\
  MEM e args /\ expr_sim_inv cenv cx env es' ==>
  expr_sim_pre cenv cx env e es'
Proof
  rw[expr_sim_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def, expr_has_evm_run_thm,
     supported_expr_exists_def] >>
  drule_all well_typed_exprs_mem >> drule_all byte_widths_exprs_mem >>
  drule_all alloc_limits_exprs_mem >>
  gvs[expr_has_evm_run_thm, supported_exprs_exists_every, EVERY_MEM, EXISTS_MEM] >>
  metis_tac[int_calls_exprs_mem]
QED

Theorem raw_log_topic_pre[local]:
  expr_sim_pre cenv cx env
    (Call ann RawLog [Builtin topic_ann (MakeArray elem_ty bnd) topics; data] dflt) es /\
  MEM e topics /\ expr_sim_inv cenv cx env es' ==>
  expr_sim_pre cenv cx env e es'
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env
     (Builtin topic_ann (MakeArray elem_ty bnd) topics) es'` by
    (irule raw_log_child_pre >> simp[] >>
     qexistsl [`ann`, `[Builtin topic_ann (MakeArray elem_ty bnd) topics; data]`,
               `dflt`, `es`] >> simp[]) >>
  drule expr_sim_pre_builtin_arg >> disch_then irule >> simp[]
QED

Theorem raw_log_topic_size[local]:
  MEM e topics ==>
  expr_size e < expr_size
    (Call ann RawLog [Builtin topic_ann (MakeArray elem_ty bnd) topics; data] dflt)
Proof
  strip_tac >> drule expr_list_member_bound >> simp[expr_size_def]
QED

Theorem compile_expr_raw_log_shape[local]:
  compile_expr cenv ty
    (Call NoneT RawLog
      [Builtin topic_ann (MakeArray elem_ty bnd) topics; data] NONE) st =
  (let (topic_ops, st1) = compile_multi_exprs compile_expr cenv topics st in
   if expr_type data = BaseT (BytesT (Fixed 32)) then
     let (tmp, st2) = compile_alloc_buffer 32 st1 in
     let (v, st3) = lower_value compile_expr cenv (expr_type data) data st2 in
     let (_, st4) = emit_void MSTORE [tmp.buf_operand; v] st3 in
     let (_, st5) = emit_inst LOG
       (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++
        [Lit 32w; tmp.buf_operand]) [] st4 in
     (StackValue NoneT (Lit 0w), st5)
   else
     let (v, st2) = lower_value compile_expr cenv (expr_type data) data st1 in
     let (data_len, st3) = emit_op MLOAD [v] st2 in
     let (data_ptr, st4) = emit_op ADD [v; Lit 32w] st3 in
     let (_, st5) = emit_inst LOG
       (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++
        [data_len; data_ptr]) [] st4 in
     (StackValue NoneT (Lit 0w), st5))
Proof
  simp[compile_raw_log_stages, raw_log_topics_lowering_bridge]
QED

Theorem raw_log_topics_eval[local]:
  compatible_bound (Dynamic n) (LENGTH topics) ==>
  eval_expr cx
    (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
      (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics) =
  do vs <- eval_exprs cx topics;
     return (Value (ArrayV (DynArrayV vs))) od
Proof
  simp[compatible_bound_def] >> strip_tac >>
  simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx topics x` >>
  drule_all raw_log_literal_eval_cases >>
  simp[bind_def, return_def] >>
  Cases_on `q` >> simp[]
QED

Theorem raw_log_eval[local]:
  ~cx.txn.is_static /\ compatible_bound (Dynamic n) (LENGTH topics) ==>
  vyperState$bind (eval_expr cx
        (Call ann RawLog
          [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
             (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
           data] dflt)) (read_result cx) =
  do vs <- eval_exprs cx topics;
     r <- eval_expr cx data;
     v <- read_result cx r;
     bs <- lift_option_type (dest_BytesV v) "raw_log data";
     type_check (LENGTH vs <= 4) "raw_log too many topics";
     push_log (encode_raw_event_values cx.txn.target vs bs);
     return NoneV od
Proof
  simp[compatible_bound_def] >> strip_tac >>
  simp[FUN_EQ_THM] >> gen_tac >>
  simp[bind_def, raw_log_source_eval] >>
  Cases_on `eval_exprs cx topics x` >>
  rename1 `eval_exprs cx topics x = (rr, st1)` >> Cases_on `rr` >>
  simp[bind_def, ignore_bind_def, return_def, read_result_def] >>
  Cases_on `eval_expr cx data st1` >>
  rename1 `eval_expr cx data st1 = (dr, st2)` >> Cases_on `dr` >> simp[] >>
  rename1 `read_result cx tv st2` >>
  Cases_on `read_result cx tv st2` >>
  rename1 `read_result cx tv st2 = (vr, st3)` >> Cases_on `vr` >> simp[] >>
  simp[type_check_def, assert_def, return_def, dest_ArrayV_def,
       lift_option_type_def, lift_option_def, bind_def, read_result_def] >>
  rename1 `dest_BytesV dv` >> Cases_on `dest_BytesV dv` >>
  simp[raise_def, return_def, bind_def, ignore_bind_def, read_result_def] >>
  Cases_on `LENGTH x' <= 4` >>
  simp[raise_def, return_def, bind_def, ignore_bind_def, read_result_def]
QED

Theorem raw_log_eval_cases[local]:
  ~cx.txn.is_static /\ compatible_bound (Dynamic n) (LENGTH topics) /\ LENGTH topics <= 4 /\
  expr_sim_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
         (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
       data] dflt) es /\
  (do r <- eval_expr cx
        (Call ann RawLog
          [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
             (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
           data] dflt);
      read_result cx r od) es = (res, es') ==>
  (?exc. eval_exprs cx topics es = (INR exc, es') /\ res = INR exc) \/
  (?vs es1 exc.
     eval_exprs cx topics es = (INL vs, es1) /\
     (do r <- eval_expr cx data; read_result cx r od) es1 = (INR exc, es') /\
     res = INR exc) \/
  (?vs es1 bs es2.
     eval_exprs cx topics es = (INL vs, es1) /\
     (do r <- eval_expr cx data; read_result cx r od) es1 = (INL (BytesV bs), es2) /\
     res = INL NoneV /\
     es' = es2 with logs := es2.logs ++
       [encode_raw_event_values cx.txn.target vs bs])
Proof
  strip_tac >>
  `no_type_error_result res` by
    (drule_all expr_sim_pre_eval >> simp[]) >>
  qpat_x_assum `expr_sim_pre _ _ _ _ _` kall_tac >>
  qpat_x_assum `bind _ _ es = _` mp_tac >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[raw_log_eval] >>
  Cases_on `eval_exprs cx topics es` >>
  rename1 `eval_exprs cx topics es = (tr, es1)` >> Cases_on `tr`
  >- (rename1 `eval_exprs cx topics es = (INL vs, es1)` >>
      `LENGTH vs <= 4` by (drule eval_exprs_length >> simp[]) >>
      simp[bind_def] >> Cases_on `eval_expr cx data es1` >>
      rename1 `eval_expr cx data es1 = (dr, es2)` >> Cases_on `dr` >> simp[]
      >- (rename1 `read_result cx tv es2` >>
          Cases_on `read_result cx tv es2` >>
          rename1 `read_result cx tv es2 = (vr, es3)` >> Cases_on `vr` >> simp[]
          >- (rename1 `dest_BytesV v` >> Cases_on `v` >>
              simp[dest_BytesV_def, lift_option_type_def, lift_option_def,
                   type_check_def, assert_def, raise_def, return_def,
                   bind_def, ignore_bind_def, push_log_def] >>
              strip_tac >> gvs[no_type_error_result_def] >> metis_tac[]) >>
          metis_tac[]) >>
      metis_tac[]) >>
  simp[bind_def] >> metis_tac[]
QED

Theorem raw_log_eval_value[local]:
  eval_expr cx (Call ann RawLog args dflt) es = (INL tv, es') ==>
  tv = Value NoneV
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       type_check_def, assert_def, raise_def, lift_option_type_def,
       lift_option_def, push_log_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem raw_log_raw_eval_cases[local]:
  ~cx.txn.is_static /\ compatible_bound (Dynamic n) (LENGTH topics) /\ LENGTH topics <= 4 /\
  expr_sim_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
         (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
       data] dflt) es /\
  eval_expr cx
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
         (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
       data] dflt) es = (res, es') ==>
  (?exc. eval_exprs cx topics es = (INR exc, es') /\ res = INR exc) \/
  (?vs es1 exc.
     eval_exprs cx topics es = (INL vs, es1) /\
     (do r <- eval_expr cx data; read_result cx r od) es1 = (INR exc, es') /\
     res = INR exc) \/
  (?vs es1 bs es2.
     eval_exprs cx topics es = (INL vs, es1) /\
     (do r <- eval_expr cx data; read_result cx r od) es1 = (INL (BytesV bs), es2) /\
     res = INL (Value NoneV) /\
     es' = es2 with logs := es2.logs ++
       [encode_raw_event_values cx.txn.target vs bs])
Proof
  strip_tac >> Cases_on `res` >>
  imp_res_tac raw_log_eval_value >> gvs[] >>
  drule_at (Pat `expr_sim_pre _ _ _ _ _`) raw_log_eval_cases >>
  simp[bind_def, read_result_def, return_def] >>
  metis_tac[]
QED

Theorem raw_log_topics_source[local]:
  expr_sim_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] dflt) es /\
  compatible_bound (Dynamic n) (LENGTH topics) /\
  eval_exprs cx topics es = (INL vs,es1) ==>
  expr_sim_pre cenv cx env data es1 /\
  EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env
     (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
       (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics) es` by
    (irule raw_log_child_pre >>
     conj_tac >- gvs[expr_sim_pre_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_expr cx
     (Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
       (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics) es =
     (INL (Value (ArrayV (DynArrayV vs))), es1)` by
    simp[raw_log_topics_eval, bind_def, return_def] >>
  drule_all expr_sim_pre_eval_result >> strip_tac >>
  conj_tac
  >- (irule raw_log_child_pre >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[expr_type_def, vyperValueTheory.evaluate_type_def,
      vyperTypeInvariantsTheory.eval_result_typed_def, vyperTypingTheory.value_has_type_def] >>
  gvs[vyperTypingTheory.all_have_type_EVERY]
QED

Theorem raw_log_topics_marked_source[local]:
  expr_sim_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] dflt) es /\
  compatible_bound (Dynamic n) (LENGTH topics) /\
  gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s0)
    marks (INL vs) mid (OK t) ==>
  expr_sim_pre cenv cx env data (mid with gas_obs := []) /\
  EVERY (value_has_type (BaseTV (BytesT (Fixed 32)))) vs
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env
    (Call ann RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] dflt)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    gvs[expr_sim_pre_def] >>
  `eval_exprs cx topics
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all raw_log_topics_source >> simp[]
QED

Theorem raw_log_data_sim[local]:
  expr_sim_below cenv (expr_size (Call ann RawLog [topic; data] dflt)) /\
  expr_sim_pre cenv cx env data es1 ==>
  expr_sim ctx func cenv cx (expr_type data) data es1
Proof
  simp[expr_size_def, expr_sim_below_def] >> strip_tac >>
  first_x_assum (qspec_then `data` mp_tac) >>
  simp[expr_ok_def, expr_sim_ok_def] >> metis_tac[]
QED

Theorem raw_log_post_vv[local]:
  expr_post ctx func cenv cx e es sa sb s0 es' NoneV (Lit 0w) s ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value NoneV)
    (StackValue NoneT (Lit 0w)) s
Proof
  simp[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
       read_result_def, return_def] >> metis_tac[]
QED

Theorem compile_multi_exprs_lower_word_args[local]:
  !topics. compile_multi_exprs compile_expr cenv topics =
           lower_word_args cenv expr_type topics
Proof
  Induct >> simp[compile_multi_exprs_def, lower_word_args_def]
QED

Theorem raw_log_topics_ready[local]:
  expr_sim_below cenv (expr_size
    (Call ann RawLog [Builtin topic_ann (MakeArray elem_ty bnd) topics; data] dflt)) /\
  expr_sim_pre cenv cx env
    (Call ann RawLog [Builtin topic_ann (MakeArray elem_ty bnd) topics; data] dflt) es /\
  EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) ==>
  typed_args_ready ctx func cenv cx expr_type
    (expr_sim_inv cenv cx env) topics /\
  wb_args_shape cenv expr_type topics
Proof
  strip_tac >> irule typed_stack_args_ready >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[raw_log_topic_pre]) >>
  reverse conj_tac
  >- (qexists `es` >> gvs[expr_sim_pre_def]) >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  `expr_type e = BaseT (BytesT (Fixed 32))` by metis_tac[] >>
  simp[is_word_type_def] >>
  `expr_size e < expr_size
    (Call ann RawLog [Builtin topic_ann (MakeArray elem_ty bnd) topics; data] dflt)` by
    (irule raw_log_topic_size >> simp[]) >>
  gvs[expr_sim_below_def, expr_ok_def] >> metis_tac[]
QED

Theorem raw_log_topics_sim[local]:
  expr_sim_below cenv (expr_size
    (Call ann RawLog [Builtin topic_ann (MakeArray elem_ty bnd) topics; data] dflt)) /\
  expr_sim_pre cenv cx env
    (Call ann RawLog [Builtin topic_ann (MakeArray elem_ty bnd) topics; data] dflt) es /\
  EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
  compile_multi_exprs compile_expr cenv topics sa = (ops, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx topics) (es,s0)
    (\rr ee t. ?vs. rr = INL vs /\
       typed_args_post ctx func cenv cx es sa s0 ee topics ops vs t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all raw_log_topics_ready >> strip_tac >>
  irule lower_typed_args_sim >> simp[] >>
  qexistsl [`expr_sim_inv cenv cx env`, `expr_type`] >>
  gvs[compile_multi_exprs_lower_word_args, expr_sim_pre_def] >>
  metis_tac[expr_sim_inv_gas_obs]
QED

Theorem raw_log_operands_frame[local]:
  !ops ws.
  eval_operands ops s = SOME ws /\
  EVERY (\op. (!p. op = Var p ==> not_fresh_at sa p) /\
              (!l. op <> Label l)) ops /\
  (!p w. not_fresh_at sa p /\ lookup_var p s = SOME w ==>
    lookup_var p t = SOME w) ==>
  eval_operands ops t = SOME ws
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all exprBopSimPropsTheory.eval_operand_frame >> strip_tac >>
  simp[] >> first_x_assum irule >> simp[]
QED

Theorem raw_log_post_rebase[local]:
  expr_post ctx func cenv cx e es1 s1 sb t es2 v op u /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  wb_frame cenv es sa s0 t ==>
  expr_post ctx func cenv cx e es sa sb s0 es2 v op u
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 u` by
    (irule wb_frame_trans >> goal_assum (drule_at Any) >>
     metis_tac[expr_post_frame]) >>
  gvs[expr_post_def, wb_frame_def] >>
  metis_tac[exprSimPropsTheory.expr_val_at_start_mono]
QED

Theorem raw_log_post_operands[local]:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
  eval_operands ops s0 = SOME ws /\
  EVERY (\op. (!p. op = Var p ==> not_fresh_at sa p) /\
              (!l. op <> Label l)) ops ==>
  eval_operands ops s = SOME ws
Proof
  strip_tac >> irule raw_log_operands_frame >>
  qexistsl [`s0`, `sa`] >> simp[] >>
  gvs[expr_post_def]
QED

Theorem raw_log_scratch_transport[local]:
  expr_post ctx func cenv cx e es sa sm s0 es' v op s /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  FLOOKUP s0.vs_allocas aid = SOME (b,32) /\
  not_fresh_at sa p /\ lookup_var p s0 = SOME (n2w b) /\
  (!name lb len. local_region cenv es.scopes s0 name lb len ==>
    b + 32 <= lb \/ lb + len <= b) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,32) /\
  lookup_var p s = SOME (n2w b) /\
  (!name lb len. local_region cenv es'.scopes s name lb len ==>
    b + 32 <= lb \/ lb + len <= b)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  gvs[expr_post_def] >> rpt strip_tac >>
  `local_region cenv es.scopes s0 name lb len` by
    (irule exprSimPropsTheory.local_region_frame >>
     conj_tac >- (qexists `func` >> simp[]) >>
     qexistsl [`sa`, `es'.scopes`, `s`] >> simp[]) >>
  metis_tac[]
QED

Theorem raw_log_dynamic_tail_summary[local]:
  expr_post ctx func cenv cx data es sa sd s0 es2 (BytesV bs) ptr_op s /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type data) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  emit_op MLOAD [ptr_op] sd = (len_op, sl) /\
  emit_op ADD [ptr_op; Lit 32w] sl = (data_op, sm) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;data_op]) []
    sm = (u,sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sd x) /\
  EVERY (\op. (!p. op = Var p ==> not_fresh_at sd p) /\
              (!l. op <> Label l)) ops /\
  eval_operands ops s = SOME (MAP event_value_to_word vs) /\
  LENGTH ops < dimword (:256) /\ local_ptrs_reserved cenv sd /\
  sa.cs_next_var <= sd.cs_next_var /\ expr_type e = NoneT /\
  fn_has_code sd sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sd.cs_current_bb /\
  s.vs_inst_idx = LENGTH sd.cs_current_insts /\ LENGTH vs <= 4 ==>
  gas_summary_at F (ctx,func) []
    (do bytes <- lift_option_type (dest_BytesV (BytesV bs)) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vs bytes);
        return NoneV od) (es2,s)
    (\rr ee t. ?v. rr = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts) (\rr ee r. expr_exit rr r)
Proof
  strip_tac >> drule_all raw_log_dynamic_data_view >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es2 s /\ wb_frame cenv es sa s0 s` by
    metis_tac[expr_post_state, expr_post_frame] >>
  `EVERY (\op. !p. op = Var p ==> not_fresh_at sd p) ops` by
    gvs[EVERY_CONJ] >>
  drule_all raw_log_dynamic_prepare_frame >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emit_inst LOG logops [] sm` >>
  `?t'. step_inst_base (mk_inst sm.cs_next_id LOG logops []) t = OK t' /\
    stmt_state_rel ctx func cenv cx
      (es2 with logs := es2.logs ++ [encode_raw_event_values cx.txn.target vs bs]) t' /\
    wb_frame cenv es sa s0 t'` by
    (irule raw_log_core_frame >> simp[mk_inst_def, Abbr `logops`] >>
     qexistsl_tac [`ops`, `len_op`, `data_op`,
                  `n2w (b + 32)`, `n2w (LENGTH bs)`] >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `sb.cs_current_bb = sd.cs_current_bb /\
   sb.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd sb /\
   emitted_insts sd sb = emitted_insts sd sm ++ [mk_inst sm.cs_next_id LOG logops []] /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sd sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sd sb) = []` by
    (gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, comp_return_def, emitted_insts_def] >>
     CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
     simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts sd sb) s = OK t'` by
    (asm_rewrite_tac[] >> drule run_inst_seq_append >>
     disch_then (fn th => rewrite_tac[th]) >> simp[run_inst_seq_def]) >>
  drule_all hash_run_path >> simp[] >> strip_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def, gasSummaryTheory.gas_marked_exec_def] >>
  qexistsl_tac [`INL NoneV`,
    `es2 with logs := es2.logs ++ [encode_raw_event_values cx.txn.target vs bs]`,
    `OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[dest_BytesV_def, lift_option_type_def, lift_option_def, type_check_def,
       assert_def, push_log_def, bind_def, ignore_bind_def, return_def] >>
  irule expr_post_none_intro >>
  simp[stmt_state_rel_inst_idx, stmt_state_rel_gas_obs] >>
  gvs[wb_frame_def, locals_kept_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) t'` mp_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx ee t'` >>
  `es2 with <|logs := es2.logs ++ [encode_raw_event_values cx.txn.target vs bs];
              gas_obs := []|> = ee with gas_obs := []` by simp[Abbr `ee`] >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem raw_log_fixed_tail_summary[local]:
  expr_post ctx func cenv cx data es sa sd s0 es2 (BytesV bs) val_op s /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  value_has_type (BaseTV (BytesT (Fixed 32))) (BytesV bs) /\
  emit_void MSTORE [ptr_op;val_op] sd = ((),sm) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;ptr_op]) []
    sm = (u,sb) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,32) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= inst.inst_id /\
  (!name lb len. local_region cenv es2.scopes s name lb len ==>
    b + 32 <= lb \/ lb + len <= b) /\
  MAP FDOM es.scopes = MAP FDOM es2.scopes /\ local_ptrs_reserved cenv sa /\
  eval_operands ops s = SOME (MAP event_value_to_word vs) /\
  LENGTH ops < dimword (:256) /\ expr_type e = NoneT /\
  fn_has_code sd sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sd.cs_current_bb /\
  s.vs_inst_idx = LENGTH sd.cs_current_insts /\ LENGTH vs <= 4 ==>
  gas_summary_at F (ctx,func) []
    (do bytes <- lift_option_type (dest_BytesV (BytesV bs)) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target vs bytes);
        return NoneV od) (es2,s)
    (\rr ee t. ?v. rr = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts) (\rr ee r. expr_exit rr r)
Proof
  strip_tac >> drule hash_fixed_post_view >> simp[] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es2 s /\ wb_frame cenv es sa s0 s` by
    metis_tac[expr_post_state, expr_post_frame] >>
  `b + 32 < dimword (:256)` by
    (irule hash_live_footprint_bound >>
     qpat_assum `stmt_state_rel _ _ _ _ _ s` (irule_at Any) >>
     disj1_tac >> qexistsl [`inst.inst_id`, `b`, `32`] >> simp[]) >>
  `!aid b' sz. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b',sz) ==>
      regions_disjoint b 32 b' sz` by
    (rpt strip_tac >> `aid <> inst.inst_id` by decide_tac >>
     drule_all exprSimPrecompilesTheory.state_allocations_disjoint >>
     simp[compileEnvTheory.regions_disjoint_def]) >>
  `!name lb len. local_region cenv es2.scopes s name lb len ==>
     regions_disjoint b 32 lb len` by
    (simp[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  `w2n (n2w b : bytes32) = b` by
    (`b < dimword (:256)` by decide_tac >> simp[wordsTheory.w2n_n2w]) >>
  `run_inst_seq (emitted_insts sd sm) s = OK (mstore (w2n (n2w b : bytes32)) w s) /\
   TAKE 32 (DROP (w2n (n2w b : bytes32)) (mstore (w2n (n2w b : bytes32)) w s).vs_memory ++ REPLICATE 32 0w) = bs /\
   stmt_state_rel ctx func cenv cx es2 (mstore (w2n (n2w b : bytes32)) w s) /\
   wb_frame cenv es sa s0 (mstore (w2n (n2w b : bytes32)) w s)` by
    (irule raw_log_fixed_store_frame >> simp[] >>
     metis_tac[]) >>
  `eval_operand ptr_op (mstore b w s) = SOME (n2w b) /\
   eval_operands ops (mstore b w s) = SOME (MAP event_value_to_word vs)` by
    (`eval_operands ops (mstore b w s) = eval_operands ops s` by
       (rpt (pop_assum kall_tac) >> Induct_on `ops` >>
        simp[eval_operands_def] >> Cases_on `h` >>
        simp[eval_operand_def, mstore_def, lookup_var_def]) >>
     simp[] >> Cases_on `ptr_op` >>
     gvs[eval_operand_def, mstore_def, lookup_var_def]) >>
  qmatch_asmsub_abbrev_tac `emit_inst LOG logops [] sm` >>
  `?t. step_inst_base (mk_inst sm.cs_next_id LOG logops []) (mstore b w s) = OK t /\
    stmt_state_rel ctx func cenv cx
      (es2 with logs := es2.logs ++ [encode_raw_event_values cx.txn.target vs bs]) t /\
    wb_frame cenv es sa s0 t` by
    (irule raw_log_core_frame >> simp[mk_inst_def, Abbr `logops`] >>
     simp[eval_operand_def, wordsTheory.dimword_def] >> metis_tac[]) >>
  `sb.cs_current_bb = sd.cs_current_bb /\
   sb.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd sb /\
   emitted_insts sd sb =
     [mk_inst sd.cs_next_id MSTORE [ptr_op; val_op] [];
      mk_inst sm.cs_next_id LOG logops []]` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
        fresh_id_def, emit_def, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `run_inst_seq (emitted_insts sd sb) s = OK t` by
    (asm_rewrite_tac[] >>
     simp[run_inst_seq_def, Once step_inst_base_def, exec_write2_def] >>
     gvs[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sd sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sd sb) = []` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all hash_run_path >> simp[] >> strip_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def, gasSummaryTheory.gas_marked_exec_def] >>
  qexistsl_tac [`INL NoneV`,
    `es2 with logs := es2.logs ++ [encode_raw_event_values cx.txn.target vs bs]`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[dest_BytesV_def, lift_option_type_def, lift_option_def, type_check_def,
       assert_def, push_log_def, bind_def, ignore_bind_def, return_def] >>
  irule expr_post_none_intro >>
  simp[stmt_state_rel_inst_idx, stmt_state_rel_gas_obs] >>
  gvs[wb_frame_def, locals_kept_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) t` mp_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx ee t` >>
  `es2 with <|logs := es2.logs ++
     [encode_raw_event_values cx.txn.target vs (TAKE 32 (word_to_bytes_be w))];
              gas_obs := []|> = ee with gas_obs := []` by simp[Abbr `ee`] >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem raw_log_alloc_path[local]:
  compile_alloc_buffer 32 sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    sa.cs_next_id < sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) 32 b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n w) 32 b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule exprSimAllocTheory.buffer_alloc_code >> goal_assum (drule_at Any) >> simp[]) >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_inst_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
        fresh_id_def, emit_def, emitted_insts_def,
        rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
  drule_all hash_run_path >> simp[] >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `w`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  gvs[lookup_var_def, local_region_def] >> metis_tac[]
QED

Theorem raw_log_dynamic_sim[local]:
  call = Call NoneT RawLog
    [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
      (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] NONE /\
  expr_type data = BaseT (BytesT (Dynamic m)) /\
  compatible_bound (Dynamic n) (LENGTH topics) /\ LENGTH topics <= 4 /\
  EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
  expr_sim_below cenv (expr_size call) /\ expr_sim_pre cenv cx env call es ==>
  expr_vv_sim ctx func cenv cx ty call es
Proof
  strip_tac >> rw[expr_vv_sim_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_raw_log_shape] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_at (Pat `expr_sim_pre _ _ _ _ _`) raw_log_topics_ready >>
  simp[expr_size_def] >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  `cs_extends sa st1 /\ sa.cs_next_var <= st1.cs_next_var /\
   sa.cs_next_id <= st1.cs_next_id /\ LENGTH topic_ops = LENGTH topics /\
   EVERY (\x. (!z. x = Var z ==> not_fresh_at st1 z) /\
              (!l. x <> Label l)) topic_ops` by
    (irule lower_word_args_shape >>
     qexistsl [`expr_type`, `cenv`] >>
     gvs[wb_args_shape_def, compile_multi_exprs_lower_word_args] >>
     first_assum MATCH_ACCEPT_TAC) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends st2 st3 /\ cs_extends st3 st4 /\ cs_extends st4 sb` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def,
              fragExecTheory.cs_extends_emit_inst] >>
  `fn_has_code sa st1 func /\ fn_has_code st1 st2 func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  irule expr_stack_outcome >> conj_tac
  >- metis_tac[raw_log_eval_value] >>
  `~cx.txn.is_static` by gvs[stmt_state_rel_def, state_rel_def] >>
  simp[raw_log_eval] >>
  drule_at (Pat `expr_sim_pre _ _ _ _ _`) raw_log_topics_sim >>
  simp[expr_size_def] >> strip_tac >>
  irule raw_log_topics_bind >>
  qexists `\vs ee t. typed_args_post ctx func cenv cx es sa s0 ee topics topic_ops vs t /\
       t.vs_current_bb = st1.cs_current_bb /\
       t.vs_inst_idx = LENGTH st1.cs_current_insts` >>
  reverse conj_tac
  >- (`(\(rr : value list + exception) (ee : evaluation_state) r.
          ?exc. rr = INR exc /\ expr_exit (INR exc : value + exception) r) =
       (\rr ee r. wb_args_exit rr r)` by
        (simp[FUN_EQ_THM] >> Cases >> simp[wb_args_exit_def]) >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      pop_assum (fn th => rewrite_tac[th]) >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >> suspend "data"
QED
Resume raw_log_dynamic_sim[data]:
  drule_all raw_log_topics_marked_source >> strip_tac >>
  qpat_x_assum `!sb' sa' s0' ops func' ctx'. _` kall_tac >>
  `~t.vs_halted` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     drule fragGasModeTheory.gas_marked_path_exec >>
     metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     disch_then (mp_tac o MATCH_MP
       vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom) >> simp[]) >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` kall_tac >>
  gvs[] >>
  `expr_sim ctx func cenv cx (expr_type data) data (mid with gas_obs := [])` by
    (irule raw_log_data_sim >> conj_tac
     >- (qexistsl [`NoneT`, `NONE`,
          `Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
            (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics`] >>
         simp[expr_size_def]) >>
     qexists `env` >> simp[]) >>
  `gas_admissible (vyperState$bind (eval_expr cx data) (read_result cx)) expr_res_ok
      (mid with gas_obs := [])` by
    (rw[gasContextTheory.gas_admissible_def] >>
     `expr_sim_pre cenv cx env data (mid with gas_obs := gs)` by simp[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_sim_pre_res_ok) >> simp[]) >>
  pure_once_rewrite_tac[GSYM bind_assoc] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule expr_sim_suffix >> simp[] >>
  qexistsl [`cenv`, `v`, `st1`, `st2`, `expr_type data`] >>
  simp[] >> reverse conj_tac
  >- (conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
      gvs[typed_args_post_def]) >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env data (mid with gas_obs := gs)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_sim_pre_eval) >> strip_tac >>
  `?bs. v' = BytesV bs` by
    (gvs[vyperTypeExprResultTheory.expr_result_typed_def,
         vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
         vyperTypeInvariantsTheory.value_result_typed_def,
         vyperValueTheory.evaluate_type_def] >>
     Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `expr_post ctx func cenv cx data es sa st2 s0 ee (BytesV bs) v t'` by
    (irule raw_log_post_rebase >> simp[] >>
     qexistsl [`mid with gas_obs := []`, `st1`, `t`] >>
     simp[] >> gvs[typed_args_post_def]) >>
  `eval_operands topic_ops t = SOME (MAP event_value_to_word vs)` by
    metis_tac[raw_log_topics_post_words] >>
  `eval_operands topic_ops t' = SOME (MAP event_value_to_word vs)` by
    (irule raw_log_post_operands >> goal_assum (drule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `LENGTH vs <= 4` by gvs[typed_args_post_def] >>
  qexists `[]` >>
  irule (CONV_RULE (DEPTH_CONV ETA_CONV) raw_log_dynamic_tail_summary) >>
  simp[expr_type_def] >>
  qpat_assum `expr_post _ _ _ _ _ es sa _ s0 _ _ _ _` (irule_at Any) >>
  qpat_assum `emit_op MLOAD _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op ADD _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operands topic_ops t' = _` (irule_at Any) >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type data))` by
    metis_tac[well_typed_expr_type_evaluates] >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  conj_tac
  >- (drule exprOperandVarTheory.compile_lower_value_var >>
      metis_tac[local_ptrs_reserved_next_var]) >>
  conj_tac >- (simp[wordsTheory.dimword_def] >> decide_tac) >>
  conj_tac
  >- (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >> simp[not_fresh_at_def] >> decide_tac) >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]
QED
Finalise raw_log_dynamic_sim

Theorem raw_log_fixed_sim[local]:
  call = Call NoneT RawLog
    [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
      (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] NONE /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  compatible_bound (Dynamic n) (LENGTH topics) /\ LENGTH topics <= 4 /\
  EVERY ($= (BaseT (BytesT (Fixed 32)))) (MAP expr_type topics) /\
  expr_sim_below cenv (expr_size call) /\ expr_sim_pre cenv cx env call es ==>
  expr_vv_sim ctx func cenv cx ty call es
Proof
  strip_tac >> rw[expr_vv_sim_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_raw_log_shape] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_at (Pat `expr_sim_pre _ _ _ _ _`) raw_log_topics_ready >>
  simp[expr_size_def] >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  `cs_extends sa st1 /\ sa.cs_next_var <= st1.cs_next_var /\
   sa.cs_next_id <= st1.cs_next_id /\ LENGTH topic_ops = LENGTH topics /\
   EVERY (\x. (!z. x = Var z ==> not_fresh_at st1 z) /\
              (!l. x <> Label l)) topic_ops` by
    (irule lower_word_args_shape >>
     qexistsl [`expr_type`, `cenv`] >>
     gvs[wb_args_shape_def, compile_multi_exprs_lower_word_args] >>
     first_assum MATCH_ACCEPT_TAC) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
  `cs_extends st1 st2 /\ cs_extends st3 st4 /\ cs_extends st4 sb` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def,
              fragExecTheory.cs_extends_emit_inst] >>
  `fn_has_code sa st1 func /\ fn_has_code st2 st3 func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  irule expr_stack_outcome >> conj_tac
  >- metis_tac[raw_log_eval_value] >>
  `~cx.txn.is_static` by gvs[stmt_state_rel_def, state_rel_def] >>
  simp[raw_log_eval] >>
  drule_at (Pat `expr_sim_pre _ _ _ _ _`) raw_log_topics_sim >>
  simp[expr_size_def] >> strip_tac >>
  irule raw_log_topics_bind >>
  qexists `\vs ee t. typed_args_post ctx func cenv cx es sa s0 ee topics topic_ops vs t /\
       t.vs_current_bb = st1.cs_current_bb /\
       t.vs_inst_idx = LENGTH st1.cs_current_insts` >>
  reverse conj_tac
  >- (`(\(rr : value list + exception) (ee : evaluation_state) r.
          ?exc. rr = INR exc /\ expr_exit (INR exc : value + exception) r) =
       (\rr ee r. wb_args_exit rr r)` by
        (simp[FUN_EQ_THM] >> Cases >> simp[wb_args_exit_def]) >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      pop_assum (fn th => rewrite_tac[th]) >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >> suspend "data"
QED
Resume raw_log_fixed_sim[data]:
  drule_all raw_log_topics_marked_source >> strip_tac >>
  qpat_x_assum `!sb' sa' s0' ops func' ctx'. _` kall_tac >>
  `~t.vs_halted` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     drule fragGasModeTheory.gas_marked_path_exec >>
     metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     disch_then (mp_tac o MATCH_MP
       vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom) >> simp[]) >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` kall_tac >>
  gvs[] >>
  `expr_sim ctx func cenv cx (expr_type data) data (mid with gas_obs := [])` by
    (irule raw_log_data_sim >> conj_tac
     >- (qexistsl [`NoneT`, `NONE`,
          `Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
            (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics`] >>
         simp[expr_size_def]) >>
     qexists `env` >> simp[]) >>
  `gas_admissible (vyperState$bind (eval_expr cx data) (read_result cx)) expr_res_ok
      (mid with gas_obs := [])` by
    (rw[gasContextTheory.gas_admissible_def] >>
     `expr_sim_pre cenv cx env data (mid with gas_obs := gs)` by simp[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_sim_pre_res_ok) >> simp[]) >>
  `local_ptrs_reserved cenv st1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `fn_has_code st1 st2 func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    gvs[typed_args_post_def] >>
  drule_all raw_log_alloc_path >> strip_tac >>
  irule stmtSimDeclComposeTheory.gas_outcome_zero_prefix >>
  goal_assum (drule_at Any) >>
  pure_once_rewrite_tac[GSYM bind_assoc] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule expr_sim_suffix >> simp[] >>
  qexistsl [`cenv`, `v`, `st2`, `st3`, `expr_type data`] >>
  simp[] >> reverse conj_tac
  >- (conj_tac
      >- (irule local_ptrs_reserved_next_var >> qexists `st1` >> simp[] >>
          drule emitted_insts_emit_op_local >> simp[]) >>
      gvs[stmt_state_rel_gas_obs]) >>
  rpt gen_tac >> strip_tac >> suspend "tail"
QED
Resume raw_log_fixed_sim[tail]:
  qpat_x_assum `expr_sim_below _ _` kall_tac >>
  qpat_x_assum `typed_args_ready _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_expr cx _) _ _` kall_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_marked_path _ _ _ _ _ _` kall_tac >>
  `expr_sim_pre cenv cx env data (mid with gas_obs := gs)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_sim_pre_eval) >> strip_tac >>
  `?bs. v' = BytesV bs` by
    (gvs[vyperTypeExprResultTheory.expr_result_typed_def,
         vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
         vyperTypeInvariantsTheory.value_result_typed_def,
         vyperValueTheory.evaluate_type_def] >>
     Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `MAP FDOM mid.scopes = MAP FDOM ee.scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV)
       exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `st1.cs_next_var <= st2.cs_next_var /\ st1.cs_next_id <= st2.cs_next_id` by
    (drule emitted_insts_emit_op_local >> simp[]) >>
  `local_ptrs_reserved cenv st2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_allocating_tail >> simp[] >>
     qexistsl [`t`, `mid.scopes`, `st1`] >>
     gvs[typed_args_post_def]) >>
  `expr_post ctx func cenv cx data es sa st3 s0 ee (BytesV bs) v t''` by
    (irule raw_log_post_rebase >> simp[] >>
     qexistsl [`mid with gas_obs := []`, `st2`, `t'`] >> simp[] >> decide_tac) >>
  `FLOOKUP t''.vs_allocas st1.cs_next_id = SOME (w2n w,32) /\
   lookup_var p t'' = SOME (n2w (w2n w)) /\
   (!name lb len. local_region cenv ee.scopes t'' name lb len ==>
     w2n w + 32 <= lb \/ lb + len <= w2n w)` by
    (irule raw_log_scratch_transport >>
     qpat_assum `expr_post _ _ _ _ _ (mid with gas_obs := []) _ _ _ _ _ _ _` (irule_at Any) >>
     gvs[eval_operand_def, compileEnvTheory.regions_disjoint_def] >>
     first_assum MATCH_ACCEPT_TAC) >>
  `eval_operands topic_ops t = SOME (MAP event_value_to_word vs)` by
    metis_tac[raw_log_topics_post_words] >>
  `eval_operands topic_ops t' = SOME (MAP event_value_to_word vs)` by
    (irule raw_log_operands_frame >> qexistsl [`t`, `st1`] >> simp[]) >>
  `EVERY (\op. (!p. op = Var p ==> not_fresh_at st2 p) /\
                 (!l. op <> Label l)) topic_ops` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[not_fresh_at_def] >> decide_tac) >>
  `eval_operands topic_ops t'' = SOME (MAP event_value_to_word vs)` by
    (irule raw_log_post_operands >>
     qpat_assum `expr_post _ _ _ _ _ (mid with gas_obs := []) _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `value_has_type (BaseTV (BytesT (Fixed 32))) (BytesV bs)` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def,
        vyperValueTheory.evaluate_type_def] >>
  `MEM (mk_inst st1.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString st1.cs_next_var)]) (fn_insts func)` by
    (irule hash_emitted_inst_mem >> qexistsl [`st1`, `st2`] >> simp[] >>
     drule emitted_insts_emit_op_local >> simp[]) >>
  qexists `[]` >>
  irule (CONV_RULE (DEPTH_CONV ETA_CONV) raw_log_fixed_tail_summary) >>
  qpat_assum `expr_post _ _ _ _ _ es sa _ s0 _ _ _ _` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operands topic_ops t'' = _` (irule_at Any) >>
  simp[expr_type_def] >>
  qexistsl [`mk_inst st1.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString st1.cs_next_var)]`, `w2n w`] >>
  simp[mk_inst_def, eval_operand_def] >>
  conj_tac >- gvs[typed_args_post_def] >>
  metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]
QED
Finalise raw_log_fixed_sim

Theorem raw_log_expr_vv_ok:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawLog) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawLog) args dflt)
Proof
  rw[expr_vv_ok_def] >>
  `well_typed_expr env (Call ann RawLog args dflt)` by
    gvs[expr_sim_pre_def] >>
  drule raw_log_typed_shape >> strip_tac >> gvs[]
  >- (irule raw_log_fixed_sim >> simp[] >> metis_tac[]) >>
  irule raw_log_dynamic_sim >> simp[] >> metis_tac[]
QED
