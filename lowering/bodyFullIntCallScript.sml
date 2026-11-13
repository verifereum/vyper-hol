(*
 * The internal call's full case from its three stages: arguments
 * (bodyFullIntCallArgs), callee (bodyFullIntCallCallee) and return
 * (bodyFullIntCallReturn).
 *
 * TOP-LEVEL:
 *   body_intcall_case_full -- evaluate_ind's IntCall case for
 *     bodySimFullMain's induction
 *)
Theory bodyFullIntCall
Ancestors
  bodyFullIntCallArgs bodyFullIntCallCallee bodyFullIntCallReturn
  bodyFullIntCallDefs bodyIntCallSeams bodyIntCallSource bodyFullPreds
  bodySimFull gasOutcomeFull gasShadowState gasShadowCompile gasShadow
  exprSimAccounts exprSimDefs exprSimHypsDefs exprLowering compileEnv
  bodyPtrDefs
  vyperInterpreter vyperState vyperAST list pair

val _ = Parse.hide "body";

Theorem bind_return_right[local]:
  bind m return = m
Proof
  simp[FUN_EQ_THM, bind_def, return_def] >> gen_tac >>
  Cases_on `m x` >> rename1 `(res,_)` >> Cases_on `res` >> simp[]
QED

(* The shadow of an expression compiles to the same value, ending related. *)
Theorem shadow_compile_same[local]:
  gas_shadow_state sa shadow_sa /\
  compile_expr cenv ty e sa = (vv, sm) /\
  compile_expr cenv ty (gas_shadow_expr e) shadow_sa = (vv2, shadow_sm) ==>
  vv2 = vv /\ gas_shadow_state sm shadow_sm
Proof
  strip_tac >>
  qspecl_then [`cenv`,`ty`,`e`,`T`] mp_tac (CONJUNCT1 gas_shadow_compile_expr) >>
  simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]
QED

(* The IHs at a supported callee (body_intcall_source_selection): no
   defaults, as many arguments as parameters. *)
Theorem intcall_results_full_ih[local]:
  !cx src_id_opt fn es ts mut nr args ret ss.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_exprs_full_ok cx es) /\
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut,nr,args,[],ret,ss) /\
    LENGTH es = LENGTH args /\ ~MEM (src_id_opt,fn) cx.stk ==>
    body_exprs_full_ok cx es
Proof
  rpt strip_tac >> first_x_assum irule >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def]
QED

Theorem intcall_body_full_ih[local]:
  !cx src_id_opt fn es ts mut nr args ret ss s1 vs t1 s3 u t3 penv rtv.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' vs t'4' needed_dflts cxd s'7' prev
         t'5' s'8' dflt_vs t'6' all_tenv s'9' env t'7' s'10' rtv
         t'8' is_view s'11' x'' t'9' s'12' cxf t'10'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_exprs cx es s'6' = (INL vs,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally
         (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd needed_dflts))
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'9' = (INL env,t'7') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'10' =
       (INL rtv,t'8') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'11' = (INL x'',t'9') /\
       push_function (src_id_opt,fn) env cx s'12' = (INL cxf,t'10') ==>
       body_stmts_full_ok cxf body') /\
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut,nr,args,[],ret,ss) /\
    LENGTH es = LENGTH args /\ ~MEM (src_id_opt,fn) cx.stk /\
    eval_exprs cx es s1 = (INL vs,t1) /\
    bind_arguments (get_tenv cx) args vs = SOME penv /\
    lock_if_nr cx nr (is_view_mut mut) s3 = (INL u,t3) /\
    evaluate_type (get_tenv cx) ret = SOME rtv ==>
    body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn)) ss
Proof
  rpt strip_tac >> first_x_assum irule >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def,
       get_scopes_def, finally_def, ignore_bind_def, bind_def,
       set_scopes_def, push_function_def, Once evaluate_def] >>
  qexistsl_tac [`penv`,`s1`,`s3`,`s3`,`t1`,`s3`,`t3`,`vs`] >>
  Cases_on `u` >> qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
  simp[return_def, lock_if_nr_def, ignore_bind_def]
QED

(* Stage (b) gives stage (c)'s callee premise. *)
Theorem intcall_callee_premise[local]:
  !DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn nrc nrbs npvs.
    body_inv tops ctx cenv cx /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args [] ret ss) tops /\
    (!s1 vs t1 s3 u t3 penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       bind_arguments (get_tenv cx) args vs = SOME penv /\
       lock_if_nr cx nr (is_view_mut mut) s3 = (INL u,t3) /\
       evaluate_type (get_tenv cx) ret = SOME rtv ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss) /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es
         sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
         G tn) /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (nrc,nrbs,npvs) ==>
    !callee entered bb inst lbl arg_ops argv.
      gas_invoke_entry (ctx,func) t callee entered /\
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
         MAP (op_prov G) arg_ops)
        (cx_tops cx) cx st0 (intcall_callee_src cx name ss)
        (es1, entered, FEMPTY, tn with t_var := FEMPTY)
        (\H res ee G' tn' t'. F)
        (\H res ee gt r.
           intcall_callee_exit_full (DF, lo) H func cenv cx rtv nrc
             (if nrc = 0 /\ 0 < nrbs then SOME (HD argv) else NONE)
             sa.cs_next_id t tn res ee gt r)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `intcall_entry H tops ctx func cenv cx tenv name es sa sb vv s0 es0
     (mut,nr,args,ret,ss,rr) prev penv rtv es1 t` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
     simp[intcall_entry_full_def]) >>
  drule intcall_entry_source >> strip_tac >>
  `body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss` by
    (qpat_x_assum `!s1 vs t1 s3 u t3 penv rtv. _` irule >> metis_tac[]) >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`func`,`tops`,`cenv`,`cx`,
               `tenv`,`name`,`es`,`st0`,`sa`,`sb`,`vv`,`s0`,`es0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`callee`,`entered`,`nrc`,`nrbs`,`npvs`]
    mp_tac intcall_callee_full >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`bb`,`inst`,`lbl`,`arg_ops`,`argv`] mp_tac) >>
  simp[]
QED

(* The vv judgment: stage (a) with nothing after the call, then stage (c)'s
   first conjunct. *)
Theorem intcall_vv_full[local]:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args [] ret ss) tops /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
    (!s1 vs t1 s3 u t3 penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       bind_arguments (get_tenv cx) args vs = SOME penv /\
       lock_if_nr cx nr (is_view_mut mut) s3 = (INL u,t3) /\
       evaluate_type (get_tenv cx) ret = SOME rtv ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss) ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  `?nrc nrbs npvs. cenv.ce_func_info (nsid_to_string (NONE,name)) =
                (nrc,nrbs,npvs)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  mp_tac (intcall_args_full
    |> Q.SPECL [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
                `tops`,`cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,
                `mut`,`nr`,`args`,`ret`,`ss`,`rr`]
    |> UNDISCH
    |> Q.SPECL [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`]
    |> Q.ISPECL [`comp_return : vyper_value -> vyper_value compiler`]
    |> Q.SPEC `vv`
    |> Q.ISPECL [`return : eval_result -> evaluation_state ->
                           (eval_result + exception) # evaluation_state`]
    |> Q.SPEC `expr_vv_res_ok` |> DISCH_ALL) >>
  impl_tac >- simp[] >>
  rewrite_tac[bind_return_right, comp_bind_comp_return] >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`gas_outcome_full _ _ _ _ _ _ _ _`]
  >- (rpt gen_tac >> strip_tac >>
  qpat_x_assum `comp_return _ _ = _`
    (strip_assume_tac o SIMP_RULE std_ss [comp_return_def, PAIR_EQ]) >>
  qpat_x_assum `_ = vv` SUBST_ALL_TAC >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`func`,`tops`,`cenv`,`cx`,
               `tenv`,`name`,`es`,`st0`,`sa`,`sb`,`vv`,`s0`,`es0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`nrc`,`nrbs`,`npvs`] mp_tac intcall_callee_premise >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  strip_tac >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
               `tops`,`cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,
               `st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`vv`,`s0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`nrc`,`nrbs`,`npvs`] mp_tac intcall_return_full >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      disch_then (irule o CONJUNCT1) >> simp[]) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt strip_tac >> first_assum ACCEPT_TAC
QED

(* The value judgment: stage (a) with the unwrap and the read after the
   call, then stage (c)'s second conjunct. *)
Theorem intcall_sim_full[local]:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args [] ret ss) tops /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
    (!s1 vs t1 s3 u t3 penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       bind_arguments (get_tenv cx) args vs = SOME penv /\
       lock_if_nr cx nr (is_view_mut mut) s3 = (INL u,t3) /\
       evaluate_type (get_tenv cx) ret = SOME rtv ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss) ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [lower_value_def, ETA_THM]) >>
  `?vv2 shadow_sm.
     compile_expr cenv ty
       (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)) shadow_sa =
       (vv2, shadow_sm) /\
     unwrap_value cenv vv2 shadow_sm = (op, shadow_sb)` by
    (qpat_x_assum `comp_bind (compile_expr _ _ (gas_shadow_expr _)) _ _ = _`
       mp_tac >>
     simp[comp_bind_def] >> pairarg_tac >> simp[]) >>
  `?nrc nrbs npvs. cenv.ce_func_info (nsid_to_string (NONE,name)) =
                (nrc,nrbs,npvs)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  mp_tac (intcall_args_full
    |> Q.SPECL [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
                `tops`,`cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,
                `mut`,`nr`,`args`,`ret`,`ss`,`rr`]
    |> UNDISCH
    |> Q.SPECL [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`]
    |> Q.ISPECL [`unwrap_value cenv : vyper_value -> operand compiler`]
    |> Q.SPEC `op`
    |> Q.ISPECL [`read_result cx`]
    |> Q.SPEC `expr_res_ok` |> DISCH_ALL) >>
  impl_tac >- simp[] >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`gas_outcome_full _ _ _ _ _ _ _ _`]
  >- (rpt gen_tac >> strip_tac >>
  `vv2 = vv /\ gas_shadow_state sm shadow_sm` by
    (irule shadow_compile_same >> metis_tac[]) >>
  qpat_x_assum `vv2 = vv` SUBST_ALL_TAC >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`func`,`tops`,`cenv`,`cx`,
               `tenv`,`name`,`es`,`st0`,`sa`,`sm`,`vv`,`s0`,`es0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`nrc`,`nrbs`,`npvs`] mp_tac intcall_callee_premise >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  strip_tac >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
               `tops`,`cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,
               `st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`nrc`,`nrbs`,`npvs`] mp_tac intcall_return_full >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      disch_then (irule o CONJUNCT2) >> simp[]) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt strip_tac >>
  fs[expr_res_ok_def, expr_vv_res_ok_def]
QED

(* The IntCall case of bodySimFullMain's induction (case 41). *)
Theorem body_intcall_case_full:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' vs t'4' needed_dflts cxd s'7' prev
         t'5' s'8' dflt_vs t'6' all_tenv s'9' env t'7' s'10' rtv
         t'8' is_view s'11' x'' t'9' s'12' cxf t'10'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_exprs cx es s'6' = (INL vs,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally
         (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd needed_dflts))
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'9' = (INL env,t'7') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'10' =
       (INL rtv,t'8') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'11' = (INL x'',t'9') /\
       push_function (src_id_opt,fn) env cx s'12' = (INL cxf,t'10') ==>
       body_stmts_full_ok cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' vs t'4' needed_dflts cxd s'7' prev
         t'5' s'8' x'' t'6'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_exprs cx es s'6' = (INL vs,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       set_scopes [FEMPTY] s'8' = (INL x'',t'6') ==>
       body_exprs_full_ok cxd needed_dflts) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC[body_expr_full_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all body_intcall_source_selection >> strip_tac >>
  `~MEM (src_id_opt,fn) cx.stk ==> body_exprs_full_ok cx es` by
    (strip_tac >> drule intcall_results_full_ih >> disch_then drule_all >>
     simp[]) >>
  `!s1 vs t1 s3 u t3 penv rtv.
     ~MEM (src_id_opt,fn) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) /\
     bind_arguments (get_tenv cx) args vs = SOME penv /\
     lock_if_nr cx nr (is_view_mut mut) s3 = (INL u,t3) /\
     evaluate_type (get_tenv cx) ret = SOME rtv ==>
     body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn)) ss` by
    (rpt strip_tac >> drule intcall_body_full_ih >> disch_then drule_all >>
     simp[]) >>
  gvs[] >> conj_tac
  >- (irule intcall_sim_full >> simp[] >> metis_tac[]) >>
  irule intcall_vv_full >> simp[] >> metis_tac[]
QED
