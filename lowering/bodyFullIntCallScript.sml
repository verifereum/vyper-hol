(* Adapt the interpreter's internal-call induction hypotheses to the
 * supplied-argument, omitted-default, and callee-body stages. *)
Theory bodyFullIntCall
Ancestors bodyFullShadowBodyInv
  bodyFullIntCallDefs bodyFullPreds bodyIntCallSeams bodySim
  vyperInterpreter vyperState vyperAST finite_map list
  bodyFullIntCallReturn compileVyper moduleLowering fragGasFocus
  gasShadowCompile gasShadowState exprSimAccounts fragExec exprSimUnwrap
  bodySimFull exprLowering compileEnv exprSimDefs vyperStorageTrace
Libs
  pairLib

val _ = Parse.hide "body";

Theorem intcall_results_full_ih:
  !cx src_id_opt fn es ts mut nr args dflts ret ss.
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
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    ~MEM (src_id_opt,fn) cx.stk ==>
    body_exprs_full_ok cx es
Proof
  rpt strip_tac >>
  `LENGTH args - LENGTH es <= LENGTH dflts` by decide_tac >>
  first_x_assum irule >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def]
QED

Theorem intcall_defaults_full_ih:
  !cx src_id_opt fn es ts mut nr args dflts ret ss s1 vs t1.
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
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    ~MEM (src_id_opt,fn) cx.stk /\
    eval_exprs cx es s1 = (INL vs,t1) ==>
    body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
Proof
  rpt strip_tac >>
  `LENGTH args - LENGTH es <= LENGTH dflts` by decide_tac >>
  first_x_assum irule >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def,
       get_scopes_def, set_scopes_def] >>
  metis_tac[]
QED

Theorem intcall_body_full_ih:
  !cx src_id_opt fn es ts mut nr args dflts ret ss s1 vs t1 sd dvs td penv rtv.
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
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    ~MEM (src_id_opt,fn) cx.stk /\
    eval_exprs cx es s1 = (INL vs,t1) /\
    eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
      (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
    bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    (nr ==> IS_SOME cx.nonreentrant_slot) /\
    (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
    body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn)) ss
Proof
  rpt strip_tac >>
  `LENGTH args - LENGTH es <= LENGTH dflts` by decide_tac >>
  `?st out. lock_if_nr cx nr (is_view_mut mut) st = (INL (),out)` by
    (drule_all lock_if_nr_runs >> simp[]) >>
  `finally
      (ignore_bind (set_scopes [FEMPTY])
        (eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)))
      (set_scopes sd.scopes) sd = (INL dvs,td with scopes := sd.scopes)` by
    gvs[finally_def, ignore_bind_apply, set_scopes_def, return_def] >>
  first_x_assum irule >>
  simp[type_check_def, assert_def, lift_option_type_def, return_def,
       get_scopes_def, push_function_def] >>
  qexistsl_tac [`dvs`, `penv`, `s1`, `sd`, `sd`, `td`,
    `st`, `t1`, `td with scopes := sd.scopes`, `td`, `out`, `vs`] >>
  gvs[return_def]
QED

(* The entry boundary records both evaluated argument lists, so the body IH
   can be specialized before dispatching to the callee stage. *)
Theorem intcall_entry_body_ih[local]:
  body_inv tops ctx cenv cx /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
    sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  (!s1 vs t1 sd dvs td penv rtv.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) /\
     eval_exprs (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
       (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
     bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
     evaluate_type (get_tenv cx) ret = SOME rtv /\
     (nr ==> IS_SOME cx.nonreentrant_slot) /\
     (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
     body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss) ==>
  ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
   body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss)
Proof
  strip_tac >>
  `nr ==> IS_SOME cx.nonreentrant_slot` by
    (strip_tac >> drule_all body_inv_nonreentrant_slot >> simp[]) >>
  qhdtm_x_assum `intcall_entry_full`
    (fn entry =>
       map_every strip_assume_tac
         (List.take (CONJUNCTS (PURE_REWRITE_RULE [intcall_entry_full_def] entry), 3))) >>
  strip_tac >>
  first_x_assum irule >>
  fs[] >> metis_tac[]
QED


(* Use only the two Args continuation types needed by the composition. *)
val args_input = Term `
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LENGTH es <= LENGTH args /\
    ~supportedExprTraverse$supported_exprs_exists (const_name_root cx)
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
    ~supportedExprTraverse$supported_exprs_exists supportedProgram$expr_msg_gas_root
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
    (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) ==>
    !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 kc out f P Q R.
      (!v. storage_trace_frame (f v)) /\
      (!v. cs_appends (kc v)) /\
      comp_bind (compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt))
        kc sa = (out, sb) /\
      comp_bind
        (compile_expr cenv ty
           (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)))
        kc shadow_sa = (out, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible
        (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
        P es0 /\
      (!e. P (INR e) ==> expr_vv_res_ok (INR e)) /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (!H. valid_horizon cx st0 H es0.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es0 s0 /\
        storage_well_formed_on cx es0 (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!H res ee gt r.
         expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
         R H res ee gt r) /\
      (!vv sm prev penv rtv es1 t G tn.
         compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
           (vv, sm) /\
         kc vv sm = (out, sb) /\
         (!H. valid_horizon cx st0 H es1.storage_trace ==>
            intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name
              es sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv
              es1 t G tn) /\
         (?H. valid_horizon cx st0 H es1.storage_trace) /\
         gas_admissible (bind (intcall_rest cx name mut nr ss prev rtv) f)
           P es1 ==>
         gas_outcome_full
           (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
           (cx_tops cx) cx st0
           (bind (intcall_rest cx name mut nr ss prev rtv) f) (es1, t, G, tn)
           Q R) ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0
        (bind (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) f)
        (es0, s0, G0, tn0) Q R
`;
val callee_input = Term `
  !DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn callee entered rc
   rbs pvs dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LENGTH es <= LENGTH args /\
    ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss) /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es
         sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
         G tn) /\
    gas_invoke_entry (ctx,func) t callee entered /\
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) ==>
    !bb inst lbl arg_ops argv.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      decode_invoke inst = SOME (lbl,arg_ops) /\
      eval_operands arg_ops t = SOME argv ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
         MAP (op_prov G) arg_ops)
        (cx_tops cx) cx st0 (intcall_callee_src cx name mut nr ss)
        (es1, entered, FEMPTY, tn with t_var := FEMPTY)
        (\H res ee G' tn' t'. F)
        (\H res ee gt r.
           intcall_callee_exit_full (DF, lo) H func cenv cx mut nr rtv rc
             (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
             sa.cs_next_id sb.cs_next_id t tn res ee gt r)
`;

fun args_instance kc f =
  let
    val (_, call) = strip_forall args_input
    val (stage_vars, _) = strip_forall (snd (dest_imp call))
    fun binder_type name =
      type_of (valOf (List.find (fn v => fst (dest_var v) = name) stage_vars))
    val comp_inst = match_type (binder_type "kc") (type_of kc)
    val source_inst = match_type (binder_type "f") (type_of f)
  in
    inst (comp_inst @ source_inst) args_input
  end;

val read_args_input =
  args_instance
    (Term `unwrap_value cenv : vyper_value -> operand compiler`)
    (Term `read_result cx`);
val vv_args_input =
  args_instance
    (Term `comp_return : vyper_value -> vyper_value compiler`)
    (Term `return : eval_result -> evaluation_state ->
                    (eval_result + exception) # evaluation_state`);

fun stage_tac input ttac =
  first_assum (fn th => if aconv (concl th) input then ttac th else NO_TAC);

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

(* Stage (b) gives stage (c)'s callee premise. *)
Theorem intcall_callee_premise[local]:
  ^callee_input ==>
  !DF lo d ctx shadow_ctx func tops cenv cx tenv name es st0 sa sb vv s0 es0
   G0 tn0 mut nr args ret ss rr prev penv rtv es1 t G tn nrc nrbs npvs dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss) /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
        (cx_tops cx) cx st0 (intcall_callee_src cx name mut nr ss)
        (es1, entered, FEMPTY, tn with t_var := FEMPTY)
        (\H res ee G' tn' t'. F)
        (\H res ee gt r.
           intcall_callee_exit_full (DF, lo) H func cenv cx mut nr rtv nrc
             (if nrc = 0 /\ 0 < nrbs then SOME (HD argv) else NONE)
             sa.cs_next_id sb.cs_next_id t tn res ee gt r)
Proof
  strip_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
      sa sb vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
    (qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  qpat_assum `body_inv _ _ _ _` (fn inv =>
    qpat_assum `lookup_callable_function _ _ _ = SOME _` (fn lookup =>
      qpat_assum `MEM (FunctionDecl Internal _ _ _ _ _ _ _ _) _` (fn decl =>
        qhdtm_assum `intcall_entry_full` (fn entry =>
          qpat_assum `!s1 vs t1 sd dvs td penv rtv. _ ==> body_stmts_full_ok _ _`
            (fn ih =>
              assume_tac (MATCH_MP intcall_entry_body_ih
                (LIST_CONJ [inv, lookup, decl, entry, ih]))))))) >>
  first_assum (fn callee_stage =>
    if aconv (concl callee_stage) callee_input then
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`func`,`tops`,`cenv`,`cx`,
               `tenv`,`name`,`es`,`st0`,`sa`,`sb`,`vv`,`s0`,`es0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`callee`,`entered`,`nrc`,`nrbs`,`npvs`,`dflts`]
    mp_tac callee_stage
    else NO_TAC) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`bb`,`inst`,`lbl`,`arg_ops`,`argv`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

(* The value judgment: stage (a) with the unwrap and the read after the
   call, then stage (c)'s second conjunct. *)
Theorem intcall_sim_full:
  ^read_args_input ==> ^callee_input ==>
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    ~supportedExprTraverse$supported_exprs_exists (const_name_root cx)
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
    ~supportedExprTraverse$supported_exprs_exists supportedProgram$expr_msg_gas_root
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
    (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
    (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss) ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
Proof
  strip_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _`
    (assume_tac o REWRITE_RULE [lower_value_def, ETA_THM]) >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o REWRITE_RULE [lower_value_def, ETA_THM]) >>
  `?vv2 shadow_sm.
     compile_expr cenv ty
       (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)) shadow_sa =
       (vv2, shadow_sm) /\
     unwrap_value cenv vv2 shadow_sm = (op, shadow_sb)` by
    (qpat_x_assum `comp_bind (compile_expr _ _ (gas_shadow_expr _)) _ _ = _`
       mp_tac >>
     simp[comp_bind_def] >> pairarg_tac >> simp[]) >>
  `!v. storage_trace_frame (read_result cx v)` by
    simp[storage_trace_frame_read_result] >>
  `!v. cs_appends (unwrap_value cenv v)` by
    (rw[cs_appends_def] >> metis_tac[unwrap_value_extends]) >>
  `?nrc nrbs npvs. cenv.ce_func_info (nsid_to_string (NONE,name)) =
                (nrc,nrbs,npvs)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  stage_tac read_args_input (fn args_stage =>
    let val header = Q.SPECL [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
                `tops`,`cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,
                `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`dflts`] args_stage
    in mp_tac (header
    |> UNDISCH
    |> Q.SPECL [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`]
    |> Q.ISPECL [`unwrap_value cenv : vyper_value -> operand compiler`]
    |> Q.SPEC `op`
    |> Q.ISPECL [`read_result cx`]
    |> Q.SPEC `expr_res_ok` |> DISCH (fst (dest_imp (concl header)))) end) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[expr_res_ok_def, expr_vv_res_ok_def] >> NO_TAC)
  >- (rpt gen_tac >> strip_tac >>
  `vv2 = vv /\ gas_shadow_state sm shadow_sm` by
    (qpat_assum `gas_shadow_state sa shadow_sa` (fn initial =>
       qpat_assum `compile_expr _ _ (Call _ _ _ _) sa = (vv,sm)` (fn real =>
         qpat_assum `compile_expr _ _ (gas_shadow_expr _) shadow_sa = _`
           (fn shadow =>
             ACCEPT_TAC (MATCH_MP shadow_compile_same
               (LIST_CONJ [initial, real, shadow])))))) >>
  qpat_x_assum `vv2 = vv` SUBST_ALL_TAC >>
  stage_tac callee_input (qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`func`,`tops`,`cenv`,`cx`,
               `tenv`,`name`,`es`,`st0`,`sa`,`sm`,`vv`,`s0`,`es0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`nrc`,`nrbs`,`npvs`,`dflts`] mp_tac o MP intcall_callee_premise) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  strip_tac >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
               `tops`,`cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,
               `st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`nrc`,`nrbs`,`npvs`,`dflts`] mp_tac intcall_return_full >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      disch_then (irule o CONJUNCT2) >> simp[]) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt strip_tac >>
  fs[expr_res_ok_def, expr_vv_res_ok_def]
QED


(* Use the return stage's owned value post for the expression judgment. *)
Theorem intcall_vv_full:
  ^vv_args_input ==> ^callee_input ==>
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    ~supportedExprTraverse$supported_exprs_exists (const_name_root cx)
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
    ~supportedExprTraverse$supported_exprs_exists supportedProgram$expr_msg_gas_root
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
    (~MEM (NONE,name) cx.stk ==> body_exprs_full_ok cx es) /\
    (!s1 vs t1.
       ~MEM (NONE,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
    (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (NONE,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (NONE,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (NONE,name)) ss) ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (IntCall (NONE,name)) es dflt) es0
Proof
  strip_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  `?nrc nrbs npvs. cenv.ce_func_info (nsid_to_string (NONE,name)) =
                (nrc,nrbs,npvs)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  `!v : eval_result. storage_trace_frame (return v)` by
    simp[storage_trace_frame_return] >>
  `!v : vyper_value. cs_appends (comp_return v)` by simp[cs_appends_return] >>
  stage_tac vv_args_input (fn args_stage =>
    let val header = Q.SPECL [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
                `tops`,`cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,
                `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`dflts`] args_stage
    in mp_tac (header
    |> UNDISCH
    |> Q.SPECL [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`]
    |> Q.ISPECL [`comp_return : vyper_value -> vyper_value compiler`]
    |> Q.SPEC `vv`
    |> Q.ISPECL [`return : eval_result -> evaluation_state ->
                           (eval_result + exception) # evaluation_state`]
    |> Q.SPEC `expr_vv_res_ok` |> DISCH (fst (dest_imp (concl header)))) end) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[bind_return_right, comp_bind_comp_return] >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[expr_res_ok_def, expr_vv_res_ok_def] >> NO_TAC)
  >- (rpt gen_tac >> strip_tac >>
  qpat_x_assum `comp_return _ _ = _`
    (strip_assume_tac o SIMP_RULE std_ss [comp_return_def, pairTheory.PAIR_EQ]) >>
  qpat_x_assum `_ = vv` SUBST_ALL_TAC >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  stage_tac callee_input (qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`func`,`tops`,`cenv`,`cx`,
               `tenv`,`name`,`es`,`st0`,`sa`,`sb`,`vv`,`s0`,`es0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`nrc`,`nrbs`,`npvs`,`dflts`] mp_tac o MP intcall_callee_premise) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  strip_tac >>
  qspecl_then [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
               `tops`,`cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,
               `st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`vv`,`s0`,`G0`,`tn0`,
               `mut`,`nr`,`args`,`ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,
               `t`,`G`,`tn`,`nrc`,`nrbs`,`npvs`,`dflts`] mp_tac intcall_return_full_owned >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      disch_then (irule o CONJUNCT1) >> simp[]) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt strip_tac >> fs[]
QED
