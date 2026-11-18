(* Adapt the interpreter's internal-call induction hypotheses to the
 * supplied-argument, omitted-default, and callee-body stages. *)
Theory bodyFullIntCall
Ancestors
  bodyFullPreds bodyIntCallSeams vyperInterpreter vyperState vyperAST
  finite_map list

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
