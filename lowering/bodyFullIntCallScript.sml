(* Adapt the interpreter's internal-call induction hypotheses to the
 * supplied-argument, omitted-default, and callee-body stages. *)
Theory bodyFullIntCall
Ancestors bodyFullShadowBodyInv
  bodyFullIntCallDefs bodyFullPreds bodyIntCallSeams bodySim constSubst
  vyperInterpreter vyperState vyperAST finite_map list
  bodyFullIntCallArgs bodyFullIntCallReturn compileVyper moduleLowering fragGasFocus
  gasShadowCompile gasShadowState exprSimAccounts fragExec exprSimUnwrap
  bodySimFull exprLowering compileEnv exprSimDefs vyperStorageTrace
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified] bodyFullPostsMods constSubstMods
  bodyFullIntCallCallee[qualified] bodyPtrDefs[qualified]
  bodyInvCodeProps[qualified] contractInvContextProps[qualified]
Libs
  pairLib

val _ = Parse.hide "body";

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
       body_exprs_full_ok_mods mods exps cxd needed_dflts) /\
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut,nr,args,dflts,ret,ss) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    ~MEM (src_id_opt,fn) cx.stk /\
    eval_exprs cx es s1 = (INL vs,t1) ==>
    body_exprs_full_ok_mods mods exps (cx with stk updated_by CONS (src_id_opt,fn))
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
       body_stmts_full_ok_mods mods exps cxf body') /\
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
    body_stmts_full_ok_mods mods exps (cx with stk updated_by CONS (src_id_opt,fn)) ss
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

(* The entry boundary records both evaluated argument lists.  Specialize
   an arbitrary body IH at those arguments, before entering the callee. *)
Theorem intcall_entry_after_arguments_mods:
  (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  intcall_entry_full_mods (DF,lo,d) H mods src tops ctx func cenv cx tenv name es
    sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  (!s1 vs t1 sd dvs td p rt.
     ~MEM (src,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) /\
     eval_exprs (cx with stk updated_by CONS (src,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
       (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
     bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME p /\
     evaluate_type (get_tenv cx) ret = SOME rt /\
     (nr ==> IS_SOME cx.nonreentrant_slot) /\
     (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==> P) ==>
  ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==> P)
Proof
  strip_tac >>
  `nr ==> IS_SOME cx.nonreentrant_slot` by
    simp[] >>
  qhdtm_x_assum `intcall_entry_full_mods`
    (fn entry =>
       map_every strip_assume_tac
         (List.take (CONJUNCTS (PURE_REWRITE_RULE [intcall_entry_full_mods_def] entry), 3))) >>
  strip_tac >>
  first_x_assum irule >>
  fs[] >> metis_tac[]
QED

Theorem intcall_entry_after_arguments:
  body_inv tops ctx cenv cx /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
    sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  (!s1 vs t1 sd dvs td p rt.
     ~MEM (NONE,name) cx.stk /\
     eval_exprs cx es s1 = (INL vs,t1) /\
     eval_exprs (cx with stk updated_by CONS (NONE,name))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
       (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
     bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME p /\
     evaluate_type (get_tenv cx) ret = SOME rt /\
     (nr ==> IS_SOME cx.nonreentrant_slot) /\
     (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==> P) ==>
  ((nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==> P)
Proof
  strip_tac >>
  drule_then assume_tac body_inv_contract >>
  drule_then (assume_tac o CONJUNCT1) bodyInvCodePropsTheory.body_inv_module_locations >>
  drule_then assume_tac bodyInvSplitTheory.contract_inv_immutable_section_layout >>
  drule_then assume_tac contractInvContextPropsTheory.contract_inv_singleton_source_modules >>
  `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[body_inv_nonreentrant_slot] >>
  `intcall_entry_full_mods (DF,lo,d) H [(NONE,tops)] NONE tops ctx func cenv cx tenv name es
     sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
    asm_simp_tac bool_ss [intcall_entry_full_mods_singleton] >>
  strip_tac >> drule_all_then ACCEPT_TAC intcall_entry_after_arguments_mods
QED

Theorem bind_return_right:
  bind m return = m
Proof
  simp[FUN_EQ_THM, bind_def, return_def] >> gen_tac >>
  Cases_on `m x` >> rename1 `(res,_)` >> Cases_on `res` >> simp[]
QED

(* The shadow of an expression compiles to the same value, ending related. *)
Theorem shadow_compile_same[local]:
  gas_shadow_state sa shadow_sa /\
  compile_expr cenv ty e sa = (vv, sm) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (vv2, shadow_sm) ==>
  vv2 = vv /\ gas_shadow_state sm shadow_sm
Proof
  strip_tac >>
  qspecl_then [`cenv`,`ty`,`e`,`T`] mp_tac
    (CONJUNCT1 (Q.INST [`sd` |-> `T`] gas_shadow_compile_expr_env)) >>
  simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]
QED

val dead_lo_ok_mods_eq =
  PURE_REWRITE_RULE [GSYM bodyPtrDefsTheory.dead_lo_ok_def] dead_lo_ok_mods_def;
val ghost_inv_at_mods_eq =
  PURE_REWRITE_RULE [GSYM bodyPtrDefsTheory.ghost_inv_at_def] ghost_inv_at_mods_def;

fun apply_linked_args kc out f P rewrites (goal as (_,target)) =
  let
    val rest_post :: normal_post :: _ = rev (snd (strip_comb target))
    val generic_call =
      Q.SPECL [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
        `mods`,`exps`,`caller_src`,`caller_tops`,`src`,`callee_tops`,`vis`,
        `cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,`mut`,`nr`,
        `args`,`ret`,`ss`,`rr`,`dflts`] intcall_args_full
    val binders = fst (strip_forall (rand (concl generic_call)))
    fun binder_type name =
      type_of (valOf (List.find (fn v => fst (dest_var v) = name) binders))
    val call = INST_TYPE (match_type (binder_type "kc") (type_of (Term kc)) @
                          match_type (binder_type "f") (type_of (Term f))) generic_call
    val source_pre = lhand (concl call)
    val machine =
      call |> UNDISCH
           |> Q.SPECL [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`]
           |> Q.SPECL [kc,out,f,P]
           |> SPECL [normal_post,rest_post] |> PURE_REWRITE_RULE rewrites
  in
    (mp_tac (DISCH source_pre machine) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) goal
  end;

fun apply_linked_return return_rule sm shadow_sm =
  mp_tac (Q.SPECL [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,
    `mods`,`exps`,`caller_src`,`caller_tops`,`src`,`callee_tops`,`vis`,
    `cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,`st0`,`sa`,
    sm,`shadow_sa`,shadow_sm,`vv`,`s0`,`G0`,`tn0`,`mut`,`nr`,`args`,
    `ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,`t`,`G`,`tn`,`nrc`,`nrbs`,
    `npvs`,`dflts`] return_rule) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (qexists_tac `H` >> first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt gen_tac >> strip_tac >>
     mp_tac (Q.SPECL [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`func`,`mods`,`exps`,
       `caller_src`,`caller_tops`,`src`,`callee_tops`,`vis`,`cenv`,`cx`,`tenv`,`name`,
       `es`,`st0`,`sa`,sm,`vv`,`s0`,`es0`,`G0`,`tn0`,`mut`,`nr`,`args`,`ret`,
       `ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,`t`,`G`,`tn`,`callee`,`entered`,`nrc`,
       `nrbs`,`npvs`,`dflts`] bodyFullIntCallCalleeTheory.intcall_callee_full) >>
     impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        qpat_assum `valid_horizon cx st0 H es1.storage_trace` (fn horizon =>
          qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> _`
            (assume_tac o C MATCH_MP horizon)) >>
        strip_tac >> drule_all_then ACCEPT_TAC intcall_entry_after_arguments_mods) >>
     disch_then (qspecl_then [`bb`,`inst`,`lbl`,`arg_ops`,`argv`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC);

Theorem intcall_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func mods exps caller_src caller_tops
   src callee_tops vis cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods caller_src caller_tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx tenv es0 /\
    expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (src,name)) es dflt) es0 /\
    ALOOKUP mods src = SOME callee_tops /\
    (src = NONE \/ context_function_live cx (src,name)) /\
    ((src = NONE /\ mods = [(NONE,callee_tops)]) \/
     MEM (src,name) (linked_live_functions mods exps)) /\
    lookup_callable_function cx.in_deploy name callee_tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret ss) callee_tops /\
    (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    (~MEM (src,name) cx.stk ==> body_exprs_full_ok_mods mods exps cx es) /\
    (!s1 vs t1.
       ~MEM (src,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok_mods mods exps (cx with stk updated_by CONS (src,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs_mods (consts_env_mods mods) dflts))) /\
    (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (src,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (src,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok_mods mods exps (cx with stk updated_by CONS (src,name))
         (subst_consts_stmts_mods (consts_env_mods mods) ss)) ==>
    expr_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (IntCall (src,name)) es dflt) es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def, ghost_inv_at_mods_eq, dead_lo_ok_mods_eq] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _`
    (assume_tac o REWRITE_RULE [lower_value_def, ETA_THM]) >>
  `unwrap_value (gas_shadow_env T cenv) = unwrap_value cenv` by
    simp[FUN_EQ_THM] >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o REWRITE_RULE [lower_value_def, ETA_THM]) >>
  qpat_x_assum `unwrap_value _ = unwrap_value _` (fn eq =>
    qpat_x_assum `comp_bind (compile_expr _ _ (gas_shadow_expr _)) _ _ = _`
      (assume_tac o REWRITE_RULE [eq])) >>
  `?vv2 shadow_sm.
     compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Call ann (IntCall (src,name)) es dflt)) shadow_sa =
       (vv2, shadow_sm) /\
     unwrap_value cenv vv2 shadow_sm = (op, shadow_sb)` by
    (qpat_assum `comp_bind (compile_expr _ _ (gas_shadow_expr _)) _ _ = _` mp_tac >>
     pure_rewrite_tac[comp_bind_def, LET_THM, pairTheory.ELIM_UNCURRY] >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Call ann (IntCall (src,name)) es dflt)) shadow_sa` >>
     simp[]) >>
  `!v. storage_trace_frame (read_result cx v)` by
    simp[storage_trace_frame_read_result] >>
  `!v. cs_appends (unwrap_value cenv v)` by
    (rw[cs_appends_def] >> drule_then ACCEPT_TAC unwrap_value_extends) >>
  `?nrc nrbs npvs. cenv.ce_func_info (nsid_to_string (src,name)) =
                (nrc,nrbs,npvs)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  apply_linked_args `unwrap_value cenv` `op` `read_result cx` `expr_res_ok` [] >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (simp[expr_res_ok_def, expr_vv_res_ok_def] >> NO_TAC) >>
     TRY (qpat_assum `!H. valid_horizon cx st0 H es0.storage_trace ==> _`
            (fn initial =>
              gen_tac >> disch_then (strip_assume_tac o MATCH_MP initial) >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >> NO_TAC) >>
     rpt gen_tac >> strip_tac >>
     `vv2 = vv /\ gas_shadow_state sm shadow_sm` by
       (drule_all shadow_compile_same >> simp[]) >>
     qpat_x_assum `vv2 = vv` SUBST_ALL_TAC >>
     apply_linked_return intcall_return_full `sm` `shadow_sm` >>
     disch_then (qspecl_then [`op`,`sb`,`shadow_sb`] mp_tac o CONJUNCT2) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED


Theorem intcall_vv_full:
  !DF lo d ctx shadow_ctx PG func shadow_func mods exps caller_src caller_tops
   src callee_tops vis cenv cx tenv ty ann name
   es dflt es0 mut nr args ret ss rr dflts.
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods caller_src caller_tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx tenv es0 /\
    expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (src,name)) es dflt) es0 /\
    ALOOKUP mods src = SOME callee_tops /\
    (src = NONE \/ context_function_live cx (src,name)) /\
    ((src = NONE /\ mods = [(NONE,callee_tops)]) \/
     MEM (src,name) (linked_live_functions mods exps)) /\
    lookup_callable_function cx.in_deploy name callee_tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret ss) callee_tops /\
    (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
    (~MEM (src,name) cx.stk ==> body_exprs_full_ok_mods mods exps cx es) /\
    (!s1 vs t1.
       ~MEM (src,name) cx.stk /\ eval_exprs cx es s1 = (INL vs,t1) ==>
       body_exprs_full_ok_mods mods exps (cx with stk updated_by CONS (src,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs_mods (consts_env_mods mods) dflts))) /\
    (!s1 vs t1 sd dvs td penv rtv.
       ~MEM (src,name) cx.stk /\
       eval_exprs cx es s1 = (INL vs,t1) /\
       eval_exprs (cx with stk updated_by CONS (src,name))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         (sd with scopes := [FEMPTY]) = (INL dvs,td) /\
       bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
       evaluate_type (get_tenv cx) ret = SOME rtv /\
       (nr ==> IS_SOME cx.nonreentrant_slot) /\
       (nr /\ ~is_view_mut mut ==> ~cx.txn.is_static) ==>
       body_stmts_full_ok_mods mods exps (cx with stk updated_by CONS (src,name))
         (subst_consts_stmts_mods (consts_env_mods mods) ss)) ==>
    expr_vv_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (IntCall (src,name)) es dflt) es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_full_mods_def, ghost_inv_at_mods_eq, dead_lo_ok_mods_eq] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?nrc nrbs npvs. cenv.ce_func_info (nsid_to_string (src,name)) =
                  (nrc,nrbs,npvs)` by metis_tac[pairTheory.ABS_PAIR_THM] >>
  `!v : eval_result. storage_trace_frame (return v)` by
    simp[storage_trace_frame_return] >>
  `!v : vyper_value. cs_appends (comp_return v)` by simp[cs_appends_return] >>
  apply_linked_args `comp_return : vyper_value -> vyper_value compiler` `vv`
    `return : eval_result -> evaluation_state -> (eval_result + exception) # evaluation_state`
    `expr_vv_res_ok` [bind_return_right, comp_bind_comp_return] >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (simp[] >> NO_TAC) >>
     TRY (qpat_assum `!H. valid_horizon cx st0 H es0.storage_trace ==> _`
            (fn initial =>
              gen_tac >> disch_then (strip_assume_tac o MATCH_MP initial) >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >> NO_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `comp_return _ _ = _`
       (strip_assume_tac o SIMP_RULE std_ss [comp_return_def, pairTheory.PAIR_EQ]) >>
     qpat_x_assum `_ = vv` SUBST_ALL_TAC >>
     qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
     apply_linked_return intcall_return_full_owned `sb` `shadow_sb` >>
     disch_then (mp_tac o CONJUNCT1) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
