(* Trigger the evaluator's explicit-argument callback before entering the callee. *)
Theory bodyIntCallExplicitIHMods
Ancestors
  bodyFullPredsMods bodyIntCallSource vyperState

Theorem intcall_explicit_args_ih_mods:
  !mods exps ctx cenv cx env ty src fn es dflt st.
    contract_inv mods exps ctx cenv cx /\
    expr_body_pre_mods mods cenv cx env (Call ty (IntCall (src,fn)) es dflt) st /\
    ~MEM (src,fn) cx.stk /\
    (!s x t s3 ts t3 s4 tup t4 mut stup nr stup2 args sstup dflts sstup2
         ret ss s5 x' t5.
       type_check (~MEM (src,fn) cx.stk) "recursion" s = (INL x,t) /\
       lift_option_type (get_module_code cx src)
         "IntCall get_module_code" s3 = (INL ts,t3) /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s4 = (INL tup,t4) /\
       mut = FST tup /\ stup = SND tup /\ (nr <=> FST stup) /\
       stup2 = SND stup /\ args = FST stup2 /\ sstup = SND stup2 /\
       dflts = FST sstup /\ sstup2 = SND sstup /\ ret = FST sstup2 /\
       ss = SND sstup2 /\
       type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s5 = (INL x',t5) ==>
       body_exprs_full_ok_mods mods exps cx es) ==>
    body_exprs_full_ok_mods mods exps cx es
Proof
  rpt strip_tac >>
  drule_all body_intcall_source_selection_mods >> strip_tac >>
  `LENGTH args - LENGTH es <= LENGTH dflts` by decide_tac >>
  first_x_assum irule >>
  simp[type_check_def, assert_def, return_def] >>
  qexistsl_tac [`st`, `st`, `(mut,nr,args,dflts,ret,ss)`] >> fs[]
QED
