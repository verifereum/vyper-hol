Theory bodyIntCallArgsStageMods
Ancestors
  bodyIntCallSourceBindMods bodyIntCallStagePacketMods
  gasContext exprSimDefs vyperContext vyperInterpreter vyperState
Libs
  monadsyntax

(* Once both argument lists have run, use their actual values to bind the
   callee scopes and retain the packet at the reached INVOKE cursor. *)
Theorem selected_stage_bound_row_mods:
  ~MEM (src,name) cx.stk /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts /\
  gas_admissible (eval_expr cx (Call ann (IntCall (src,name)) es dflt))
    expr_vv_res_ok es0 /\
  eval_exprs cx es (es0 with gas_obs := obs) = (INL vs,mid) /\
  eval_exprs (cx with stk updated_by CONS (src,name))
    (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
    (mid with scopes := [FEMPTY]) = (INL dvs,fin) /\
  intcall_stage_ops_mods (lo,func) ce cx sa
    (s3,fin with scopes := mid.scopes,t,G,tn) pin
    (supplied ++ dfl,ws,vs ++ dvs,ptys,pflags) /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0
    (sa,es0,s0,G0,tn0) (s3,fin with scopes := mid.scopes,t,G,tn) pin ==>
  ?vals penv rtv es1.
    vals = vs ++ dvs /\
    bind_arguments (get_tenv cx) args vals = SOME penv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    es1 = fin with scopes := [penv] /\ es1.scopes = [penv] /\
    intcall_stage_ops_mods (lo,func) ce cx sa
      (s3,es1 with scopes := mid.scopes,t,G,tn) pin
      (supplied ++ dfl,ws,vals,ptys,pflags) /\
    intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0
      (sa,es0,s0,G0,tn0) (s3,es1 with scopes := mid.scopes,t,G,tn) pin
Proof
  strip_tac >> drule_all_then strip_assume_tac selected_source_bind_values_mods >>
  qexistsl [`vs ++ dvs`,`penv`,`rtv`,`fin with scopes := [penv]`] >>
  asm_simp_tac std_ss [evaluation_state_accfupds,
    evaluation_state_fupdfupds, combinTheory.K_THM]
QED
