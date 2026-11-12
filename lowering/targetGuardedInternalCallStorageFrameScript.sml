Theory targetGuardedInternalCallStorageFrame
Ancestors
  targetReachableInternalCallStorageFrame

Theorem internal_call_storage_frame_guarded:
  ~cx.in_deploy /\
  (~tr \/ !slot. cx.nonreentrant_slot = SOME slot ==> w <> n2w slot) /\
  (!env st res fin.
    runtime_consistent env cx st /\ functions_well_typed cx /\
    well_typed_exprs env es /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    eval_expr_results cx es st = (res,fin) ==>
    lookup_storage w (get_storage cx fin tr) =
    lookup_storage w (get_storage cx st tr)) /\
  (!ts mut nr args dflts ret body env st res fin.
    get_module_code cx src = SOME ts /\
    lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) /\
    runtime_consistent env (cx with stk updated_by CONS (src,fn)) st /\
    functions_well_typed (cx with stk updated_by CONS (src,fn)) /\
    well_typed_exprs env
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
    call_evaluation_safe (cx with stk updated_by CONS (src,fn))
      (int_calls_exprs (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
    eval_exprs (cx with stk updated_by CONS (src,fn))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) st = (res,fin) ==>
    lookup_storage w (get_storage cx fin tr) =
    lookup_storage w (get_storage cx st tr)) /\
  (!ts mut nr args dflts ret body env ret_ty env' st res fin.
    get_module_code cx src = SOME ts /\
    lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,body) /\
    runtime_consistent env (cx with stk updated_by CONS (src,fn)) st /\
    functions_well_typed (cx with stk updated_by CONS (src,fn)) /\
    type_stmts env ret_ty body = SOME env' /\
    call_evaluation_safe (cx with stk updated_by CONS (src,fn))
      (int_calls_stmts body) /\
    eval_stmts (cx with stk updated_by CONS (src,fn)) body st = (res,fin) ==>
    lookup_storage w (get_storage cx fin tr) =
    lookup_storage w (get_storage cx st tr)) ==>
  !env st res fin.
    runtime_consistent env cx st /\ functions_well_typed cx /\
    well_typed_expr env (Call ty (IntCall (src,fn)) es ann) /\
    call_evaluation_safe cx (int_calls_expr (Call ty (IntCall (src,fn)) es ann)) /\
    eval_expr cx (Call ty (IntCall (src,fn)) es ann) st = (res,fin) ==>
    lookup_storage w (get_storage cx fin tr) =
    lookup_storage w (get_storage cx st tr)
Proof
  rpt strip_tac >> (
  drule_at (Pat `eval_expr _ _ _ = _`) internal_call_storage_frame_reachable >>
  disch_then (qspecl_then [`w`,`tr`,`env`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[])
QED
