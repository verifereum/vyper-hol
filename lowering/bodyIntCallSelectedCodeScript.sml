(* Selected internal compilation interval in either lowering mode. *)
Theory bodyIntCallSelectedCode
Ancestors
  bodyIntCallDeployCode bodyIntCallRuntimeCode bodySim

Theorem body_inv_selected_internal_code:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops F (assign_nkeys tops 0) cx.in_deploy
      (if cx.in_deploy then
         compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
       else 0)
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (label,ce,params,has_buf,nr',key,trans,view,ctor,ilen,compiled_ss,rty) ==>
  ?func before old st0 after.
    lookup_function label ctx.ctx_functions = SOME func /\
    new_block label before = (old,st0) /\
    compile_internal_function ce params has_buf nr' key trans view ctor ilen
      compiled_ss rty st0 = ((),after) /\
    fn_has_code st0 after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks) /\
    ctx_inst_ids_distinct ctx
Proof
  strip_tac >>
  qpat_x_assum `body_inv _ _ _ _` mp_tac >>
  simp[body_inv_def] >> strip_tac >>
  Cases_on `cx.in_deploy` >> gvs[]
  >- (drule_all lower_vyper_deploy_unit_selected_internal_code >> simp[]) >>
  drule_all lower_vyper_runtime_unit_selected_internal_code >> simp[]
QED
