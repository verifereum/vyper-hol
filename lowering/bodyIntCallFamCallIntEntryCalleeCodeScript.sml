(* Source selection and entry ownership retain the very same packaged callee. *)
Theory bodyIntCallFamCallIntEntryCalleeCode
Ancestors
  bodyIntCallFamCallIntEntryRuntimeCode bodyIntCallFamCallIntEntryDeployCode
  bodyIntCallFamCallIntEntryFunctionCode bodySim compileVyper

Theorem intcall_selected_callee_entry_code:
  !tops ctx caller cx mut rr name args ret ss.
    body_inv tops ctx caller cx /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops ==>
    ?ut nk im lbl ce params rb nr key tr view ctor il body rt b c callee
     ce2 rpc immopt m.
      set_internal_package_target caller.ce_target
        (package_internal_fn tops ut nk caller.ce_is_ctor im
          (mut,F,rr,name,args,([]:expr list),ret,ss)) =
        (lbl,ce,params,rb,nr,key,tr,view,ctor,il,body,rt) /\
      lookup_function lbl ctx.ctx_functions = SOME callee /\
      compile_internal_function ce params rb nr key tr view ctor il body rt b =
        ((),c) /\ fn_has_code b c callee /\
      compile_internal_function_entry ce params rb ctor il rt b =
        ((ce2,rpc,immopt),m) /\
      cs_extends b m /\ cs_extends m c /\ fn_has_code b m callee
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `cx.in_deploy`
  >- (drule_all intcall_deploy_selected_code >> strip_tac >>
      drule_all intcall_function_entry_code >> strip_tac >>
      goal_assum (drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule_all intcall_runtime_selected_code >> strip_tac >>
  drule_all intcall_function_entry_code >> strip_tac >>
  goal_assum (drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
      rpt (goal_assum (drule_at Any)) >> simp[]
QED
