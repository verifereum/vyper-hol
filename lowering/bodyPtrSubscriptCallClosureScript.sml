(* Declaration-indexed boundary for the inherited internal-call case. *)
Theory bodyPtrSubscriptCallClosure
Ancestors
  bodyPtrIntCallCase bodyPtrPreds vyperInterpreter vyperState vyperAST list

Theorem body_intcall_ptr_callable_closure:
  !cx ty src fn es opt.
    body_results_ptr_ok cx es /\
    (!ts mut nr args dflts ret ss.
       get_module_code cx src = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts =
         SOME (mut,nr,args,dflts,ret,ss) ==>
       body_exprs_ptr_ok (cx with stk updated_by CONS (src,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) /\
       body_stmts_ptr_ok (cx with stk updated_by CONS (src,fn)) ss) ==>
    body_expr_ptr_ok cx (Call ty (IntCall (src,fn)) es opt)
Proof
  rpt gen_tac >> strip_tac >>
  irule body_intcall_case_ptr >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[lift_option_type_def, push_function_def, return_def, AllCaseEqs()] >>
  Cases_on `get_module_code cx src` >>
  gvs[raise_def, return_def] >>
  Cases_on `lookup_callable_function cx.in_deploy fn ts` >>
  gvs[raise_def, return_def] >>
  PairCases_on `tup` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED
