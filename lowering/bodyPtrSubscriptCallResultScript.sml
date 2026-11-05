(* Exhaustive compiler routing, retaining the harmless zero-return branch. *)
Theory bodyPtrSubscriptCallResult
Ancestors intCallStep exprLowering context compileEnv

Theorem compile_call_intcall_result:
  compile_call cfn cenv ret_ty ty (IntCall id) args dret sa = (vv,sb) ==>
  ((?p. vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string id)) p /\
        p.ptr_location = LocMemory) \/
   vv = StackValue (cenv.ce_func_return_type (nsid_to_string id)) (Lit 0w))
Proof
  strip_tac >>
  namedCases_on `cenv.ce_func_info (nsid_to_string id)` ["nret rbs pvs"] >>
  drule_all compile_call_intcall_shape >> strip_tac >>
  Cases_on `nret = 0` >> Cases_on `rbs = 0` >>
  gvs[base_ptr_def] >> metis_tac[]
QED

Theorem compile_expr_intcall_result:
  compile_expr cenv ret_ty (Call ty (IntCall id) args dret) sa = (vv,sb) ==>
  ((?p. vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string id)) p /\
        p.ptr_location = LocMemory) \/
   vv = StackValue (cenv.ce_func_return_type (nsid_to_string id)) (Lit 0w))
Proof
  simp[Once compile_expr_def] >>
  metis_tac[compile_call_intcall_result]
QED
