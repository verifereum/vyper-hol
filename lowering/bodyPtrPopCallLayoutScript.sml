Theory bodyPtrPopCallLayout
Ancestors intCallStep context

(* This projection records the returned layout, not the annotation of the
   expression and not a semantic representation claim. *)
Theorem pop_intcall_result_type:
  compile_call cfn cenv ret_ty ty (IntCall fid) args dret sa = (vv,sb) ==>
  vv_type vv = cenv.ce_func_return_type (nsid_to_string fid)
Proof
  strip_tac >>
  Cases_on `cenv.ce_func_info (nsid_to_string fid)` >>
  PairCases_on `r` >>
  drule_all compile_call_intcall_shape >> strip_tac >>
  Cases_on `0 < q` >> gvs[vv_type_def] >>
  Cases_on `0 < r0` >> gvs[vv_type_def]
QED
