Theory bodyPtrCodeSliceCase
Ancestors
  bodyPtrCodeSliceSelf bodyPtrCodeSliceExternal
  bodyPtrPreds vyperInterpreter exprLowering

Theorem body_code_slice_some_ptr:
  !cx ty bt es ct addr.
    code_slice_source bt es = SOME (ct,addr) /\
    body_exprs_ptr_ok cx (TL es) /\
    (!s vs t. eval_exprs cx (TL es) s = (INL vs,t) ==>
      body_exprs_ptr_ok cx [addr]) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[code_slice_source_SOME] >>
  Cases_on `is_self_code (Builtin ct (Acc Code) [addr])`
  >- (Cases_on `addr` >> gvs[is_self_code_def] >>
      rename1 `Builtin st b args` >> Cases_on `b` >> gvs[is_self_code_def] >>
      rename1 `Env env` >> Cases_on `env` >> gvs[is_self_code_def] >>
      Cases_on `args` >> gvs[is_self_code_def] >>
      irule body_code_slice_self_ptr >> simp[]) >>
  irule body_code_slice_external_ptr >> simp[] >> first_assum ACCEPT_TAC
QED
