(* Raw immutable results can be read without changing the common endpoint. *)
Theory bodyFullToplevelCodeSource
Ancestors
  exprPtrUnwrapCode loweringPosts exprLowering vyperInterpreter

Theorem toplevel_code_runtime_source_post:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (LocatedValue t p,sm) /\
  p.ptr_location = LocCode /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee raw
    (LocatedValue t p) s ==>
  ?v. read_result cx raw ee = (INL v,ee) /\
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee (Value v)
      (LocatedValue t p) s
Proof
  strip_tac >> drule_all vv_post_code_source >> strip_tac >>
  qexists `v` >> simp[] >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, vv_own_def] >> metis_tac[]
QED
