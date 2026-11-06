(* Compiler-indexed dispatch for pointer-safe forcing; location inversion stays here. *)
Theory exprPtrUnwrapMarked
Ancestors
  exprPtrUnwrapIdentity exprPtrUnwrapLoad exprPtrUnwrapStorage
  exprPtrUnwrapStorageMarked exprPtrUnwrapCode exprPtrUnwrapCodeCopyMarked
  exprPtrUnwrapStorageShape exprPtrUnwrapStorageSource
  bodyPtrDefs loweringPosts compileEnv context

Theorem vv_post_located_type:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s ==>
  t = expr_type e
Proof
  simp[vv_post_def, vv_holds_def]
QED

Theorem vv_post_not_calldata:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s ==>
  p.ptr_location <> LocCalldata
Proof
  simp[vv_post_def, vv_holds_def] >> rpt strip_tac >> gvs[]
QED
