Theory bodyPtrPopAggregateBoundary
Ancestors
  bodyPtrPopDynAssignProbe supportedTypes supportedExprs
  compileEnv vyperValue

(* Boundary ledger for multiword replacement:
   context.compile_dynarray_to_storage copies [dst+1, dst+1+len*ew)
   and then writes dst. A saved region disjoint from these writes can use
   pop_region_taint_frame, once operational storage/taint frames are supplied.
   Inside that prefix, a saved descendant needs imported taint dead relative
   to its OWN header, not relative to the source root. The branch's MLOAD /
   word-copy loop supplies no recursive inner-length guard. supported_place_type
   admits the triple-array layout; supported_copy_types admits equal types.
   However supported_expr admits Pop only at TopLevelNameTarget. Hence these
   type facts do not certify a supported caller containing the nested Pop.
   Missing producer: source/compiler reachable-place hypotheses must either
   exclude such captured descendants or imply their imported bytes are locally
   dead under the replacement header. ptr_mem_ok at the root is insufficient.
   The empty-outer run in DynAssignProbe does not exercise this boundary. *)

Theorem pop_dyn_assign_supported_layout:
  supported_place_type tops pop_dyn_assign_ty /\
  supported_storage_type tops pop_dyn_assign_ty /\
  supported_copy_types pop_dyn_assign_ty pop_dyn_assign_ty
Proof
  EVAL_TAC
QED

Theorem pop_dyn_assign_nested_pop_unsupported:
  ~supported_expr tops
    (Pop ann (SubscriptTarget (SubscriptTarget root ix) iy))
Proof
  Cases_on `root` >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED
