(* The code base has no mutable-memory ownership to transport. *)
Theory bodyPtrSubscriptSeamArrayCodeFrame
Ancestors
  exprSimSubscriptArrayFrame bodyPtrBopInWordBoundary
  bodyPtrPrecompileBuiltinsGhost bodyPtrDefs loweringPosts

Theorem captured_code_base_transport:
  vv_post ctx func cenv cx obj es sa sb s0 t r
    (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u t' iv iop v /\
  expr_type obj = ArrayT et bd /\ ~cenv.ce_is_ctor /\
  p.ptr_location = LocCode /\
  ptr_vv_ok cx (ArrayT et bd) r (LocatedValue (ArrayT et bd) p) t G0 tn0 u /\
  ghost_kept cenv t sb G0 tn0 u G tn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  t'.scopes = t.scopes /\ t'.immutables = t.immutables /\
  expr_sim_inv cenv cx env t /\ local_ptrs_reserved cenv sb /\
  sb.cs_next_id <= sc.cs_next_id ==>
  vv_holds cenv cx (ArrayT et bd) r (LocatedValue (ArrayT et bd) p) t' v /\
  vv_at cenv cx (ArrayT et bd) sa sc t' r (LocatedValue (ArrayT et bd) p) v /\
  ptr_vv_ok cx (ArrayT et bd) r (LocatedValue (ArrayT et bd) p) t' G tn v
Proof
  strip_tac >>
  `vv_holds cenv cx (ArrayT et bd) r (LocatedValue (ArrayT et bd) p) t' v /\
   vv_at cenv cx (ArrayT et bd) sa sc t' r (LocatedValue (ArrayT et bd) p) v`
    by (irule framed_array_base_transport >> simp[] >> metis_tac[]) >>
  `op_prov G p.ptr_operand = op_prov G0 p.ptr_operand` by
    (irule ghost_kept_operand_prov >> metis_tac[]) >>
  `op_taint tn p.ptr_operand = op_taint tn0 p.ptr_operand` by
    (drule_all ghost_kept_operand_taint >> simp[]) >>
  gvs[ptr_vv_ok_def]
QED
