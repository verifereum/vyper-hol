(* Buffer metadata does not affect a located value's store bound. *)
Theory locatedValueStoreBound
Ancestors
  exprSimMemDefs context

Theorem vv_store_bound_located_mk_ptr:
  vv_store_bound cx ty lt es tv (LocatedValue vt p) s <=>
  vv_store_bound cx ty lt es tv
    (LocatedValue vt (mk_ptr p.ptr_operand p.ptr_location)) s
Proof
  simp[vv_store_bound_def, mk_ptr_def]
QED
