Theory exprSimIfExpWidenedOwnedProvenance
Ancestors
  loweringPosts exprSimProps context

Theorem vv_own_memory_transport:
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ val_wf dtv v /\
  val_footprint stv v = val_footprint dtv v /\
  vv_own ce cx sty sa sb es raw (LocatedValue t (mk_ptr op LocMemory)) s ==>
  vv_at ce cx dty sa sb es raw (LocatedValue t' (mk_ptr op LocMemory)) s
Proof
  simp[vv_own_def, vv_at_def, mk_ptr_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`v`, `stv`] mp_tac) >> simp[] >>
  metis_tac[]
QED
