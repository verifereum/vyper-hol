Theory bodyPtrPopTraceTransport
Ancestors
  bodyPtrPopWriteTransport bodyPtrPopSavedTransport bodyPtrDefs
  bodyPtrPopRegionInvariant list pair words

val _ = Parse.hide "base";

(* The trace certificate is deliberately conditional. In particular a call
   edge must establish this implication from its actual callee operations. *)
Theorem pop_region_taint_trace_transport:
  !xs p q bs tv.
    EVERY2 (\r u.
      pop_region_taint_ok (FST r) bs tv (SND r) ==>
      pop_region_taint_ok (FST u) bs tv (SND u))
      (p::xs) (xs ++ [q]) /\
    pop_region_taint_ok (FST p) bs tv (SND p) ==>
    pop_region_taint_ok (FST q) bs tv (SND q)
Proof
  Induct
  >- (simp[])
  >> simp_tac bool_ss [APPEND, LIST_REL_def] >> rpt strip_tac >>
  first_x_assum irule >> qexists_tac `h` >> simp[LIST_REL_def]
QED

Theorem pop_region_taint_trace_storage_ptr:
  base < dimword (:256) /\
  op_taint tn p.ptr_operand = {} /\ p.ptr_location = LocStorage /\
  eval_operand p.ptr_operand s = SOME (n2w base) /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  EVERY2 (\r u.
    pop_region_taint_ok (FST r) base tv (SND r) ==>
    pop_region_taint_ok (FST u) base tv (SND u))
    ((st0,X0)::xs) (xs ++ [(st,tn.t_stor)]) /\
  pop_region_taint_ok st0 base tv X0 /\
  (s.vs_accounts s.vs_call_ctx.cc_address).storage = st ==>
  ptr_vv_ok cx t result (LocatedValue t' p) es G tn s
Proof
  strip_tac >>
  drule pop_region_taint_trace_transport >> simp[] >> strip_tac >>
  irule pop_saved_storage_ptr_vv >> simp[] >>
  rpt strip_tac >> gvs[w2n_n2w, pop_region_taint_ok_def] >> metis_tac[]
QED
