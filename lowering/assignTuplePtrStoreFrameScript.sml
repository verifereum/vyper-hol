(* Updated-scope assembly: representation of the changed local is supplied
   separately; this boundary transports only the nonlocal ghost clauses. *)
Theory assignTuplePtrStoreFrame
Ancestors
  bodyPtrDefs

Theorem updated_scope_ghost_inv_ptr:
  ghost_inv d cenv cx es G tn s /\
  (!p. lookup_var p t = lookup_var p s) /\
  (!p. op_taint tn' (Var p) = op_taint tn (Var p)) /\
  stor_taint_ok cx tn' t /\
  (!name entry p sz.
     lookup_scopes name es'.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     ptr_covers G tn' p t sz /\
     !w m. lookup_var p t = SOME w /\
       mem_agree_outside tn'.t_mem t.vs_memory m ==>
       val_in_memory entry.type entry.value (w2n w) m) ==>
  ghost_inv d cenv cx es' G tn' t
Proof
  rpt strip_tac >>
  gvs[ghost_inv_def] >>
  conj_tac >- metis_tac[] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME pair) cenv G tn' t` >>
  PairCases_on `pair` >>
  gvs[return_buf_ptr_def, ptr_covers_def] >>
  metis_tac[]
QED
