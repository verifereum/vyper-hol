(* Pointer-result capacity transport along the if-expression join edge. *)
Theory bodyIfExpMemoryJoin
Ancestors
  exprSimMemDefs venomState

Theorem ifexp_pointer_bound_assign:
  vv_store_bound cx ty lt es tv
    (LocatedValue vt (mk_ptr op LocMemory)) s /\
  eval_operand op s = SOME w ==>
  vv_store_bound cx ty lt es tv
    (LocatedValue vt (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w s with vs_inst_idx := k))
Proof
  simp[vv_store_bound_def, contextTheory.mk_ptr_def,
       jump_to_def, update_var_def, eval_operand_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
