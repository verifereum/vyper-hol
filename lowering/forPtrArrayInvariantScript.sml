(* Shared array-round contracts prevent drift between preparation, callback
   finishing and exhaustion. These only package existing semantic resources;
   robust source contents are derived from the current ghost, not framed. *)
Theory forPtrArrayInvariant
Ancestors forPtrArraySnapshot stmtSimForArrayLoop bodyPtrDefs forPtrElement
  compileEnv loweringPosts exprSimDefs venomExecSemantics vyperState
  venomState ptrDiscipline finite_map list valueEncoding arithmetic

Definition for_array_inv_ptr_def:
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot k es G tn s <=>
  array_loop_inv ctx func cenv cx
    (\ei. lookup_scopes name ei.scopes = SOME snapshot)
    vs id idx (Var bp) arr_base p dst sz ainst cond_lbl st k es s /\
  ghost_inv d cenv cx es G tn s /\ FLOOKUP G idx = NONE /\
  op_taint tn (Var idx) = {} /\ ptr_covers G tn p s sz /\
  ptr_covers G tn bp s (LENGTH vs * type_memory_size tv) /\
  (!nm lo z. local_region cenv es.scopes s nm lo z ==>
    regions_disjoint (w2n dst) sz lo z) /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x))
End

Definition for_array_done_ptr_def:
  for_array_done_ptr ctx func cenv cx exit_lbl st s0 G0 tn0 d es G tn s <=>
  s.vs_current_bb = exit_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x))
End

Theorem for_array_inv_element_ptr:
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot k es G tn s /\
  k < LENGTH vs /\ snapshot.type = ArrayTV tv (Fixed n) /\
  snapshot.value = ArrayV (SArrayV kvs) /\
  vs = array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs) /\ n = LENGTH vs /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var bp) arrsz) ==>
  ptr_covers G tn bp s ((k+1)*type_memory_size tv) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (EL k vs) (w2n arr_base + k*type_memory_size tv) mem)
Proof
  strip_tac >> fs[for_array_inv_ptr_def, array_loop_inv_def, eval_operand_def] >>
  conj_tac
  >- (fs[ptr_covers_def] >>
      `k+1 <= LENGTH vs` by decide_tac >>
      `((k+1)*type_memory_size tv) <= LENGTH vs * type_memory_size tv` by
        simp[LESS_MONO_MULT] >> decide_tac) >>
  qpat_assum `vs = _` (fn th => once_rewrite_tac[th]) >>
  rpt strip_tac >> irule for_local_array_element_robust >> metis_tac[]
QED

Theorem for_array_inv_header_ptr:
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot k es G tn s ==>
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  lookup_var idx s = SOME (n2w k) /\ FLOOKUP G idx = NONE /\
  op_taint tn (Var idx) = {} /\
  (!x v. not_fresh_at st x /\ lookup_var x s0 = SOME v ==>
    lookup_var x s = SOME v) /\
  (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x))
Proof
  simp[for_array_inv_ptr_def, array_loop_inv_def]
QED
