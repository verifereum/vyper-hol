(* Memory-taint monotonicity and region-separated copy transport. *)
Theory bodyFullUnwrapSlotFrame
Ancestors
  bodyFullUnwrapSlotPost bodyPtrDefs ptrDiscipline pred_set arithmetic

Theorem ghost_inv_at_mem_decrease:
  ghost_inv_at D lo d cenv cx es G tn s /\ m SUBSET tn.t_mem ==>
  ghost_inv_at D lo d cenv cx es G (tn with t_mem := m) s
Proof
  strip_tac >>
  `!mem. mem_agree_outside m s.vs_memory mem ==>
     mem_agree_outside tn.t_mem s.vs_memory mem` by
    (gvs[mem_agree_outside_def, SUBSET_DEF] >> metis_tac[]) >>
  `!p sz. ptr_covers G (tn with t_mem := m) p s sz <=> ptr_covers G tn p s sz` by
    simp[ptr_covers_def, op_taint_def] >>
  `return_buf_ptr d cenv G (tn with t_mem := m) s <=> return_buf_ptr d cenv G tn s` by
    (Cases_on `d` >- simp[return_buf_ptr_def] >>
     rename1 `return_buf_ptr (SOME pair) _ _ _ _` >> PairCases_on `pair` >>
     simp[return_buf_ptr_def]) >>
  gvs[ghost_inv_at_def, op_taint_def, stor_taint_ok_at_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum (drule_all_then strip_assume_tac) >> metis_tac[]) >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem unwrap_slot_copy_ghost_inv_at_mono:
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel func cenv es.scopes s /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    start+nb <= b \/ b+len <= start) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!j. j < start \/ start+nb <= j ==> (j IN tf.t_mem ==> j IN tn.t_mem)) /\
  lo <= start /\ stor_taint_ok_at D tf z /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  ghost_inv_at D lo d cenv cx es H tf z
Proof
  strip_tac >>
  qabbrev_tac `m = tn.t_mem UNION {j | start <= j /\ j < start+nb}` >>
  `ghost_inv_at D lo d cenv cx es H (tf with t_mem := m) z` by
    (irule unwrap_slot_copy_ghost_inv_at >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac >- fs[stor_taint_ok_at_def] >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
     qexistsl [`nb`, `sa`, `start`] >>
     simp[op_taint_def, Abbr `m`, ADD_COMM] >>
     fs[op_taint_def] >> metis_tac[NOT_LESS_EQUAL]) >>
  `tf.t_mem SUBSET m` by
    (simp[SUBSET_DEF, Abbr `m`] >> rpt strip_tac >>
     Cases_on `start <= x /\ x < start+nb` >> gvs[] >>
     metis_tac[NOT_LESS, NOT_LESS_EQUAL]) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ (_ with t_mem := _) _`
    (mp_then Any (qspec_then `tf.t_mem` mp_tac) ghost_inv_at_mem_decrease) >>
  simp[]
QED
