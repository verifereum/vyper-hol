(* A final local overwrite needs robust representation, not ghost_kept on
   the overwritten bytes. Scalar stores and aggregate copies share this post. *)
Theory assignBasePtrScopePost
Ancestors assignTuplePtrLocalCopyGhost assignTuplePtrStoreWord assignTuplePtrCopyLen
  bodyPtrDefs robustCopyTransportPtr localPtrsProps compileEnv loweringStateRelDefs
  vyperState vyperLookup finite_map pred_set

Theorem assign_base_local_scope_ghost_post:
  !d cenv cx es G tn s id pre sc entry rest p sz dst n v
    sa t Gf tf func.
    ghost_inv d cenv cx es G tn s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME dst /\
    local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n dst) sz /\ n <= sz /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory entry.type v (w2n dst) mem) /\
    (!i. ~(w2n dst <= i /\ i < w2n dst+n) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    stor_taint_ok cx tf t ==>
    ghost_inv d cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      Gf tf t /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> reverse conj_tac >- simp[] >>
  `!name x cap. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) cap) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  rewrite_tac[ghost_inv_def] >> conj_tac >- suspend "locals" >>
  `return_buf_ptr d cenv Gf tf t` by
    (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
     fs[ghost_inv_def, return_buf_ptr_def] >>
     irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> fs[ghost_inv_def] >> metis_tac[]
QED

Resume assign_base_local_scope_ghost_post[locals]:
  rpt gen_tac >> strip_tac >> fs[] >>
  drule_all local_copy_scope_lookup_ptr >> strip_tac >>
  `lookup_var p' t = lookup_var p' s /\ FLOOKUP Gf p' = FLOOKUP G p' /\
   op_taint tf (Var p') = op_taint tn (Var p')` by metis_tac[] >>
  conj_tac
  >- (irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >>
      fs[ghost_inv_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  `lookup_var p' s = SOME w` by metis_tac[] >> gvs[] >>
  drule_all local_region_other_footprint_ptr >> strip_tac >>
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tf.t_mem`] >>
  simp[] >> fs[ghost_inv_def] >> metis_tac[]
QED

Finalise assign_base_local_scope_ghost_post
