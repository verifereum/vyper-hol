(* Scope-specialized robust ghost boundary for a local aggregate copy.
   The write window is explicit: bytestring padding is part of the copy. *)
Theory assignTuplePtrLocalCopyGhost
Ancestors
  assignTuplePtrScopeUpdate assignTuplePtrCopyLen vyperLookup vyperState
  finite_map bodyPtrDefs assignTuplePtrStoreWord localPtrsProps compileEnv loweringStateRelDefs

Theorem local_copy_scope_lookup_ptr:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  lookup_scopes name
    (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) = SOME e ==>
  (?old. lookup_scopes name es.scopes = SOME old) /\
  (name = id ==> e.type = entry.type /\ e.value = v) /\
  (name <> id ==> lookup_scopes name es.scopes = SOME e)
Proof
  strip_tac >> Cases_on `name = id`
  >- (gvs[] >> drule find_containing_scope_pre_none >> strip_tac >>
      gvs[lookup_scopes_update] >>
      metis_tac[find_containing_scope_lookup]) >>
  drule find_containing_scope_structure >> strip_tac >>
  fs[lookup_scopes_update_other] >>
  qpat_x_assum `es.scopes = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> simp[]
QED

Theorem local_copy_ghost_update_ptr:
  ghost_inv d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME dw /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  val_wf entry.type v /\ val_footprint entry.type v <= n /\
  mem_bytes_at (w2n dw) n t.vs_memory = mem_bytes_at src n s.vs_memory /\
  (!i. i < n ==> (w2n dw+i IN tn'.t_mem <=> src+i IN tn.t_mem)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type v src m) /\
  (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  local_ptrs_rel func cenv es.scopes s /\
  local_region cenv es.scopes s id (w2n dw) sz /\ n <= sz /\
  stor_taint_ok cx tn' t ==>
  ghost_inv d cenv cx
    (es with scopes := pre ++
      (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) G' tn' t
Proof
  strip_tac >>
  `!name x cap. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) cap) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
    op_taint tn' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  irule ghost_inv_local_copy_update >>
  conj_tac >- simp[] >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[ghost_inv_def, return_buf_ptr_def] >>
      irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `ghost_inv _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`{i | w2n dw <= i /\ i < w2n dw+n}`, `v`,
    `entry.type`, `src`, `n`, `id`, `w2n dw`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!name x cap. FLOOKUP _ _ = _ ==> _` drule >>
      strip_tac >> gvs[ptr_covers_def])
  >- (rpt strip_tac >> drule_all local_copy_scope_lookup_ptr >>
      strip_tac >> gvs[] >>
      drule_all local_region_other_footprint_ptr >> simp[])
  >- (rpt strip_tac >> drule_all local_copy_scope_lookup_ptr >> simp[])
  >> rpt strip_tac >> gvs[] >>
  qpat_assum `!name x cap. FLOOKUP _ _ = _ ==> _` drule >> simp[] >>
  strip_tac >> gvs[]
QED
