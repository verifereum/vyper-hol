Theory bodyPtrPopLocalRootPost
Ancestors
  bodyPtrPopLocalRootRobust bodyPtrPopLocalRootEntry
  assignTuplePtrWordLocals assignTuplePtrLoadStep
  bodyPtrDefs exprSimPop exprSimProps compileEnv context venomState ptrDiscipline
  finite_map pred_set words list

Theorem pop_local_header_ghost:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ 32 <= sz /\
  entry.type = ArrayTV tv (Dynamic cap) /\
  entry.value = ArrayV (DynArrayV vs) /\
  vs <> [] /\ elems_val_wf vs tv /\ LENGTH vs <= cap /\
  lookup_scopes id es'.scopes = SOME (pop_name_entry entry vs) /\
  (!name. name <> id ==> lookup_scopes name es'.scopes = lookup_scopes name es.scopes) ==>
  ghost_inv d cenv cx es' G tn (mstore (w2n a) (n2w (LENGTH vs-1)) s)
Proof
  strip_tac >> drule_all pop_local_robust_layout >> strip_tac >>
  `tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} = tn.t_mem` by
    (simp[EXTENSION] >> metis_tac[]) >>
  `local_region cenv es.scopes s id (w2n a) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  irule ghost_inv_local_word_update_ptr >>
  conj_tac >- gvs[ghost_inv_def, stor_taint_ok_def, mstore_def] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`tn`, `ArrayTV tv (Dynamic cap)`, `ArrayV (DynArrayV (FRONT vs))`] >>
  simp[] >> conj_tac
  >- metis_tac[pop_local_robust_shortened] >>
  rpt strip_tac >> Cases_on `name = id` >> gvs[pop_name_entry_def]
QED

Theorem pop_local_endpoint_ghost:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ 32 <= sz /\
  entry.type = ArrayTV tv (Dynamic cap) /\
  entry.value = ArrayV (DynArrayV vs) /\
  vs <> [] /\ elems_val_wf vs tv /\ LENGTH vs <= cap /\
  lookup_scopes id es'.scopes = SOME (pop_name_entry entry vs) /\
  (!name. name <> id ==> lookup_scopes name es'.scopes = lookup_scopes name es.scopes) /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = (mstore (w2n a) (n2w (LENGTH vs-1)) s).vs_memory /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ghost_inv d cenv cx es' G' tn' t
Proof
  strip_tac >> drule_all pop_local_header_ghost >> strip_tac >>
  irule ghost_inv_old_vars_frame_ptr >>
  goal_assum (drule_at Any) >>
  qexists_tac `sa` >> simp[mstore_def, lookup_var_def] >>
  metis_tac[lookup_var_def]
QED

Theorem pop_local_returned_ptr_vv:
  vs <> [] /\ elems_val_wf vs tv /\ LENGTH vs <= cap /\
  entry.type = ArrayTV tv (Dynamic cap) /\
  lookup_scopes id es'.scopes = SOME (pop_name_entry entry vs) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem) /\
  t.vs_memory = (mstore off (n2w (LENGTH vs-1)) s).vs_memory /\
  tn.t_mem = dirty DIFF {i | off <= i /\ i < off+32} /\
  lookup_var out t = SOME (n2w (off+32+(LENGTH vs-1)*type_memory_size tv)) /\
  off+32+(LENGTH vs-1)*type_memory_size tv < dimword(:256) /\
  ptr_covers G tn out t (type_memory_size tv) ==>
  ptr_vv_ok cx ann
    (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs-1))]))
    (LocatedValue ann (mk_ptr (Var out) LocMemory)) es' G tn t
Proof
  strip_tac >>
  `read_result cx (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs-1))])) es' =
    (INL (LAST vs),es')` by (irule read_result_pop_name >> metis_tac[]) >>
  `val_wf tv (LAST vs)` by
    (`LENGTH vs-1 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
     simp[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1] >>
     metis_tac[elems_val_wf_EL]) >>
  `val_store_size tv (LAST vs) <= type_memory_size tv` by
    metis_tac[val_store_size_le] >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory tv (LAST vs) (off+32+(LENGTH vs-1)*type_memory_size tv) mem` by
    metis_tac[pop_local_robust_last] >>
  simp[ptr_vv_ok_def, mk_ptr_def] >>
  conj_tac >- gvs[ptr_covers_def] >>
  simp[ptr_mem_ok_def, eval_operand_def] >>
  gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_MONO_ADD]
QED
