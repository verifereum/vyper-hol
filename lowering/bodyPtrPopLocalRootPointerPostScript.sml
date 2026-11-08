Theory bodyPtrPopLocalRootPointerPost
Ancestors
  bodyPtrPopLocalRootPost bodyPtrPopLocalRootSemanticPost bodyPtrPopLocalRootEntry
  rawCallBufferPtr appendStorageGhostPtr stmtFragPtr
  exprLowering exprSimPop compileEnv context venomState ptrDiscipline
  finite_map words list pred_set

Theorem pop_local_pointer_endpoint:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ 32 <= sz /\
  entry.type = ArrayTV tv (Dynamic cap) /\
  entry.value = ArrayV (DynArrayV vs) /\
  vs <> [] /\ elems_val_wf vs tv /\ LENGTH vs <= cap /\
  lookup_scopes id ee.scopes = SOME (pop_name_entry entry vs) /\
  (!name. name <> id ==> lookup_scopes name ee.scopes = lookup_scopes name es.scopes) /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = (mstore (w2n a) (n2w (LENGTH vs-1)) s).vs_memory /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  type_memory_bytes cenv ann = type_memory_size tv /\
  lookup_var out t = SOME (n2w (w2n a+32+(LENGTH vs-1)*type_memory_size tv)) /\
  w2n a+32+(LENGTH vs-1)*type_memory_size tv < dimword(:256) /\
  ptr_covers G' tn' out t (type_memory_size tv) ==>
  ghost_inv d cenv cx (ee with gas_obs := gs) G' tn' t /\
  ptr_vv_ok cx ann
    (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs-1))]))
    (LocatedValue ann (mk_ptr (Var out) LocMemory)) (ee with gas_obs := gs) G' tn' t /\
  ptr_buf_ok cenv (Pop ann (NameTarget id)) (Var out) G' t /\
  ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  drule_all pop_local_endpoint_ghost >> strip_tac >>
  drule_all pop_local_robust_layout >> strip_tac >>
  `tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} = tn.t_mem` by
    (simp[EXTENSION] >> metis_tac[]) >>
  `ptr_vv_ok cx ann
    (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs-1))]))
    (LocatedValue ann (mk_ptr (Var out) LocMemory)) ee G' tn' t` by
    (irule pop_local_returned_ptr_vv >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[ghost_inv_gas_obs, pop_local_memory_ptr_gas_obs] >> conj_tac
  >- (irule ptr_buf_ok_from_covers >> goal_assum (drule_at Any) >>
      simp[lowered_value_type_def, vyperASTTheory.expr_type_def]) >>
  irule ghost_kept_old_transport >> simp[]
QED
