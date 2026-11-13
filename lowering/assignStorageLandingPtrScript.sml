(* A copied live prefix lands in the real storage child's source state. *)
Theory assignStorageLandingPtr
Ancestors
  assignStorageSubregionSemanticPtr assignSubregionPtrStoragePrefix
  assignBasePtrStorageSemantic assignBasePtrStorageGhost assignBasePtrStorageLoop
  exprLoweringProps vyperStoragePlaceRegion
  vyperPlaceFrames bodyPtrDefs exprSimDefs compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs venomState words arithmetic

Theorem storage_prefix_counted_landing_ptr:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 copied s tn /\
  execution_frame s = execution_frame (store_copy_prefix
    (if tr then LocTransient else LocStorage) b k s0 copied) /\
  declared_storage_region cx mid id subs = SOME (tr,root,rtv) /\
  storage_subregion rtv path delta tv /\ w2n k = w2n root+delta /\
  w2n root+type_slot_size rtv <= dimword (:256) /\
  (!mid' id' subs' root' rtv'.
    declared_storage_region cx mid' id' subs' = SOME (tr,root',rtv') /\
    (root',rtv') <> (root,rtv) ==>
    ranges_disjoint (w2n root) (type_slot_size rtv)
                    (w2n root') (type_slot_size rtv')) /\
  0 < type_slot_size tv /\ copied <= type_slot_size tv /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  w2n b+32*(copied-1) < dimword (:256) /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
    val_in_memory tv v (w2n b) m) /\
  (!st i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
    i < w2n k+copied) /\
  (!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
    w2n k+copied <= w2n q /\ w2n q < w2n k+type_slot_size tv ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n k) tv (w2n q) c) /\
  write_place cx (StoragePlace tr k tv) v es = (INL (),es') /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x) /\
    lookup_var x s = lookup_var x s0) ==>
  stmt_state_rel ctx func cenv cx es' s /\
  ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >>
  `w2n k+type_slot_size tv <= dimword (:256)` by
    (drule storage_subregion_bounds >> strip_tac >> decide_tac) >>
  `val_in_memory tv v (w2n b) s0.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `s0.vs_call_ctx.cc_address = cx.txn.target /\ stor_taint_ok cx tn0 s0` by
    fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def,ghost_inv_def] >>
  `stor_taint_ok cx tn s` by
    (irule assign_base_store_subregion_prefix_stor_taint_ok >>
     goal_assum (drule_at (Pat `assign_base_store_frame _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
     simp[] >> qexistsl_tac [`id`,`mid`,`subs`] >>
     conj_tac
     >- (qpat_x_assum `!st i c. w2n k <= i /\ _ ==> _`
           (qspec_then `if tr then contract_transient s0 else contract_storage s0` mp_tac) >>
         qpat_x_assum `w2n k = w2n root+delta` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> strip_tac >>
         asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
     first_assum ACCEPT_TAC) >>
  `stmt_state_rel ctx func cenv cx es'
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k s0 copied)` by
    (mp_tac (SPEC_ALL assign_store_subregion_model_state) >>
     (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
     asm_rewrite_tac[]) >>
  `stmt_state_rel ctx func cenv cx es' s` by
    (irule assign_base_store_endpoint_state >>
     goal_assum (drule_at (Pat `execution_frame _ = _`)) >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     simp[assign_base_storage_model_lookup]) >>
  `es'.scopes = es.scopes` by metis_tac[write_storage_place_scopes] >>
  simp[] >> irule assign_base_store_ghost_post >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  qexistsl_tac [`b`,`k`,`if tr then LocTransient else LocStorage`,`copied`] >>
  first_assum ACCEPT_TAC
QED
