(* The existing encoded-leaf semantics accepts an actual copied live prefix. *)
Theory assignStorageSubregionSemanticPtr
Ancestors
  placeStoreStorage assignBasePtrStorageSemantic assignBasePtrStorageLoop
  vyperPlaceFrames vyperStorageBackend storageCopyLive loweringStateRelDefs
  exprLoweringProps stmtSimStoreCopy exprSimDefs bodyPtrDefs compileEnv venomState words arithmetic list

Theorem assign_store_subregion_model_state:
  expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s0 /\
  declared_storage_region cx mid id subs = SOME (tr,root,rtv) /\
  storage_subregion rtv path delta tv /\ w2n k = w2n root+delta /\
  0 < type_slot_size tv /\ copied <= type_slot_size tv /\
  w2n k+type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n b) s0.vs_memory /\ encode_value tv v = SOME writes /\
  w2n b+32*(copied-1) < dimword (:256) /\
  (!i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes (get_storage cx es tr)) (w2n k) tv i c ==>
    i < w2n k+copied) /\
  write_place cx (StoragePlace tr k tv) v es = (INL (),es') ==>
  stmt_state_rel ctx func cenv cx es'
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k s0 copied)
Proof
  strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def,state_rel_def] >>
  `es' = set_storage cx es tr (apply_writes k writes (get_storage cx es tr))` by
    gvs[write_storage_place_eq] >>
  `!i c. i < type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes (get_storage cx es tr))
       (w2n k) tv (w2n k+i) c ==>
    i < copied /\
    EL c (word_to_bytes (lookup_storage (n2w (w2n k+i))
      (apply_writes k writes (get_storage cx es tr))) T) =
    EL c (word_to_bytes (mload (w2n (b+n2w i*32w)) s0) T)` by
    (rpt strip_tac >>
     `i < copied` by
       (qpat_x_assum `!i c. _` (qspecl_then [`w2n (k:bytes32)+i`,`c`] mp_tac) >>
        simp[]) >> simp[] >>
     `mload (w2n (b+n2w i*32w)) s0 =
        mem_word_at (w2n b+32*i) s0.vs_memory` by
       (irule assign_base_store_source_word >> qexists_tac `copied` >> simp[]) >>
     simp[] >>
     mp_tac (Q.SPECL [`tv`,`v`,`w2n (b:bytes32)`,`s0.vs_memory`,
       `k`,`writes`,`get_storage cx es tr`,`i`,`c`]
       encode_value_memory_live) >> simp[] >> metis_tac[ADD_COMM]) >>
  `stmt_state_rel ctx func cenv cx es'
    (FOLDL (\t i. (if tr then tstore else sstore)
      (n2w (w2n k+i)) (mload (w2n (b+n2w i*32w)) s0) t)
      s0 (COUNT_LIST copied))` by
    (mp_tac (SIMP_RULE bool_ss [n2w_w2n] (BETA_RULE (Q.SPECL [`cenv`,`cx`,`env`,`es`,`ctx`,`func`,`s0`,
       `mid`,`id`,`subs`,`tr`,`root`,`rtv`,`path`,`delta`,`tv`,
       `w2n (k:bytes32)`,`writes`,`v`,`copied`,
       `\i. mload (w2n ((b:bytes32)+n2w i*32w)) s0`]
       place_store_encoded_leaf_state))) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  Cases_on `tr` >> simp[store_copy_prefix_def,GSYM word_add_n2w]
QED
