(* Bytestring capacity widening leaves only a dead destination tail. *)
Theory assignBytesStorageLandingPtr
Ancestors
  assignStorageLandingPtr assignStorageBytesPrefixPtr assignBasePtrStorageTaint
  assignBasePtrStorageSemantic assignBasePtrStorageLoop assignBasePtrStorageGhost
  exprLoweringProps vyperStoragePlaceRegion bodyPtrDefs loweringStateRelDefs
  valueEncodingProps valueEncoding valueEncodingDefs venomState words arithmetic

Theorem bytes_storage_counted_landing_ptr:
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
  (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
  mload (w2n b) s0 = n2w len /\ len < dimword (:256) /\
  0 < copied /\ len <= 32*(copied-1) /\
  write_place cx (StoragePlace tr k tv) v es = (INL (),es') /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x) /\
    lookup_var x s = lookup_var x s0) ==>
  stmt_state_rel ctx func cenv cx es' s /\
  ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n k+type_slot_size tv <= dimword (:256)` by
    (drule storage_subregion_bounds >> strip_tac >> decide_tac) >>
  `val_in_memory tv v (w2n b) s0.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mem_word_at (w2n b) s0.vs_memory = n2w len` by
    simp[mem_word_at_eq_mload] >>
  `!st i c. w2n k <= i /\ i < w2n k+type_slot_size tv /\ c<32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
    i < w2n k+copied` by
    (gen_tac >> mp_tac (Q.INST [`off` |-> `w2n (b:bytes32)`,
       `mem` |-> `s0.vs_memory`] (SPEC_ALL assign_store_bytes_live_prefix)) >>
     (impl_tac >- asm_rewrite_tac[]) >> asm_rewrite_tac[]) >>
  `s0.vs_call_ctx.cc_address = cx.txn.target /\ stor_taint_ok cx tn0 s0` by
    fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def,ghost_inv_def] >>
  `!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) ==>
    storage_dead cx tr (if tr then contract_transient s0 else contract_storage s0)
      (w2n q) c` by
    (rpt strip_tac >> irule assign_base_store_initial_selected_dead >>
     simp[] >> qexists_tac `tn0` >> fs[ghost_inv_def]) >>
  `lookup_storage k (if tr then contract_transient s else contract_storage s) =
    n2w len` by
    (mp_tac (Q.INST [`n` |-> `copied`,`q` |-> `k`]
       (SPEC_ALL assign_base_store_frame_lookup)) >>
     (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
     simp[WORD_MULT_CLAUSES,WORD_ADD_0]) >>
  `!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
    w2n k+copied <= w2n q /\ w2n q < w2n k+type_slot_size tv ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n k) tv (w2n q) c` by
    (mp_tac (Q.INST [`start` |-> `w2n (k:bytes32)`,
       `initial` |-> `if tr then contract_transient s0 else contract_storage s0`,
       `final` |-> `if tr then contract_transient s else contract_storage s`,
       `old` |-> `if tr then tn0.t_trans else tn0.t_stor`]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:256``]
         assign_store_bytes_retained_tail_dead))) >>
     (impl_tac >- asm_rewrite_tac[n2w_w2n]) >> asm_rewrite_tac[]) >>
  mp_tac (SPEC_ALL storage_prefix_counted_landing_ptr) >>
  (impl_tac >- asm_rewrite_tac[]) >> asm_rewrite_tac[]
QED
