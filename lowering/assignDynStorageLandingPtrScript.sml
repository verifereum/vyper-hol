(* The actual counted dynamic write lands in both semantic and ghost relations. *)
Theory assignDynStorageLandingPtr
Ancestors
  assignSubregionPtrStoragePrefix assignStoragePrefixLivePtr assignSubregionPtrStorageGhost
  exprLoweringProps vyperStoragePlaceRegion placeStoreCopyPath valueEncodingProps
  assignBasePtrStorageGhost assignBasePtrStorageSemantic assignBasePtrStorageLoop
  placeDynStoreState vyperPlaceFrames bodyPtrDefs compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs vyperValue vyperTyping venomState
  words arithmetic pred_set

Theorem dyn_storage_counted_landing_ptr:
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  assign_base_store_frame (if tr then LocTransient else LocStorage)
    b k s0 tn0 (1+LENGTH vs*type_slot_size et) s tn /\
  execution_frame s = execution_frame (store_copy_prefix
    (if tr then LocTransient else LocStorage) b k s0 (1+LENGTH vs*type_slot_size et)) /\
  declared_storage_region cx mid id subs = SOME (tr,root,rtv) /\
  storage_subregion rtv path delta (ArrayTV et (Dynamic cap)) /\
  w2n k = w2n root+delta /\ w2n root+type_slot_size rtv <= dimword (:256) /\
  (!mid' id' subs' root' rtv'.
    declared_storage_region cx mid' id' subs' = SOME (tr,root',rtv') /\
    (root',rtv') <> (root,rtv) ==>
    ranges_disjoint (w2n root) (type_slot_size rtv)
                    (w2n root') (type_slot_size rtv')) /\
  well_formed_type_value (ArrayTV et (Dynamic cap)) /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  encode_value (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes /\
  w2n b+32*(1+LENGTH vs*type_slot_size et) < dimword (:256) /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
    val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n b) m) /\
  write_place cx (StoragePlace tr k (ArrayTV et (Dynamic cap)))
    (ArrayV (DynArrayV vs)) es = (INL (),es') /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x) /\
    lookup_var x s = lookup_var x s0) ==>
  stmt_state_rel ctx func cenv cx es' s /\
  ghost_inv d cenv cx es' G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >>
  `val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs))
     (w2n b) s0.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `LENGTH vs <= cap /\ LENGTH vs < dimword (:256)` by
    (fs[value_has_type_def,well_formed_type_value_def] >> decide_tac) >>
  `type_slot_size (ArrayTV et (Dynamic cap)) = 1+cap*type_slot_size et` by
    simp[type_slot_size_def] >>
  `1+LENGTH vs*type_slot_size et <= type_slot_size (ArrayTV et (Dynamic cap))` by
    (simp[] >> simp[LE_MULT_RCANCEL]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n k+type_slot_size (ArrayTV et (Dynamic cap)) <= dimword (:256)` by decide_tac >>
  `w2n b+32*((1+LENGTH vs*type_slot_size et)-1) < dimword (:256)` by decide_tac >>
  `s0.vs_call_ctx.cc_address = cx.txn.target /\ stor_taint_ok cx tn0 s0` by
    fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def,ghost_inv_def] >>
  `!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) ==>
    storage_dead cx tr (if tr then contract_transient s0 else contract_storage s0)
      (w2n q) c` by
    (rpt strip_tac >> irule assign_base_store_initial_selected_dead >>
     simp[] >> qexists_tac `tn0` >> simp[]) >>
  `mload (w2n b) s0 = n2w (LENGTH vs)` by
    fs[val_in_memory_def,mem_word_at_eq_mload] >>
  `lookup_storage k (if tr then contract_transient s else contract_storage s) =
    n2w (LENGTH vs)` by
    (mp_tac (Q.INST [`b` |-> `b`,`k` |-> `k`,`s0` |-> `s0`,
       `tn0` |-> `tn0`,`n` |-> `1+LENGTH (vs:value list)*type_slot_size et`,
       `s` |-> `s`,`tn` |-> `tn`,`tr` |-> `tr`,`q` |-> `k`]
       (SPEC_ALL assign_base_store_frame_lookup)) >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac)) >>
     simp[WORD_MULT_CLAUSES,WORD_ADD_0]) >>
  `!i c. w2n k <= i /\ i < w2n k+type_slot_size (ArrayTV et (Dynamic cap)) /\
     c<32 /\ ~dead_bytes (apply_writes k writes
       (if tr then contract_transient s0 else contract_storage s0))
       (w2n k) (ArrayTV et (Dynamic cap)) i c ==>
     i < w2n k+(1+LENGTH vs*type_slot_size et)` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`et` |-> `et`,`cap` |-> `cap`,`vs` |-> `vs`,
       `off` |-> `w2n (b:bytes32)`,`mem` |-> `s0.vs_memory`,
       `writes` |-> `writes`,`k` |-> `k`,
       `st` |-> `if tr then contract_transient s0 else contract_storage s0`]
       (SPEC_ALL assign_store_dynarray_live_prefix)) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then (qspecl_then [`i`,`c`] mp_tac) >>
     full_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
  `!q c. (q,c) IN (if tr then tn0.t_trans else tn0.t_stor) /\
     w2n k+(1+LENGTH vs*type_slot_size et) <= w2n q /\
     w2n q < w2n k+type_slot_size (ArrayTV et (Dynamic cap)) ==>
     dead_bytes (if tr then contract_transient s else contract_storage s)
       (w2n k) (ArrayTV et (Dynamic cap)) (w2n q) c` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`cx`,`tr`,
       `if tr then contract_transient s0 else contract_storage s0`,
       `if tr then contract_transient s else contract_storage s`,
       `if tr then tn0.t_trans else tn0.t_stor`,`w2n (k:bytes32)`,
       `LENGTH (vs:value list)`,`et`,`cap`]
       (Q.GENL [`cx`,`tr`,`initial`,`final`,`old`,`start`,`n`,`et`,`cap`]
         (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] dynarray_retained_tail_dead)))) >>
     (impl_tac >- asm_rewrite_tac[n2w_w2n]) >>
     disch_then (qspecl_then [`q`,`c`] mp_tac) >>
     disch_then irule >> asm_rewrite_tac[] >> decide_tac) >>
  `stor_taint_ok cx tn s` by
    (irule assign_base_store_subregion_prefix_stor_taint_ok >>
     goal_assum (drule_at (Pat `assign_base_store_frame _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
     simp[] >> qexistsl_tac [`id`,`mid`,`subs`] >> conj_tac
     >- (qpat_x_assum `!i c. w2n k <= i /\ _ ==> _` mp_tac >>
         qpat_x_assum `w2n k = w2n root+delta` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> strip_tac >>
         asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM,type_slot_size_def]) >>
     first_assum ACCEPT_TAC) >>
  `stmt_state_rel ctx func cenv cx es'
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k s0
      (1+LENGTH vs*type_slot_size et))` by
    (`w2n b+32*(1+LENGTH vs*type_slot_size et) <= dimword (:256)` by decide_tac >>
     mp_tac (Q.INST [`ee` |-> `es`,`ff` |-> `es'`,`name` |-> `id`,
       `tv` |-> `rtv`,`q` |-> `s0`] (SPEC_ALL place_dyn_storage_write_state)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     asm_rewrite_tac[]) >>
  `stmt_state_rel ctx func cenv cx es' s` by
    (irule assign_base_store_endpoint_state >>
     goal_assum (drule_at (Pat `execution_frame _ = _`)) >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     simp[assign_base_storage_model_lookup]) >>
  `es'.scopes = es.scopes` by metis_tac[write_storage_place_scopes] >>
  simp[] >> irule assign_base_store_ghost_post >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  qexistsl_tac [`b`,`k`,`if tr then LocTransient else LocStorage`,
    `1+LENGTH (vs:value list)*type_slot_size et`] >> first_assum ACCEPT_TAC
QED
