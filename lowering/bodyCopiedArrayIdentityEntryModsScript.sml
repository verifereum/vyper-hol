Theory bodyCopiedArrayIdentityEntryMods
Ancestors
  bodyCopiedArrayCutDefsMods assignBasePtrBoundary stateRelProj exprLoweringProps
  exprSimMemDefs loweringPosts bodyFullPostsMods bodyPtrDefs exprLowering
  compileEnv context vyperTypeSystem vyperStorageFootprint words

(* Neither kind of identity unwrap runs a read, even at size zero. *)
Theorem copied_identity_unwrap[local]:
  vv_type vv = ArrayT et bd /\
  ((?t op. vv = StackValue t op) \/ vv_location vv = SOME LocMemory) /\
  unwrap_value ce vv k = (src,l) ==>
  src = vv_operand vv /\ l = k
Proof
  Cases_on `vv` >>
  simp[vv_type_def,vv_location_def,vv_operand_def,unwrap_value_def,
       comp_return_def,is_word_type_def] >>
  strip_tac >> gvs[comp_return_def,is_word_type_def]
QED

Theorem copied_identity_source[local]:
  ((?t op. vv = StackValue t op) \/ vv_location vv = SOME LocMemory) /\
  vv_holds_mods ce cx (ArrayT et bd) raw vv mid a /\
  ptr_vv_ok cx (ArrayT et bd) raw vv mid Ga ta a /\
  read_result cx raw mid = (INL saved,mid) ==>
  (?sw. eval_operand (vv_operand vv) a = SOME sw) /\
  ptr_mem_ok cx (ArrayT et bd) saved (vv_operand vv) Ga ta a /\
  op_taint ta (vv_operand vv) = {}
Proof
  Cases_on `vv` >>
  simp[vv_location_def,vv_operand_def,vv_holds_mods_def,vv_holds_def,expr_val_rel_def,
       ptr_vv_ok_def,ptr_val_ok_def,is_word_type_def] >>
  strip_tac >> gvs[]
QED

Theorem copied_identity_source_bound[local]:
  ((?t op. vv = StackValue t op) \/ vv_location vv = SOME LocMemory) /\
  vv_store_bound cx (ArrayT et bd) (ArrayT et bd) mid raw vv a /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
  eval_operand (vv_operand vv) a = SOME sw /\
  type_memory_size atv <> 0 ==>
  w2n sw + type_memory_size atv <= a.vs_alloca_next
Proof
  Cases_on `vv` >>
  simp[vv_location_def,vv_operand_def,vv_store_bound_def,is_word_type_def] >>
  strip_tac >> gvs[] >>
  qpat_assum `!tvt w. _ ==> _` (drule_all_then strip_assume_tac) >> fs[]
QED

Theorem copied_array_identity_store_entry_mods:
  copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (q,w) /\
  ((?t op. bvv = StackValue t op) \/ vv_location bvv = SOME LocMemory) ==>
  ?sw. copied_store_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (l,a,Ga,ta) (src,sw,sc,cvv) (q,w)
Proof
  disch_then (CONJUNCTS_THEN2
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_alloc_cut_mods_def])
    assume_tac) >>
  drule_all_then (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) copied_identity_unwrap >>
  `storage_trace_domain cx st0 mid.storage_trace` by
    fs[copied_parent_frame_mods_def] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
  `post_value_type ce obj = ArrayT et bd /\ lowered_value_type ce obj = ArrayT et bd /\
   read_result cx raw mid = (INL saved,mid) /\
   evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
   type_memory_bytes ce (ArrayT et bd) = type_memory_size atv` by
    fs[copied_array_type_mods_def] >>
  qpat_x_assum `post_value_type ce obj = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `lowered_value_type ce obj = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all_then strip_assume_tac copied_identity_source >>
  `ptr_buf_ok ce obj (vv_operand bvv) Ga a` by
    (Cases_on `bvv` >> fs[vv_location_def,vv_operand_def]) >>
  `a.vs_alloca_next < dimword (:256)` by
    (drule_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt) stmt_state_rel_alloca_room) >>
  `type_memory_size atv <> 0 ==>
     (?x. vv_operand bvv = Var x /\ ptr_covers Ga ta x a (type_memory_size atv)) /\
     w2n sw + type_memory_size atv <= a.vs_alloca_next /\
     a.vs_alloca_next < dimword (:256)` by
    (strip_tac >> rpt conj_tac
     >- (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
         goal_assum (drule_at Any) >> conj_tac
         >- (qexists_tac `sw` >> first_assum ACCEPT_TAC) >>
         qexistsl [`ce`,`obj`] >> simp[])
     >- drule_all_then ACCEPT_TAC copied_identity_source_bound >>
     first_assum ACCEPT_TAC) >>
  qexists_tac `sw` >> pure_rewrite_tac[copied_store_cut_mods_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
