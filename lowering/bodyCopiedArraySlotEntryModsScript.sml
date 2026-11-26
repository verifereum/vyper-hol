(* Read the slot-backed base at the cursor after the outer ALLOCA. *)
Theory bodyCopiedArraySlotEntryMods
Ancestors
  bodyCopiedArrayMaterializedEntryMods bodyCopiedArrayCutDefsMods
  bodyCopySlotRhsEndpointMods bodyFullPostsMods exprLowering compileEnv context
  gasExplicitSites

Theorem copied_array_slot_store_entry_mods:
  copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (q,w) /\
  ci_mono sa sm /\ ci_mono sm k /\ bvv = LocatedValue tag p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  ?t Gl tl sw. copied_store_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (l,t,Gl,tl) (src,sw,sc,cvv) (q,w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (drule_then (drule_then irule))
    (REWRITE_RULE [AND_IMP_INTRO] copied_array_materialized_store_entry_mods) >>
  qpat_x_assum `bvv = _` SUBST_ALL_TAC >>
  qpat_x_assum `copied_alloc_cut_mods _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [copied_alloc_cut_mods_def]) >>
  `tag = ArrayT et bd` by fs[vv_type_def] >>
  qpat_x_assum `tag = _` SUBST_ALL_TAC >>
  qpat_assum `copied_array_type_mods _ _ _`
    (strip_assume_tac o REWRITE_RULE [copied_array_type_mods_def]) >>
  qpat_assum `copied_cursor_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [copied_cursor_mods_def]) >>
  qpat_assum `copied_parent_frame_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [copied_parent_frame_mods_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post_mods H ctx fn ce cx obj es sa k s0 mid raw (LocatedValue (ArrayT et bd) p) a /\
    ghost_inv_at_mods (DF H) lo d ce cx mid Ga ta a` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at k x` by fs[vv_operand_def] >>
  `~is_word_type (ArrayT et bd)` by simp[is_word_type_def] >>
  `evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME atv /\
   type_memory_bytes ce (post_value_type ce obj) = type_memory_size atv` by simp[] >>
  drule_all copy_slot_rhs_endpoint_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`] mp_tac) >>
  simp_tac bool_ss [AND_IMP_INTRO]
QED
