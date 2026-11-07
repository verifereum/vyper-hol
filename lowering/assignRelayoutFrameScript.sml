(* Restore an existing local after a multi-block typed copy. *)
Theory assignRelayoutFrame
Ancestors
  assignRelayoutSource annassignRelayoutBounds localMemoryStorePath
  stmtSimAssignStore placeMemoryCopyEffect exprLoweringProps
  localPtrsProps compileEnv venomState venomMemDefs vyperLookup

Theorem stmt_state_rel_control[local]:
  stmt_state_rel ctx func cenv cx es
    (s with <|vs_prev_bb := prev; vs_current_bb := bb; vs_inst_idx := idx|>) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  `fmp_room ctx func
    (s with <|vs_prev_bb := prev; vs_current_bb := bb; vs_inst_idx := idx|>) <=>
   fmp_room ctx func s` by (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def, accounts_rel_def,
       immutable_base_zero_alt]
QED

Theorem stmt_state_rel_write_local_copy_effect:
  !ctx func cenv cx es s t sa sb id p cap dw pre scope entry rest v.
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre,scope,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
    lookup_var p s = SOME dw /\ local_ptrs_reserved cenv sa /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size entry.type) /\
    val_wf entry.type v /\ val_in_memory entry.type v (w2n dw) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (scope |+ (id, entry with <|value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `type_memory_size entry.type <= cap` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     qpat_x_assum `!name entry' p' sz. _` (qspecl_then [`id`,`entry`,`p`,`cap`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `local_region cenv es.scopes s id (w2n dw) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  drule typed_copy_effect_record >>
  simp[venom_state_component_equality] >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule local_copy_immutables >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `type_memory_size entry.type` >> simp[] >>
     fs[typed_copy_effect_def] >> first_assum ACCEPT_TAC) >>
  `!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> irule typed_copy_effect_lookup >> goal_assum (drule_at Any) >>
     fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  qabbrev_tac `u = t with <|vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>` >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es u` by
    (gvs[Abbr `u`, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (scope |+ (id, entry with <|value := v; popped := []|>)) :: rest) u` by
    (irule stmt_state_rel_write_local >>
     simp[] >>
     qexistsl_tac [`s`,`dw`] >>
     gvs[Abbr `u`, lookup_var_def, venom_state_component_equality,
         typed_copy_effect_def] >> first_assum ACCEPT_TAC) >>
  fs[Abbr `u`, stmt_state_rel_control]
QED

Theorem local_memory_relayout_store_path:
  !ctx func cenv cx es s id p cap pre scope entry rest v src dty sty
   sa sb sw dw dtv stv.
    compile_store_memory cenv src (Var p) dty sty sa = ((),sb) /\
    ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname,fty,sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ entry.type = dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre,scope,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
        (es with scopes := pre ++
          (scope |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
      typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all compile_store_memory_relayout_effect >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  irule stmt_state_rel_write_local_copy_effect >>
  simp[] >> qexistsl_tac [`dw`,`s`,`sa`,`sb`] >> gvs[]
QED
