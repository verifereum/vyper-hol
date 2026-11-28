(* Sparse read boundary for the selected-default slice.  Syntactic occurrence
   selects a key; it is not evidence that the interpreter reached that key. *)
Theory bodyIntCallDefaultAccessMods
Ancestors
  bodyFullPreds bodyFullPredsMods bodyFullPostsMods bodyInvSplit stateRelProj
  loweringStateRelDefs supportedExprTraverse exprLowering
  vyperStoragePlaceProvenance vyperStorageLayoutSafety vyperState
  list pair alist finite_map words

(* Package pointwise facts as absence of a bad qualified occurrence, using
   the same traversal for raw expressions and substituted expressions. *)
Theorem default_access_occurrence[local]:
  (!p e q. (!x. p x <=> ?ty owner id. x = TopLevelName ty (owner,id) /\ q owner id) ==>
    (supported_expr_exists p e <=> ?owner id. q owner id /\
      supported_expr_exists (\x. ?ty. x = TopLevelName ty (owner,id)) e)) /\
  (!p t q. (!x. p x <=> ?ty owner id. x = TopLevelName ty (owner,id) /\ q owner id) ==>
    (supported_target_exists p t <=> ?owner id. q owner id /\
      supported_target_exists (\x. ?ty. x = TopLevelName ty (owner,id)) t)) /\
  (!p es q. (!x. p x <=> ?ty owner id. x = TopLevelName ty (owner,id) /\ q owner id) ==>
    (supported_exprs_exists p es <=> ?owner id. q owner id /\
      supported_exprs_exists (\x. ?ty. x = TopLevelName ty (owner,id)) es)) /\
  (!p opt q. (!x. p x <=> ?ty owner id. x = TopLevelName ty (owner,id) /\ q owner id) ==>
    (supported_opt_exists p opt <=> ?owner id. q owner id /\
      supported_opt_exists (\x. ?ty. x = TopLevelName ty (owner,id)) opt)) /\
  (!p fs q. (!x. p x <=> ?ty owner id. x = TopLevelName ty (owner,id) /\ q owner id) ==>
    (supported_fields_exists p fs <=> ?owner id. q owner id /\
      supported_fields_exists (\x. ?ty. x = TopLevelName ty (owner,id)) fs))
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  rw[supported_expr_exists_def] >>
  qpat_assum `!x. p x <=> ?ty owner id. _` (fn h =>
    rpt (qpat_x_assum `!q. (!x. _ <=> ?ty owner id. _ /\ q owner id) ==> _`
      (qspec_then `q` (fn ih => assume_tac (MP ih h))))) >>
  fs[] >> metis_tac[]
QED

Theorem default_slice_qualified_occurrence_mods:
  supported_exprs_exists (\e. ?ty owner id. e = TopLevelName ty (owner,id) /\ P owner id) es <=>
  ?owner id. P owner id /\ supported_exprs_exists (\e. ?ty. e = TopLevelName ty (owner,id)) es
Proof
  irule (List.nth (CONJUNCTS default_access_occurrence,2)) >> simp[]
QED

Theorem raw_default_const_read[local]:
  body_const_cells_agree mods p ed es /\
  ALOOKUP (consts_env_mods mods) (owner,id) = SOME replacement ==>
  lookup_global p owner id es = (INL (PlaceR (ImmutablePlace owner id [])),es)
Proof
  rw[body_const_cells_agree_def] >>
  first_x_assum (qspecl_then [`owner`,`id`,`replacement`] mp_tac) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem default_immutable_read[local]:
  immutable_frame_mods func ce p es s /\
  ALOOKUP ce.ce_modules owner = SOME tops /\
  FLOOKUP (cenv_without_defaults ce tag).ce_module_vars (owner,id) =
    SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables p.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (tv,v) ==>
  immutable_value_admissible tv v /\
  (~ce.ce_is_ctor ==> off + type_memory_size tv <= LENGTH s.vs_data_section) /\
  val_in_memory tv v off (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section) /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv)
       (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section))
Proof
  rw[cenv_without_defaults_def, immutable_frame_mods_def, immutables_rel_mods_def] >>
  first_x_assum drule >> simp[immutables_rel_def] >>
  disch_then $ qspecl_then [`id`,`tv`,`v`,`off`] mp_tac >> simp[]
QED

Theorem default_storage_read[local]:
  stmt_state_rel H ctx func ce p es s /\
  lookup_global p owner id es = (INL (PlaceR (StoragePlace tr slot tv)),es') ==>
  FLOOKUP (cenv_without_defaults ce tag).ce_module_vars (owner,id) =
    SOME (if tr then TransientLoc slot else StorageLoc slot)
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_vars_rels >>
  drule lookup_global_storage_region >>
  simp[declared_storage_region_def, AllCaseEqs()] >>
  strip_tac >> gvs[resolve_hashmap_leaf_def] >>
  rename1 `StorageVarDecl transient _` >>
  Cases_on `transient` >> gvs[cenv_without_defaults_def] >>
  fs[storage_vars_rel_def, transient_vars_rel_def, var_decl_transient_def] >>
  first_x_assum drule_all >> simp[]
QED

(* No state relation at a selected-module pin is needed.  The raw read
   comes from the cell certificate; the compiled reads use owner-key
   metadata and the immutable/slot projections of the caller packet. *)
Theorem default_slice_access_frame_mods:
  body_const_cells_agree mods p ed es /\
  immutable_frame_mods func ce p es s /\ stmt_state_rel H ctx func ce p es s /\
  (!owner id off. supported_exprs_exists (\e. ?ty. e = TopLevelName ty (owner,id)) ds /\
    FLOOKUP (cenv_without_defaults ce tag).ce_module_vars (owner,id) =
      SOME (ImmutableLoc off) ==>
    ?tops. ALOOKUP ce.ce_modules owner = SOME tops) ==>
  (!owner id replacement.
    supported_exprs_exists (\e. ?ty. e = TopLevelName ty (owner,id)) raw /\
    ALOOKUP (consts_env_mods mods) (owner,id) = SOME replacement ==>
    lookup_global p owner id es = (INL (PlaceR (ImmutablePlace owner id [])),es)) /\
  (!owner id off imms tv v.
    supported_exprs_exists (\e. ?ty. e = TopLevelName ty (owner,id)) ds /\
    FLOOKUP (cenv_without_defaults ce tag).ce_module_vars (owner,id) =
      SOME (ImmutableLoc off) /\
    ALOOKUP es.immutables p.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (tv,v) ==>
    immutable_value_admissible tv v /\
    (~ce.ce_is_ctor ==> off + type_memory_size tv <= LENGTH s.vs_data_section) /\
    val_in_memory tv v off (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section) /\
    immutable_value_bytes_rel tv v
      (mem_bytes_at off (type_memory_size tv)
        (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section))) /\
  (!owner id tr slot tv es'.
    supported_exprs_exists (\e. ?ty. e = TopLevelName ty (owner,id)) ds /\
    lookup_global p owner id es = (INL (PlaceR (StoragePlace tr slot tv)),es') ==>
    FLOOKUP (cenv_without_defaults ce tag).ce_module_vars (owner,id) =
      SOME (if tr then TransientLoc slot else StorageLoc slot))
Proof
  strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> drule_all raw_default_const_read >> simp[])
  >- (rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      drule_all default_immutable_read >> simp[])
  >> rpt strip_tac >> drule_all default_storage_read >> simp[]
QED
