(* Typed locations for linked writes.  This boundary keeps the source
   declaration and the compile-environment location together. *)
Theory bodyWriteKeyLocationMods
Ancestors
  targetPlaceSim immutableRegionTypingProps linkedStorageMetadataProps
  bodyInvCodeProps bodyInvSplit exprSimHypsDefs bodySim
  vyperSubscriptOverlap vyperTypeContract vyperTypeSystem vyperContext
  compileEnv alist finite_map list pair

Theorem linked_immutable_write_location[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  FLOOKUP env.bare_global_assignable (src,id) = SOME ty /\
  IS_SOME (FLOOKUP cenv.ce_module_vars (src,id)) ==>
  ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off)
Proof
  strip_tac >>
  fs[expr_sim_inv_mods_def, bare_globals_layout_def] >>
  first_assum (qspecl_then [`src`, `id`, `ty`] mp_tac) >>
  simp[optionTheory.IS_SOME_EXISTS] >>
  metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem linked_storage_write_location[local]:
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot ==>
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  strip_tac >>
  irule toplevel_decl_ce_vars >>
  qexistsl_tac [`cx`, `StorageVarDecl tr typ`, `id_str`, `tops`] >>
  simp[loweringStateRelDefsTheory.var_decl_transient_def]
QED

Theorem typed_write_location_mods_L0031:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  storage_vars_rel cenv cx /\
  transient_vars_rel cenv cx /\
  MEM (vyperSubscriptOverlap$WriteAcc
         (vyperSubscriptOverlap$StateRef (src,id)))
      (vyperSubscriptOverlap$accesses_stmt s) /\
  ((?ty.
      FLOOKUP env.bare_globals (src,id) = SOME ty /\
      FLOOKUP env.bare_global_assignable (src,id) = SOME ty /\
      IS_SOME (FLOOKUP cenv.ce_module_vars (src,id))) \/
   (?tr typ id_str slot.
      ALOOKUP mods src = SOME tops /\
      find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str) /\
      lookup_var_slot_from_layout cx tr src id_str = SOME slot)) ==>
  (?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off)) \/
  (?tr slot.
     FLOOKUP cenv.ce_module_vars (src,id) =
       SOME (if tr then TransientLoc (n2w slot)
             else StorageLoc (n2w slot)))
Proof
  strip_tac
  >- (disj1_tac >> metis_tac[linked_immutable_write_location,
                              optionTheory.IS_SOME_EXISTS])
  >> disj2_tac >> qexistsl_tac [`tr`, `slot`] >>
  `get_module_code cx src = SOME tops` by
    (drule_all contract_inv_module_codes >> simp[]) >>
  drule_all linked_storage_write_location >>
  simp[]
QED

Theorem typed_write_location_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  storage_vars_rel cenv cx /\
  transient_vars_rel cenv cx /\
  MEM (vyperSubscriptOverlap$WriteAcc
         (vyperSubscriptOverlap$StateRef (src,id)))
      (vyperSubscriptOverlap$accesses_stmt s) /\
  ((?ty.
      FLOOKUP env.bare_globals (src,id) = SOME ty /\
      FLOOKUP env.bare_global_assignable (src,id) = SOME ty /\
      IS_SOME (FLOOKUP cenv.ce_module_vars (src,id))) \/
   (?tr typ id_str slot.
      ALOOKUP mods src = SOME tops /\
      find_var_decl_by_name id tops = SOME (StorageVarDecl tr typ,id_str) /\
      lookup_var_slot_from_layout cx tr src id_str = SOME slot)) ==>
  (?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off)) \/
  (?tr slot.
     FLOOKUP cenv.ce_module_vars (src,id) =
       SOME (if tr then TransientLoc (n2w slot)
             else StorageLoc (n2w slot)))
Proof
  ACCEPT_TAC typed_write_location_mods_L0031
QED
