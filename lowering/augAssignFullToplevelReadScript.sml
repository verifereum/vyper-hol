(* A scalar observed root chooses one read value for all valid horizons. *)
Theory augAssignFullToplevelRead
Ancestors
  augAssignFullLoad stmtSimAugAssignStorage gasOutcomeFull
  bodyPtrDefs accountsRelProps vyperStorageFootprint vyperState
  vyperTyping vyperValue loweringPosts compileEnv list

Theorem observed_storage_toplevel_clean_read_full:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  storage_trace_domain cx st0
    (es.storage_trace ++ [StorageRoot tr slot tvt]) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  well_formed_type_value tvt /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  0 < type_slot_size tvt ==>
  ?cur.
    read_storage_slot cx tr (n2w slot) tvt es = (INL cur,es) /\
    (!H. valid_horizon cx st0 H
          (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
      storage_holds cx tr ty (Value cur) (n2w slot) es s /\
      key_taint (if tr then tn.t_trans else tn.t_stor) (n2w slot) = {})
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon
    (es.storage_trace ++ [StorageRoot tr slot tvt])` >>
  `valid_horizon cx st0 H0
     (es.storage_trace ++ [StorageRoot tr slot tvt])` by
    fs[storage_trace_domain_def, Abbr `H0`] >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `MEM (tr,n2w slot,tvt) (FST H0)` by
    fs[valid_horizon_def, storage_observations_ok_def,
       storage_trace_regions_def] >>
  `storage_well_formed_on cx es (FST H0)` by metis_tac[] >>
  drule_all observed_region_read >> strip_tac >>
  qexists_tac `v` >> simp[] >> qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H)` by
    fs[valid_horizon_def, storage_observations_ok_def,
       storage_trace_regions_def] >>
  `stmt_state_rel H ctx func cenv cx es s /\
   storage_well_formed_on cx es (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx es G tn s` by metis_tac[] >>
  conj_tac
  >- (irule declared_storage_holds_value >> metis_tac[]) >>
  `!st. storage_read_live H tr st (n2w slot) tvt` by
    metis_tac[observed_storage_region_read_live] >>
  irule (INST_TYPE [alpha |-> ``:256``] live_storage_head_clean_at) >>
  qexistsl_tac [`DF H`, `H`, `cenv`, `cx`, `lo`, `s`, `tvt`] >>
  fs[ghost_inv_at_def]
QED
