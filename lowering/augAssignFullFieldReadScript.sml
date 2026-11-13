(* Choose the field value at the observed trace's own horizon, then keep
   that same value and clean load address at every larger valid horizon. *)
Theory augAssignFullFieldRead
Ancestors
  augAssignStorageFieldSource augAssignFullLoad gasOutcomeFull
  bodyPtrDefs accountsRelProps vyperStorageFootprint vyperState
  vyperTyping vyperValue loweringPosts compileEnv
  list

Theorem observed_storage_field_clean_read_full:
  storage_trace_domain cx st0
    (es.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  well_formed_type_value (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) /\
  evaluate_type (get_tenv cx) ty = SOME ftv /\
  0 < type_slot_size ftv ==>
  ?cur.
    read_storage_slot cx tr (n2w slot + n2w off) ftv es = (INL cur,es) /\
    (!H. valid_horizon cx st0 H
          (es.storage_trace ++ [StorageRoot tr slot (StructTV fs)]) ==>
      storage_holds cx tr ty (Value cur) (n2w slot + n2w off) es s /\
      key_taint (if tr then tn.t_trans else tn.t_stor)
        (n2w slot + n2w off) = {})
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon
    (es.storage_trace ++ [StorageRoot tr slot (StructTV fs)])` >>
  `valid_horizon cx st0 H0
     (es.storage_trace ++ [StorageRoot tr slot (StructTV fs)])` by
    fs[storage_trace_domain_def, Abbr `H0`] >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `MEM (tr,n2w slot,StructTV fs) (FST H0) /\
   regions_consistent (FST H0)` by
    fs[valid_horizon_def, storage_observations_ok_def,
       storage_trace_regions_def] >>
  `storage_well_formed_on cx es (FST H0)` by metis_tac[] >>
  drule_all augassign_storage_field_read >> strip_tac >>
  qexists_tac `cur` >> simp[] >> rpt strip_tac
  >- (first_x_assum irule >>
      `valid_horizon cx st0 H0 es.storage_trace` by metis_tac[] >>
      metis_tac[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `MEM (tr,n2w slot,StructTV fs) (FST H)` by
    fs[valid_horizon_def, storage_observations_ok_def,
       storage_trace_regions_def] >>
  `!st. storage_read_live H tr st (n2w slot + n2w off) ftv` by
    (gen_tac >> irule storage_read_live_field >>
     qexistsl_tac [`fs`, `fld`] >> simp[] >>
     irule observed_storage_region_read_live >> simp[]) >>
  irule (INST_TYPE [alpha |-> ``:256``] live_storage_head_clean_at) >>
  qexistsl_tac [`DF H`, `H`, `cenv`, `cx`, `lo`, `s`, `ftv`] >>
  fs[ghost_inv_at_def] >> metis_tac[]
QED
