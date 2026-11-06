(* Source writes are independent of the observation tail. These equations
   retain the chosen endpoint for the counted pointer continuation. *)
Theory assignTuplePtrSourceGas
Ancestors
  tupleTargetStoreProps tupleTargetStoreRun stmtSimAssignStorage
  vyperInterpreter vyperState vyperValue vyperTyping vyperContext
  vyperStorageBackend vyperLookup list rich_list finite_map

Theorem tuple_source_target_gas_obs_ptr:
  !cx es g tv v tail.
    tuple_source_target cx es.scopes g tv /\ value_has_type tv v ==>
    assign_tuple_targets cx g v (es with gas_obs := tail) =
      (FST (assign_tuple_targets cx g v es),
       SND (assign_tuple_targets cx g v es) with gas_obs := tail)
Proof
  rpt gen_tac >> simp[tuple_source_target_def] >> strip_tac >> gvs[]
  >- (drule lookup_scopes_find_containing_scope >> strip_tac >>
      simp[evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, get_place_def, get_scopes_def] >>
      simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
           lift_option_type_def, type_check_def, assert_def, lift_sum_def,
           replace_memory_entry_def, evaluate_subscripts_def,
           assign_subscripts_def, set_scopes_def, return_def])
  >- (drule_all tuple_target_toplevel_place >> strip_tac >>
      ntac 3 (simp[Once evaluate_def, bind_def] >> asm_rewrite_tac[]) >>
      simp[write_place_def, write_storage_slot_gas_obs]) >>
  drule_all tuple_target_field_place >> strip_tac >>
  ntac 3 (simp[Once evaluate_def, bind_def] >> asm_rewrite_tac[]) >>
  simp[write_place_def, write_storage_slot_gas_obs]
QED

Theorem assign_tuple_target_list_gas_obs_ptr:
  !gs cx es tvs vs tail.
    ~cx.txn.is_static /\
    LIST_REL (tuple_source_target cx es.scopes) gs tvs /\
    LIST_REL value_has_type tvs vs ==>
    assign_tuple_target_list cx gs vs (es with gas_obs := tail) =
      (FST (assign_tuple_target_list cx gs vs es),
       SND (assign_tuple_target_list cx gs vs es) with gas_obs := tail)
Proof
  Induct
  >- simp[evaluate_def, return_def] >>
  rpt gen_tac >> Cases_on `tvs` >> simp[] >> Cases_on `vs` >> simp[] >>
  strip_tac >> rename1 `LIST_REL value_has_type tail_tvs tail_vs` >>
  drule_all tuple_source_target_safe >> strip_tac >>
  `LIST_REL (tuple_source_target cx es'.scopes) gs tail_tvs` by
    (irule LIST_REL_mono >> first_assum (irule_at Any) >>
     metis_tac[tuple_source_target_layout]) >>
  drule_all tuple_source_target_gas_obs_ptr >>
  disch_then (qspec_then `tail` assume_tac) >>
  first_x_assum drule_all >>
  disch_then (qspec_then `tail` assume_tac) >>
  ntac 3 (simp[Once evaluate_def, ignore_bind_def, bind_def])
QED

Theorem assign_tuple_targets_success_gas_tail_ptr:
  ~cx.txn.is_static /\
  LIST_REL (tuple_source_target cx es.scopes) gs tvs /\
  LIST_REL value_has_type tvs vs /\
  assign_tuple_target_list cx gs vs es = (INL (),ee) ==>
  !tail. assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs))
    (es with gas_obs := tail) = (INL (),ee with gas_obs := tail)
Proof
  strip_tac >> drule_all assign_tuple_target_list_gas_obs_ptr >>
  simp[Once evaluate_def]
QED
