(* Static-inclusive source outcomes for ordered tuple stores. *)
Theory tupleTargetStoreAbort
Ancestors
  tupleTargetStoreProps vyperInterpreter vyperState vyperValue vyperLookup

Theorem tuple_target_source_outcome:
  !cenv cx es g ty tv v.
    tuple_target_aligned cenv cx g ty tv /\
    tuple_target_layout es.scopes g ty tv v /\ value_has_type tv v ==>
    ?res es1.
      (!tail. assign_tuple_targets cx g v (es with gas_obs := tail) =
        (res, es1 with gas_obs := tail)) /\
      (res = INL () \/
       cx.txn.is_static /\ (!id. g <> BaseTarget (NameTarget id)) /\
       res = INR (Error (RuntimeError "write in static context")))
Proof
  rpt strip_tac >>
  drule_all tuple_target_aligned_source >> strip_tac >>
  qexistsl [`FST (assign_tuple_targets cx g v es)`,
            `SND (assign_tuple_targets cx g v es)`] >>
  conj_tac
  >- (gen_tac >> irule tuple_source_target_gas_obs >> metis_tac[]) >>
  Cases_on `cx.txn.is_static`
  >- (qpat_x_assum `tuple_source_target _ _ _ _` mp_tac >>
      simp[tuple_source_target_def] >> strip_tac >> gvs[]
      >- (drule lookup_scopes_find_containing_scope >> strip_tac >>
          simp[evaluate_def, bind_def, ignore_bind_def, type_check_def,
               assert_def, return_def, get_place_def, get_scopes_def] >>
          simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
               lift_option_type_def, type_check_def, assert_def, lift_sum_def,
               replace_memory_entry_def, evaluate_subscripts_def,
               assign_subscripts_def, set_scopes_def, return_def])
      >- (drule_all tuple_target_toplevel_place >> strip_tac >>
          ntac 3 (simp[Once evaluate_def, bind_def] >> asm_rewrite_tac[]) >>
          simp[write_place_def, write_storage_slot_def, ignore_bind_def,
               bind_def]) >>
      drule_all tuple_target_field_place >> strip_tac >>
      ntac 3 (simp[Once evaluate_def, bind_def] >> asm_rewrite_tac[]) >>
      simp[write_place_def, write_storage_slot_def, ignore_bind_def, bind_def]) >>
  drule_all tuple_source_target_safe >> strip_tac >> simp[]
QED
