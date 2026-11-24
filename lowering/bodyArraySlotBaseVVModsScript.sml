(* A qualified array slot contributes a literal pointer without running code. *)
Theory bodyArraySlotBaseVVMods
Ancestors
  bodyQualifiedSlotRawMods bodyFullPostsMods gasOutcomeFullPostMods
  fragGasOriginPtr bodyPtrDefs context loweringPosts
  vyperStorageFootprint vyperInterpreter vyperState vyperAST

Theorem array_slot_base_vv_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  well_typed_expr env (TopLevelName (ArrayT et bd) (src,id)) /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME rt ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TopLevelName (ArrayT et bd) (src,id)) es
Proof
  strip_tac >> rw[expr_vv_sim_full_mods_def] >>
  drule_all_then (qspecl_then [`ty`,`sa`] (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]))
    qualified_array_slot_raw_mods >>
  Cases_on `storage_trace_domain cx st0 (es.storage_trace ++ [StorageRoot tr slot rt])`
  >- (qpat_assum `storage_trace_domain _ _ _ ==> _` (drule_then strip_assume_tac) >>
      qpat_x_assum `compile_expr cenv ty _ sa = (vv,sb)` mp_tac >> simp[] >>
      disch_then (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
      irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G0`, `es with storage_trace := es.storage_trace ++ [StorageRoot tr slot rt]`,
                    `INL (PlaceR (StoragePlace tr (n2w slot) rt))`, `s0`, `tn0`] >>
      simp[] >> gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> MEM _ _ /\ _`
        (drule_then strip_assume_tac) >>
      Cases_on `tr` >> fs[gas_origin_ptr_path_rules, ghost_kept_at_def,
                          vv_location_def, mk_ptr_def, slot_loc_def]) >>
  irule gas_outcome_full_mods_bad_nil >> simp[]
QED
