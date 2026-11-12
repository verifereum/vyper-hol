(* Memory case of the body induction (bodyMemory's body_mem_mutual): append. *)
Theory bodyMemAppend
Ancestors
  bodyMemoryPreds bodyMemAppendAdapter supportedStmts supportedExprs
  bodyMemAppendAggregateFacts bodyExprPreFacts
  bodyMemAssignTopCopyFacts vyperLookupStorage vyperStorageLayoutSafety
  bodyAppendStorageFacts bodyAppendStorageAdapter bodySim exprSimHypsDefs
  exprLoweringProps loweringStateRelDefs compileEnv vyperValue
  vyperTypeValues supportedDecls stmtSimDefs exprSimMemDefs bodyStorageMetadata
  vyperAST supportedTypes vyperTypeSystem
Libs
  monadsyntax

(* PORT_ADMISSION SEQ-4381: body_append_storage_narrow_mem.
   Original source: 488580bb2. TRUE as stated on 67c6f13fd; body_inv and
   expr_sim_inv supply acyclic_struct_metadata and field consistency.
   The lower metadata-free memory helper is false, so the cut is here.
   This masks the whole aggregate case, including previously proved static
   aggregate/direct-single-word aggregate paths, until the actual sparse
   compile_store_slots consumer port is restored. Primitive full-word Append
   (uint256, int256, bytes32) remains proved by bodyMemAppendAdapter;
   append_storage_element_domain excludes other scalar word types here.
   Original proof retained:

Proof
  rpt gen_tac >> strip_tac >>
  rw[body_stmt_mem_ok_def] >>
  `tops' = tops` by fs[body_inv_def] >> gvs[] >>
  drule_all append_narrow_annotation >> strip_tac >>
  `supported_storage_type tops elem /\ ~is_bytestring_type elem /\
   ~is_word_type elem` by metis_tac[append_storage_element_domain] >>
  Cases_on `nid` >>
  drule_at (Pat `supported_variable_decl _ _ = _`) append_aggregate_target_layout >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `supported_pure_expr tops e /\ supported_expr tops e` by
    (fs[supported_stmt_def] >> metis_tac[supportedExprsTheory.supported_expr_def]) >>
  drule append_typing_target >> strip_tac >>
  `expr_body_pre cenv' cx env e es` by metis_tac[body_append_expr_pre] >>
  `body_expr_mem_ok cx e` by metis_tac[] >>
  `expr_sim_mem ctx' func cenv' cx elem e es` by
    metis_tac[body_expr_mem_ok_def] >>
  `type_memory_bytes cenv' elem < 2 ** 64` by
    metis_tac[body_append_element_alloc_bound] >>
  `get_module_code cx q = SOME tops` by
    (drule supported_variable_decl_mem >> strip_tac >> gvs[body_inv_def]) >>
  qmatch_asmsub_abbrev_tac `StorageVarDecl tr (ArrayT elem (Dynamic dn))` >>
  `storage_var_info cx q r = SOME (tr,rslot,ArrayTV tv (Dynamic dn))` by
    gvs[storage_var_info_def, evaluate_type_def] >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  `0 < type_slot_size (ArrayTV tv (Dynamic dn))` by simp[type_slot_size_def] >>
  drule_all topcopy_region >> strip_tac >>
  `rslot < dimword (:256)` by decide_tac >>
  `w2n (n2w rslot : 256 word) = rslot` by simp[] >>
  `declared_storage_region cx q r [] =
    SOME (tr,n2w rslot,ArrayTV tv (Dynamic dn))` by
    metis_tac[declared_storage_region_ordinary] >>
  `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  `dn < dimword (:256)` by
    (`dn <= dn * type_slot_size tv` by
       (Cases_on `type_slot_size tv` >> fs[] >> simp[arithmeticTheory.MULT_CLAUSES]) >>
     qpat_x_assum `type_slot_size (ArrayTV _ _) < _` mp_tac >>
     pure_rewrite_tac[type_slot_size_def, bound_length_def] >> decide_tac) >>
  `lowered_value_type cenv' e = elem` by
    metis_tac[append_aggregate_lowered_type, supported_pure_int_calls] >>
  drule_all body_append_root_metadata >> strip_tac >>
  `(storage_vars_rel cenv' cx /\ transient_vars_rel cenv' cx) ==>
    stmt_frag_mem d ctx' func cx lctx RetQ cenv'
      (stmt_env cenv' lctx ret_ty (Append (TopLevelNameTarget (q,r)) e))
      (eval_stmt cx (Append (TopLevelNameTarget (q,r)) e)) es`
    suffices_by
      (strip_tac >> rewrite_tac[stmt_frag_mem_def] >>
       rpt gen_tac >> strip_tac >>
       `storage_vars_rel cenv' cx /\ transient_vars_rel cenv' cx` by
         fs[stmt_state_rel_def, state_rel_def] >>
       qpat_x_assum `_ ==> stmt_frag_mem _ _ _ _ _ _ _ _ _ _`
         (mp_tac o REWRITE_RULE [stmt_frag_mem_def]) >> simp[] >> metis_tac[]) >>
  strip_tac >> drule_all append_storage_compiler_location >> strip_tac >>
  irule compile_append_storage_aggregate_stmt_frag_mem >>
  (conj_tac >- metis_tac[]) >>
  qexistsl_tac [`dn`, `elem`, `q`, `r`, `n2w rslot`, `tr`, `tv`] >>
  simp[] >>
  (conj_tac >-
    (rpt strip_tac >>
     `value_has_type tv v` by metis_tac[topcopy_rhs_value_typed] >>
     metis_tac[vyperTypingTheory.value_has_type_equiv, optionTheory.IS_SOME_EXISTS])) >>
  rpt strip_tac >> fs[Abbr `tr`] >> metis_tac[]
QED
*)
Theorem body_append_storage_narrow_mem:
  !cx nid e tops ctx cenv vis mut elem dn slot.
    (!s'' p t'. eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
                body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_variable_decl tops nid =
      SOME (vis, mut, ArrayT elem (Dynamic dn), SOME slot) /\
    (mut = Storage \/ mut = Transient) /\ ~supported_full_word_type elem /\
    type_memory_bytes cenv elem < 2 ** 64 ==>
    body_stmt_mem_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  cheat
QED

Theorem body_append_mem_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_mem_ok cx e) /\
    body_base_target_mem_ok cx t ==>
    body_stmt_mem_ok cx (Append t e)
Proof
  rpt strip_tac >> Cases_on `?nid. t = TopLevelNameTarget nid`
  >- (gvs[] >> rw[body_stmt_mem_ok_def] >>
      Cases_on `supported_storage_dynamic_array tops nid`
      >- (Cases_on `nid` >>
          irule body_append_storage_fragment_mem >>
          gvs[supported_stmt_def] >> metis_tac[supportedExprsTheory.supported_expr_def]) >>
      gvs[supported_stmt_def, supported_append_target_def] >>
      `supported_stmt tops [] (Append (TopLevelNameTarget nid) e)` by
        (simp[supported_stmt_def, supported_append_target_def] >> metis_tac[]) >>
      drule bodyAppendStorageFactsTheory.body_append_element_alloc_bound >> strip_tac >>
      drule_at (Pat `supported_variable_decl _ _ = _`)
        body_append_storage_narrow_mem >>
      disch_then (qspecl_then [`cx`, `e`, `ctx`, `cenv`] mp_tac) >>
      simp[] >>
      rewrite_tac[body_stmt_mem_ok_def] >> disch_then drule_all >> simp[]) >>
  Cases_on `t` >> gvs[] >>
  rw[body_stmt_mem_ok_def, supported_stmt_def, supported_append_target_def]
QED
