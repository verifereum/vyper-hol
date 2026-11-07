(*
 * Pop on a nested target: pop_nested_immutable_deploy_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedImmutableDeploy
Ancestors
  exprSimPopNestedBase exprSimPopImmutableTarget
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

Theorem pop_immutable_place_live[local]:
  !cx es src id path imms tv a vs updated.
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,a) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) =
      INL updated ==>
    pop_place cx (ImmutablePlace src id path) es =
      (INL (Value (LAST vs)),
       es with immutables :=
         (cx.txn.target,
          set_source_immutables src
            (get_source_immutables src imms |+ (id,(tv,updated))) imms) ::
         ADELKEY cx.txn.target es.immutables)
Proof
  rpt strip_tac >>
  `pop_element (ArrayV (DynArrayV vs)) =
    INL (ArrayV (DynArrayV (FRONT vs)))` by
    simp[vyperValueOperationTheory.pop_element_def] >>
  drule_all vyperLookupTheory.assign_subscripts_pop_replace >> strip_tac >>
  simp[pop_place_def, get_immutables_def, get_address_immutables_def,
       set_immutable_def, set_address_immutables_def,
       bind_def, ignore_bind_def, return_def, lift_option_type_def, lift_sum_def,
       vyperValueOperationTheory.popped_value_def] >>
  simp[evaluation_state_component_equality]
QED

(* Updating one source immutable needs new bytes only for that root. *)
Theorem immutables_rel_ctor_update[local]:
  !cenv addr src es s t imms id tv updated off es'.
    immutables_rel cenv addr src T es s /\
    ALOOKUP es.immutables addr = SOME imms /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    es'.immutables =
      (addr,set_source_immutables src
        (get_source_immutables src imms |+ (id,(tv,updated))) imms) ::
      ADELKEY addr es.immutables /\
    immutable_value_admissible tv updated /\
    val_in_memory tv updated off t.vs_memory /\
    immutable_value_bytes_rel tv updated
      (mem_bytes_at off (type_memory_size tv) t.vs_memory) /\
    (!name tv0 v off0.
      name <> id /\
      FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off0) /\
      FLOOKUP (get_source_immutables src imms) name = SOME (tv0,v) ==>
      mem_bytes_at off0 (type_memory_size tv0) t.vs_memory =
      mem_bytes_at off0 (type_memory_size tv0) s.vs_memory) ==>
    immutables_rel cenv addr src T es' t
Proof
  rpt gen_tac >> strip_tac >>
  gvs[immutables_rel_def, get_source_immutables_def, set_source_immutables_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `name = id` >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  `mem_bytes_at byte_offset (type_memory_size tv') t.vs_memory =
    mem_bytes_at byte_offset (type_memory_size tv') s.vs_memory` by
    (first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!name tv' v byte_offset. _ ==> _ /\ _ /\ _`
    drule_all >> strip_tac >>
  simp[] >> irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac
  >- metis_tac[loweringSliceTheory.immutable_admissible_val_wf] >>
  qexistsl [`type_memory_size tv'`, `s.vs_memory`] >> simp[]
QED

Theorem immutable_store_other_bytes[local]:
  !cenv cx env es imms src id off tv a k word s.
    expr_sim_inv cenv cx env es /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,a) /\
    k + 32 <= type_memory_size tv ==>
    !name tv0 v off0.
      name <> id /\
      FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off0) /\
      FLOOKUP (get_source_immutables src imms) name = SOME (tv0,v) ==>
      mem_bytes_at off0 (type_memory_size tv0)
        (mstore (off+k) word s).vs_memory =
      mem_bytes_at off0 (type_memory_size tv0) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) off0 (type_memory_size tv0)` by
    (gvs[exprSimHypsDefsTheory.expr_sim_inv_def,
         exprSimHypsDefsTheory.bare_globals_layout_def,
         env_consistent_def, env_immutables_consistent_def] >>
     qpat_assum `!src id off. _ ==> ?ty. _`
       (qspecl_then [`src`, `id`, `off`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `ty1` assume_tac) >>
     qpat_assum `!src id off. _ ==> ?ty. _`
       (qspecl_then [`src`, `name`, `off0`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `ty2` assume_tac) >>
     `evaluate_type (get_tenv cx) ty1 = SOME tv` by
       (qpat_assum `!src id ty tv v. _ /\ _ ==> _`
          irule >> goal_assum (drule_at Any) >> simp[]) >>
     `evaluate_type (get_tenv cx) ty2 = SOME tv0` by
       (qpat_assum `!src id ty tv v. _ /\ _ ==> _`
          irule >> goal_assum (drule_at Any) >> simp[]) >>
     first_x_assum irule >>
     qexistsl [`id`, `name`, `src`, `ty1`, `ty2`] >> simp[]) >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  gvs[regions_disjoint_def] >> decide_tac
QED

Theorem immutable_store_frame_bytes[local]:
  !ctx func cenv cx env es s imms id off tv a k word.
    expr_sim_inv cenv cx env es /\
    stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
    FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
    k + 32 <= type_memory_size tv ==>
    !base sz.
      ((?aid. FLOOKUP s.vs_allocas aid = SOME (base,sz)) \/
       (?name. local_region cenv es.scopes s name base sz)) ==>
      mem_bytes_at base sz (mstore (off+k) word s).vs_memory =
      mem_bytes_at base sz s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `?ty. cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
        evaluate_type (get_tenv cx) ty = SOME tv` by
    (gvs[exprSimHypsDefsTheory.expr_sim_inv_def,
         exprSimHypsDefsTheory.bare_globals_layout_def,
         env_consistent_def, env_immutables_consistent_def] >>
     qpat_assum `!src id off. _ ==> ?ty. _` drule_all >>
     disch_then (qx_choose_then `ty` assume_tac) >>
     qexists `ty` >> conj_tac
     >- (qpat_assum `!src id ty. _ ==> _ = SOME ty` drule_all >> simp[]) >>
     qpat_assum `!src id ty tv v. _ /\ _ ==> _` irule >>
     goal_assum (drule_at Any) >> simp[]) >>
  `immutable_decl_sep cenv cx es.scopes s.vs_vars s.vs_allocas s.vs_alloca_next` by
    gvs[stmt_state_rel_def, immutable_alloca_sep_def] >>
  qpat_x_assum `immutable_decl_sep _ _ _ _ _ _` mp_tac >>
  rewrite_tac[immutable_decl_sep_alt] >>
  disch_then drule_all >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_rename_tac `mem_bytes_at b n` >>
  `regions_disjoint off (type_memory_size tv) b n` by
    metis_tac[] >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  gvs[regions_disjoint_def] >> decide_tac
QED

(* Pop on a member of an immutable in the constructor, which Python's
   checker accepts for a complex immutable (local.py skips the
   modification count when var_info is None), with pure indices.  The
   lowering (nested_pop_compile_eq, compile_dynarray_pop) walks the target
   to a code-location pointer, loads the length through the immutables
   buffer (compile_ptr_load: in the constructor an MLOAD at immutable
   base 0 plus the offset), asserts it nonzero, stores the decremented
   length (compile_ptr_store, an ISTORE) and returns the pointer to the
   last element.  The target's indices are lowered by compile_expr, so
   their judgments (target_idx_case) are a premise, as target_case_all
   takes them; the ce_is_ctor and ce_module_var_type premises also follow
   from expr_sim_inv's bare_globals_layout (pop_nested_immutable_root_ctor).

   Why it holds (admitted pending alan):
   - the result: vv_holds of a LocatedValue at LocCode is immutable_holds,
     whose constructor disjunct reads the element from memory at
     off + k + 32 + (len-1) * elem_size, past the stored length word
     (pop_path_elem_in_memory is the memory version); vv_at at LocCode is
     vacuous; the source value is LAST vs (pop_place, popped_value);
   - immutables_rel: the popped immutable's new value is in memory by the
     path lemma (val_in_memory_pop_path, stated with Replace (FRONT vs)),
     and immutable_value_bytes_rel's T positions after the pop are the new
     length word plus a subset of the old ones; every other immutable is
     in bare_globals (bare_globals_layout's first clause) and its region
     disjoint (its third), so immutables_rel_mem_agree carries it over;
   - frames: immutable_decl_sep separates the declared immutable's region
     from every vs_allocas entry and every live local, and the store lies
     inside that region (k + 32 <= type_memory_size);
   - errors: an empty array is RuntimeError "pop empty" in the source and
     a failing ASSERT in Venom, which expr_exit accepts;
   - gas: as pop_nested_storage_pure_sim (gas_outcome split,
     gas_exempt_cert_error_place on the error branch).
   imm_target_walk is stated over eval_base_place; Pop evaluates with
   eval_target_place. *)
Theorem pop_nested_immutable_deploy_pure_sim:
  !ctx func cenv cx env ann bt ty es src id nocalls.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    target_idx_case nocalls ctx func cenv cx bt /\
    (nocalls ==> int_calls_target bt = []) /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    EVERY pure_expr (target_indices bt) /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* By the indices: pure ones by pop_nested_immutable_deploy_pure_sim; one
   that pops or calls is exprSimPopImmutableTarget's residual
   pop_nested_immutable_deploy_impure_index_case. *)
Theorem pop_nested_immutable_deploy_sim:
  !ctx func cenv cx env ann bt ty es src id nocalls.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    target_idx_case nocalls ctx func cenv cx bt /\
    (nocalls ==> int_calls_target bt = []) /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> Cases_on `EVERY pure_expr (target_indices bt)`
  >- (irule pop_nested_immutable_deploy_pure_sim >> metis_tac[]) >>
  irule pop_nested_immutable_deploy_impure_index_case >> metis_tac[]
QED
