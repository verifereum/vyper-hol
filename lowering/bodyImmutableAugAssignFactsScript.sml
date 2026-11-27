Theory bodyImmutableAugAssignFacts
Ancestors
  bodySim bodyInvSplit bodyInvCodeProps bodyInvMetadataProps exprBodyPreProps
  augAssignFullImmutableSetup alist bodyStorageMetadata exprSimHypsDefs
  stmtSimAugAssignPlace supportedDecls
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperInterpreter
  vyperState exprOpenMain exprSimSource exprSimTopLevelImmutable
  finite_map list compileEnv loweringStateRelDefs exprSimUnwrap loweringPosts exprLoweringProps

(* In a linked environment, a declaration can be typed before its location
   is allocated. The location bound applies when the compiler map has an entry. *)
Theorem immutable_augassign_metadata_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  cx.in_deploy /\ expr_sim_inv_mods mods cenv cx env es /\
  supported_immutable_type tops (NONE,id) = SOME ity /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) =
    SOME env' ==>
  cenv.ce_is_ctor /\ ty = ity /\ is_word_type ty /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  FLOOKUP env.bare_global_assignable (src,id) = SOME ty /\
  src = cenv.ce_module /\
  cenv.ce_module_var_type (src,id) = SOME ty /\
  (IS_SOME (FLOOKUP cenv.ce_module_vars (src,id)) ==>
   ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
         (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
               off + type_memory_size tv < dimword (:256)))
Proof
  strip_tac >>
  drule_then strip_assume_tac aug_place_typing >>
  `is_word_type ty` by
    (`?tv. evaluate_type env.type_defs ty = SOME tv` by
       metis_tac[assignable_type_well_formed, well_formed_type_def,
                 optionTheory.IS_SOME_EXISTS] >>
     metis_tac[stmtSimAugAssignTheory.well_typed_binop_augassign_is_word]) >>
  qpat_assum `module_body_inv _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [module_body_inv_def]) >>
  drule_all_then strip_assume_tac augassign_immutable_place_mods >>
  drule_then assume_tac contract_inv_constructor >>
  `ty = ity` by
    fs[type_place_target_TopLevelNameTarget] >>
  fs[expr_sim_inv_mods_def, bare_globals_layout_def] >>
  metis_tac[]
QED

Theorem immutable_augassign_metadata:
  !tops ctx cenv cx env es src id ity ret_ty ty bop e env'.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    expr_sim_inv cenv cx env es /\
    supported_immutable_type tops (src,id) = SOME ity /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) =
      SOME env' ==>
    src = NONE /\ cenv.ce_is_ctor /\ ty = ity /\ is_word_type ty /\
    FLOOKUP env.bare_globals (src,id) = SOME ty /\
    ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
          src = cenv.ce_module /\
          cenv.ce_module_var_type (src,id) = SOME ty /\
          (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                off + type_memory_size tv < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `src = NONE` by
    (spose_not_then assume_tac >>
     drule_then strip_assume_tac supported_lookup_other_module >>
     fs[supported_immutable_type_def]) >>
  gvs[] >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac body_inv_module >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env es` by fs[expr_sim_inv_split_def] >>
  drule_all_then strip_assume_tac (SIMP_RULE (srw_ss()) [ALOOKUP_def] (Q.INST
    [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`]
    (SPEC_ALL immutable_augassign_metadata_mods))) >>
  qpat_x_assum `ty = ity` SUBST_ALL_TAC >>
  `IS_SOME (FLOOKUP cenv.ce_module_vars (NONE,id))` by
    (qpat_assum `expr_sim_inv cenv cx env es`
       (mp_tac o Q.SPECL [`NONE`,`id`,`ity`] o
        CONJUNCT2 o REWRITE_RULE [expr_sim_inv_split_def]) >>
     simp[]) >>
  first_x_assum drule >> simp[]
QED

Theorem immutable_augassign_source_prefix:
  !cx src id es ts imms tv v.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = NONE /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (ImmutablePlace src id []),es) /\
    read_place cx (ImmutablePlace src id []) es = (INL v,es) /\
    place_type_value cx (ImmutablePlace src id []) es = (INL tv,es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def,
       get_immutables_def, get_address_immutables_def, get_place_def,
       read_place_def, place_type_value_def, bind_def, return_def,
       lift_option_type_def, lift_sum_def, evaluate_subscripts_def,
       subscripts_type_def]
QED

Theorem immutable_augassign_entry:
  !cenv cx env es src id ty.
    expr_sim_inv cenv cx env es /\
    FLOOKUP env.bare_globals (src,id) = SOME ty ==>
    ?ts imms tv v.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = NONE /\
      ALOOKUP es.immutables cx.txn.target = SOME imms /\
      FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v
Proof
  rpt strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  drule_all env_consistent_bare_global_ready_src >> strip_tac >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  `find_var_decl_by_name id ts = NONE` by
    (fs[env_consistent_def, env_context_consistent_def] >>
     qpat_x_assum `!src id ty. FLOOKUP env.bare_globals _ = _ ==> ?ts. _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  Cases_on `FLOOKUP (get_source_immutables src x) id` >>
  gvs[get_source_immutables_def] >>
  rename1 `_ = SOME pair` >> PairCases_on `pair` >>
  qexistsl_tac [`pair0`, `pair1`] >> simp[] >>
  conj_tac
  >- (fs[env_consistent_def, env_immutables_consistent_def,
         get_source_immutables_def] >> metis_tac[]) >>
  `state_well_typed es` by fs[expr_sim_inv_def] >>
  drule_all state_well_typed_immutables_ALOOKUP >>
  strip_tac >> drule imms_well_typed_get_source_immutables >>
  simp[get_source_immutables_def] >> metis_tac[]
QED

Theorem immutable_augassign_load:
  stmt_state_rel H ctx func cenv cx es ss /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,v) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  value_has_type tv v /\ off + type_memory_size tv < dimword (:256) ==>
  mload off ss = typed_val_to_w256 tv v
Proof
  strip_tac >>
  drule_then assume_tac stateRelProjTheory.stmt_state_rel_state_rel >>
  `val_in_memory tv v off ss.vs_memory` by
    (drule stateRelProjTheory.state_rel_immutables_rel >>
     simp[immutables_rel_def] >> disch_then drule_all >> simp[]) >>
  drule_all exprSimPropsTheory.val_in_memory_word_type >>
  simp[valueEncodingDefsTheory.mem_word_at_def, venomStateTheory.mload_def]
QED
