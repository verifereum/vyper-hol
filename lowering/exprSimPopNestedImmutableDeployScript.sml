(*
 * Pop on a nested target: pop_nested_immutable_deploy_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedImmutableDeploy
Ancestors
  exprSimPopNestedBase exprSimPopImmutableTarget
  exprSimHash fragGasSeqAbort gasSummaryCompose gasExemptCert gasSummary gasOutcome
  popTargetPre allocLimits supportedExprTraverse exprSimHypsDefs supportedProgram
  loweringPosts bodySim stmtSimProps fragGasMode fragGasPath
  exprSimPopNestedLocalSource exprSimPopNestedLocalPath
  list rich_list arithmetic words fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv loweringStateRelDefs finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

Theorem immutable_pop_read[local]:
  !cenv cx env es id path w ann n.
    expr_sim_inv cenv cx env es /\
    imm_place_at cenv cx es
      (PlaceR (ImmutablePlace cenv.ce_module id path)) w (ArrayT ann (Dynamic n)) ==>
    ?imms itv iv off k etv vs.
      ALOOKUP es.immutables cx.txn.target = SOME imms /\
      FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (itv,iv) /\
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
      off + type_memory_size itv < dimword (:256) /\ w = n2w (off+k) /\
      mem_path_offset itv path = SOME (k,ArrayTV etv (Dynamic n)) /\
      evaluate_subscripts itv iv path = INL (ArrayV (DynArrayV vs)) /\
      evaluate_type (get_tenv cx) ann = SOME etv /\
      value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
      read_place cx (ImmutablePlace cenv.ce_module id path) es =
        (INL (ArrayV (DynArrayV vs)),es)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[imm_place_at_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  drule_all imm_place_at_value_type >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
  simp[read_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, return_def, lift_sum_def, lift_option_type_def]
QED

Theorem immutable_pop_bounds[local]:
  !tv a path k etv n vs.
    value_has_type tv a /\ well_formed_type_value tv /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) ==>
    LENGTH vs < dimword (:256) /\
    (vs <> [] ==>
      value_has_type etv (LAST vs) /\
      k + 32 + (LENGTH vs-1) * type_memory_size etv + type_memory_size etv <=
        type_memory_size tv)
Proof
  rpt gen_tac >> strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
   well_formed_type_value (ArrayTV etv (Dynamic n))` by
    metis_tac[vyperPlaceStatePreservationTheory.evaluate_subscripts_type,
      vyperPlaceStatePreservationTheory.subscripts_type_well_formed] >>
  gvs[vyperTypingTheory.value_has_type_def,
      vyperTypingTheory.well_formed_type_value_def,
      valueEncodingTheory.type_memory_size_def] >>
  strip_tac >> conj_tac
  >- (gvs[vyperTypingTheory.all_have_type_EVERY, EVERY_MEM] >>
      metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  `type_memory_size etv * (LENGTH vs - 1) + type_memory_size etv =
     LENGTH vs * type_memory_size etv` by
    (Cases_on `vs` >> gvs[arithmeticTheory.MULT_CLAUSES]) >>
  `LENGTH vs * type_memory_size etv <= n * type_memory_size etv` by
    simp[] >> decide_tac
QED

Theorem immutable_pop_empty[local]:
  read_place cx (ImmutablePlace src id path) es =
    (INL (ArrayV (DynArrayV [])),es) ==>
  pop_place cx (ImmutablePlace src id path) es =
    (INR (Error (RuntimeError "pop empty")),es)
Proof
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[read_place_def, pop_place_def, get_immutables_def,
       get_address_immutables_def, bind_def, return_def, raise_def,
       lift_sum_def, lift_option_type_def, ignore_bind_def] >>
  rename1 `get_source_immutables src imms` >>
  Cases_on `FLOOKUP (get_source_immutables src imms) id` >>
  simp[return_def, raise_def] >>
  PairCases_on `x` >>
  Cases_on `evaluate_subscripts x0 x1 path` >>
  simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  simp[vyperValueOperationTheory.popped_value_def, raise_def]
QED

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

Theorem immutable_store_wb_frame[local]:
  !ctx func cenv cx env es s imms id off tv a k word sm.
    expr_sim_inv cenv cx env es /\
    stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
    FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
    k + 32 <= type_memory_size tv ==>
    wb_frame cenv es sm s (mstore (off+k) word s)
Proof
  rpt gen_tac >> strip_tac >>
  `!b sz. ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
           (?name. local_region cenv es.scopes s name b sz)) ==>
     mem_bytes_at b sz (mstore (off+k) word s).vs_memory =
     mem_bytes_at b sz s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     irule immutable_store_frame_bytes >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `(mstore (off+k) word s).vs_vars = s.vs_vars /\
   (mstore (off+k) word s).vs_allocas = s.vs_allocas` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  simp[wb_frame_def, lookup_var_def] >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule locals_kept_regions >> rpt strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem immutable_replace_mstore_stmt_frame[local]:
  !ctx func cenv cx es s imms id tv a updated es' p word.
    stmt_state_rel ctx func cenv cx es s /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
    es' = es with immutables :=
      (cx.txn.target,set_source_immutables cenv.ce_module
        (get_source_immutables cenv.ce_module imms |+ (id,(tv,updated))) imms) ::
      ADELKEY cx.txn.target es.immutables /\
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
      es' (mstore p word s) /\
    local_ptrs_rel func cenv es.scopes (mstore p word s) ==>
    stmt_state_rel ctx func cenv cx es' (mstore p word s)
Proof
  rpt gen_tac >> strip_tac >>
  `immutable_alloca_sep func cenv cx es' (mstore p word s)` by
    (`immutable_alloca_sep func cenv cx es s` by gvs[stmt_state_rel_def] >>
     gvs[immutable_alloca_sep_def, immutable_decl_sep_alt,
         mstore_def, write_memory_with_expansion_def,
         get_source_immutables_def, set_source_immutables_def,
         local_region_def, lookup_var_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> rpt gen_tac >> strip_tac >>
     Cases_on `name = id` >> gvs[FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  irule stmt_state_rel_allocas_frame >>
  reverse (rpt conj_tac)
  >- (qexistsl [`es`, `s`] >>
      simp[mstore_def, write_memory_with_expansion_def])
  >- (gvs[stmt_state_rel_def, state_rel_def,
           storage_rel_def, transient_rel_def, accounts_rel_def, logs_rel_def,
           contract_storage_def, contract_transient_def,
           mstore_def, write_memory_with_expansion_def])
  >- first_assum ACCEPT_TAC >>
  gvs[stmt_state_rel_def, immutable_base_zero_def,
      mstore_def, write_memory_with_expansion_def]
QED

Theorem immutable_pop_stmt_state_rel[local]:
  !ctx func cenv cx env es s imms id off tv a path k etv n vs updated.
    cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
    stmt_state_rel ctx func cenv cx es s /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
    FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
    mutable_place_path tv path /\ value_has_type tv a /\ well_formed_type_value tv /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) =
      INL updated ==>
    stmt_state_rel ctx func cenv cx
      (es with immutables :=
        (cx.txn.target,set_source_immutables cenv.ce_module
          (get_source_immutables cenv.ce_module imms |+ (id,(tv,updated))) imms) ::
        ADELKEY cx.txn.target es.immutables)
      (mstore (off+k) (n2w (LENGTH vs-1)) s)
Proof
  rpt gen_tac >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module T es s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `immutable_value_admissible tv a /\ val_in_memory tv a off s.vs_memory` by
    (gvs[immutables_rel_def] >> first_x_assum drule_all >> simp[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `k + 32 <= type_memory_size tv` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `val_wf tv a` by metis_tac[loweringSliceTheory.immutable_admissible_val_wf] >>
  `immutable_value_admissible tv updated` by
    (irule immutable_pop_path_admissible >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `val_in_memory tv updated off
     (mstore (off+k) (n2w (LENGTH vs-1)) s).vs_memory` by
    (irule exprSimPopNestedLocalMemoryTheory.val_in_memory_pop_path >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `immutable_value_bytes_rel tv updated
     (mem_bytes_at off (type_memory_size tv)
       (mstore (off+k) (n2w (LENGTH vs-1)) s).vs_memory)` by
    (irule immutable_pop_path_bytes >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx es' t` >>
  `immutables_rel cenv cx.txn.target cenv.ce_module T es' t` by
    (irule immutables_rel_ctor_update >>
     qexistsl [`es`, `id`, `imms`, `off`, `s`, `tv`, `updated`] >>
     simp[Abbr `es'`, Abbr `t`] >> rpt strip_tac >>
     pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule immutable_store_other_bytes >>
     metis_tac[]) >>
  `t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `t`, mstore_def, write_memory_with_expansion_def] >>
  `local_ptrs_rel func cenv es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!name b sz. local_region cenv es.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >> unabbrev_all_tac >>
     irule immutable_store_frame_bytes >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes t` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists `s` >>
     simp[lookup_var_def] >> conj_tac >- metis_tac[] >>
     rpt strip_tac >> gvs[]) >>
  unabbrev_all_tac >>
  irule immutable_replace_mstore_stmt_frame >>
  conj_tac >- asm_rewrite_tac[] >>
  metis_tac[]
QED

(* ISTORE's finite map is bookkeeping, not the constructor representation. *)
Theorem immutable_bookkeeping_stmt_frame[local]:
  stmt_state_rel ctx func cenv cx es
    (s with vs_immutables := im) =
  stmt_state_rel ctx func cenv cx es s
Proof
  `!op. eval_operand op (s with vs_immutables := im) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       storage_rel_def, transient_rel_def, accounts_rel_def, logs_rel_def,
       contract_storage_def, contract_transient_def, immutables_rel_def,
       immutable_alloca_sep_def, immutable_decl_sep_def, local_region_def,
       lookup_var_def, immutable_base_zero_def, eval_operand_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       alloca_room_def, fmp_room_def, pending_alloca_size_def,
       local_backed_def]
QED

Theorem immutable_suffix_stmt_frame[local]:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  u = s with <|vs_vars := u.vs_vars; vs_immutables := u.vs_immutables;
              vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es u
Proof
  strip_tac >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  rewrite_tac[immutable_bookkeeping_stmt_frame] >>
  irule stmt_state_rel_vars_frame >> simp[lookup_var_def] >>
  gvs[local_ptrs_reserved_def, lookup_var_def,
      immutable_bookkeeping_stmt_frame, stmt_state_rel_inst_idx] >> metis_tac[]
QED

Theorem immutable_ctor_pointer_post[local]:
  post_value_type cenv e = expr_type e /\
  stmt_state_rel ctx func cenv cx es' u /\
  wb_frame cenv initial sa s0 u /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es'.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,updated) /\
  off + type_memory_size tv < dimword (:256) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  j + type_memory_size etv <= type_memory_size tv /\
  val_in_memory etv v (off+j) u.vs_memory /\ value_has_type etv v /\
  read_result cx result es' = (INL v,es') /\
  eval_operand op u = SOME (n2w (off+j)) ==>
  vv_post ctx func cenv cx e initial sa sb s0 es' result
    (LocatedValue (expr_type e) (mk_ptr op LocCode)) u
Proof
  strip_tac >>
  simp[vv_post_def, vv_holds_def, vv_at_def, contextTheory.mk_ptr_def] >>
  conj_tac
  >- (rewrite_tac[immutable_holds_def] >>
      qexistsl [`id`, `off`, `tv`, `updated`, `j`, `etv`, `v`] >> simp[]) >>
  gvs[wb_frame_def] >> first_assum ACCEPT_TAC
QED

(* Operational suffix at the compiler boundary; the immutable map is only
   bookkeeping, while the canonical byte update is MSTORE. *)
Theorem immutable_pop_run[local]:
  compile_dynarray_pop hdr 32 esz T imm LocCode sa = (r,sb) /\
  (!x. hdr = Var x ==> not_fresh_at sa x) /\
  (!region. imm = SOME region ==>
     eval_operand region s = SOME 0w /\
     (!x. region = Var x ==> not_fresh_at sa x)) /\
  eval_operand hdr s = SOME w /\ mload (w2n w) s <> 0w ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u.vs_memory = (mstore (w2n w) (mload (w2n w) s - 1w) s).vs_memory /\
    u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
                vs_immutables := u.vs_immutables|> /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    eval_operand r u = SOME (w + 32w + (mload (w2n w) s - 1w) * n2w esz)
Proof
  Cases_on `imm` >>
  simp[compile_dynarray_pop_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def, contextTheory.compile_imm_load_word_def,
       contextTheory.compile_imm_store_word_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `hdr` >> gvs[eval_operand_def] >>
  TRY (rename1 `eval_operand region s = SOME 0w` >>
       `!a V. mload a (s with vs_vars := V) = mload a s` by simp[mload_def] >>
       Cases_on `region` >> gvs[eval_operand_def]) >>
  fs[not_fresh_at_def, lookup_var_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[DROP_LENGTH_APPEND, APPEND] >>
  simp[Once run_inst_seq_def, mk_inst_def,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_11, bool_to_word_def, WORD_ADD_0] >>
  simp[Ntimes run_inst_seq_def 4,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_11, bool_to_word_def, WORD_ADD_0] >>
  simp[run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_11, bool_to_word_def, WORD_ADD_0] >>
  simp[istore_def, mstore_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_11] >>
  rpt strip_tac >> gvs[]
QED

Theorem immutable_pop_run_empty[local]:
  compile_dynarray_pop hdr 32 esz T imm LocCode sa = (r,sb) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  eval_operand hdr s = SOME w /\ mload (w2n w) s = 0w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  Cases_on `imm` >>
  simp[compile_dynarray_pop_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def, contextTheory.compile_imm_load_word_def,
       contextTheory.compile_imm_store_word_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  `!a V. mload a (s with vs_vars := V) = mload a s` by simp[mload_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[DROP_LENGTH_APPEND, APPEND] >>
  simp[Once run_inst_seq_def, mk_inst_def,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_11, bool_to_word_def, WORD_ADD_0] >>
  simp[Ntimes run_inst_seq_def 4,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_11, bool_to_word_def, WORD_ADD_0] >>
  simp[run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_read1_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       ASCIInumbersTheory.toString_11, bool_to_word_def, WORD_ADD_0]
QED

Theorem immutable_pop_code[local]:
  compile_dynarray_pop hdr 32 esz T imm LocCode sa = (r,sb) ==>
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  Cases_on `imm` >>
  simp[compile_dynarray_pop_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def, contextTheory.compile_imm_load_word_def,
       contextTheory.compile_imm_store_word_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt strip_tac >> gvs[same_blocks_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  pure_rewrite_tac[DROP_LENGTH_APPEND, APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem immutable_pop_gas_path[local]:
  compile_dynarray_pop hdr 32 esz T imm LocCode sa = (r,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule immutable_pop_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >> metis_tac[]) >>
  gvs[same_blocks_def] >> drule_all hash_run_path >> simp[]
QED

Theorem immutable_pop_abort_path[local]:
  compile_dynarray_pop hdr 32 esz T imm LocCode sa = (r,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?j. gas_marked_path F ctx func s 0 (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> drule immutable_pop_code >> strip_tac >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[IS_PREFIX_APPEND] >>
  drule_all storageCopyGasPathTheory.storage_copy_code_prefix >> strip_tac >>
  `isPREFIX (emitted_insts sa sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all run_inst_seq_abort_zero_path >> simp[]
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
Theorem nested_pop_immutable_suffix_sim[local]:
  expr_sim_inv cenv cx env es /\ cenv.ce_is_ctor /\ es.gas_obs = [] /\
  stmt_state_rel ctx func cenv cx es0 s0 /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  writable_place_result cx es (PlaceR (ImmutablePlace cenv.ce_module id path)) /\
  imm_target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (ImmutablePlace cenv.ce_module id path)) (ArrayT ann (Dynamic n))
    (hdr,SOME LocCode,pt) t /\
  compile_dynarray_pop hdr 32 (type_memory_bytes cenv ann) T cenv.ce_imm_alloca
    LocCode sm = (q,r) /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm /\ fn_has_code sm r func /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (pop_place cx (ImmutablePlace cenv.ce_module id path)) (es,t)
    (\res fin u. ?v. res = INL v /\
      vv_post ctx func cenv cx (Pop ann bt) es0 sa r s0 fin v
        (LocatedValue ann (mk_ptr q LocCode)) u /\
      u.vs_current_bb = r.cs_current_bb /\
      u.vs_inst_idx = LENGTH r.cs_current_insts)
    (\res fin rr. expr_exit res rr)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es t /\
   ?w. eval_operand hdr t = SOME w /\
     imm_place_at cenv cx es
       (PlaceR (ImmutablePlace cenv.ce_module id path)) w (ArrayT ann (Dynamic n))` by
    gvs[imm_target_post_def] >>
  drule_all immutable_pop_read >> strip_tac >>
  drule_all imm_place_pop_memory_root >> strip_tac >> gvs[] >>
  drule_all immutable_pop_bounds >> strip_tac >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region t = SOME 0w` by
    fs[stmt_state_rel_def, state_rel_def, immutable_base_zero_def] >>
  `mload (off+k) t = n2w (LENGTH vs)` by
    (simp[mload_def, GSYM valueEncodingDefsTheory.mem_word_at_def] >>
     drule_at (Pat `FLOOKUP cenv.ce_module_vars _ = _`)
       imm_readable_dynarray_length >>
     simp[] >> disch_then irule >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `off+k < dimword (:256)` by decide_tac >>
  Cases_on `vs = []`
  >- (gvs[] >>
      `mload (w2n (n2w (k+off):bytes32)) t = 0w` by
        simp[arithmeticTheory.ADD_COMM] >>
      drule_all immutable_pop_run_empty >> strip_tac >>
      drule_all immutable_pop_abort_path >> strip_tac >>
      drule_all immutable_pop_empty >> strip_tac >>
      `!tail. pop_place cx (ImmutablePlace cenv.ce_module id path)
          (es with gas_obs := tail) =
          (INR (Error (RuntimeError "pop empty")),es with gas_obs := tail)` by
        (gen_tac >> irule immutable_pop_empty >>
         simp[read_place_def, get_immutables_def, get_address_immutables_def,
              bind_def, return_def, lift_sum_def, lift_option_type_def]) >>
      qpat_x_assum `!ctx. ?j. _` (qspec_then `ctx` strip_assume_tac) >>
      simp[gas_summary_at_def, gas_marked_exec_def] >>
      qexistsl [`INR (Error (RuntimeError "pop empty"))`, `es`,
        `Abort Revert_abort (t' with vs_inst_idx := j)`] >>
      simp[expr_exit_def, exit_result_def]) >>
  `!x. hdr = Var x ==> not_fresh_at sm x` by fs[imm_target_post_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region t = SOME 0w /\
      (!x. region = Var x ==> not_fresh_at sm x)` by
    (fs[local_ptrs_reserved_def, ci_mono_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `mload (w2n (n2w (k+off):bytes32)) t <> 0w` by
    (simp[arithmeticTheory.ADD_COMM] >> Cases_on `vs` >> gvs[]) >>
  drule_all immutable_pop_run >> strip_tac >>
  drule_all immutable_pop_gas_path >> strip_tac >>
  drule_all assign_subscripts_replace_readback >>
  disch_then (qspec_then `ArrayV (DynArrayV (FRONT vs))` strip_assume_tac) >>
  drule_all pop_immutable_place_live >> strip_tac >>
  drule_all immutable_pop_stmt_state_rel >> strip_tac >>
  `n2w (LENGTH vs) - 1w = (n2w (LENGTH vs-1):bytes32)` by
    (Cases_on `vs` >> gvs[arithmeticTheory.ADD1, wordsTheory.n2w_sub]) >>
  `mload (k+off) t = n2w (LENGTH vs)` by
    (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> asm_rewrite_tac[]) >>
  `u.vs_memory = (mstore (off+k) (n2w (LENGTH vs-1)) t).vs_memory` by
    (qpat_x_assum `u.vs_memory = _` mp_tac >>
     simp[arithmeticTheory.ADD_COMM]) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func cenv cx fin stored` >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >>
     qpat_x_assum `ci_mono sa sm` mp_tac >> simp[ci_mono_def]) >>
  `stmt_state_rel ctx func cenv cx fin u` by
    (irule immutable_suffix_stmt_frame >>
     qexistsl [`stored`, `sm`] >>
     simp[Abbr `stored`, mstore_def, write_memory_with_expansion_def,
          lookup_var_def] >>
     qpat_x_assum `u = _` mp_tac >>
     simp[venom_state_component_equality, mstore_def,
          write_memory_with_expansion_def]) >>
  `wb_frame cenv es sm t stored` by
    (drule_all immutable_store_wb_frame >>
     disch_then (qspecl_then [`n2w (LENGTH vs-1)`, `sm`] mp_tac) >>
     simp[Abbr `stored`]) >>
  `u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `u = _` mp_tac >> simp[venom_state_component_equality]) >>
  `wb_frame cenv es sm t u` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >> qexistsl [`sm`, `stored`] >>
     simp[Abbr `stored`, mstore_def, write_memory_with_expansion_def,
          lookup_var_def]) >>
  `wb_frame cenv es0 sa s0 t` by
    (qpat_x_assum `imm_target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac std_ss [imm_target_post_def, wb_frame_def] >>
     metis_tac[]) >>
  `wb_frame cenv es0 sa s0 u` by
    (`sa.cs_next_var <= sm.cs_next_var /\
      sa.cs_next_id <= sm.cs_next_id` by
       (qpat_x_assum `ci_mono sa sm` mp_tac >> simp[ci_mono_def]) >>
     drule_all exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
  `val_in_memory etv (LAST vs)
      (off + (k+32+(LENGTH vs-1)*type_memory_size etv)) u.vs_memory` by
    (`(mstore (k+off) (n2w (LENGTH vs-1)) t).vs_memory = stored.vs_memory` by
       simp[NoAsms, Abbr `stored`, arithmeticTheory.ADD_COMM] >>
     `k + (off + (type_memory_size etv * (LENGTH vs-1) + 32)) =
      off + (k+32+(LENGTH vs-1)*type_memory_size etv)` by
       (simp[NoAsms, arithmeticTheory.MULT_COMM] >> decide_tac) >>
     metis_tac[]) >>
  `eval_operand q u = SOME
      (n2w (off + (k+32+(LENGTH vs-1)*type_memory_size etv)))` by
    (qpat_x_assum `eval_operand q u = _` mp_tac >>
     qpat_assum `mload (k+off) t = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `n2w (LENGTH vs) - 1w = _` (fn th => rewrite_tac[th]) >>
     `w2n (n2w (k+off):bytes32) = k+off` by simp[] >>
     pop_assum (fn th => rewrite_tac[th]) >>
     qpat_assum `mload (k+off) t = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `n2w (LENGTH vs) - 1w = _` (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac[wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w] >>
     `k+off+32+(LENGTH vs-1)*type_memory_size etv =
      off+(k+32+(LENGTH vs-1)*type_memory_size etv)` by decide_tac >>
     pop_assum (fn th => rewrite_tac[th])) >>
  `?imms'. ALOOKUP fin.immutables cx.txn.target = SOME imms' /\
      FLOOKUP (get_source_immutables cenv.ce_module imms') id =
        SOME (itv,updated)` by
    simp[Abbr `fin`, alistTheory.ALOOKUP_def, finite_mapTheory.FLOOKUP_UPDATE,
         vyperTypeInitialStateTheory.get_source_immutables_set_same] >>
  `value_has_type etv (LAST vs) /\
   (k+32+(LENGTH vs-1)*type_memory_size etv) + type_memory_size etv <=
     type_memory_size itv` by metis_tac[] >>
  `read_result cx (Value (LAST vs)) fin = (INL (LAST vs),fin)` by
    simp[read_result_def, return_def] >>
  `vv_post ctx func cenv cx (Pop ann bt) es0 sa r s0 fin
      (Value (LAST vs)) (LocatedValue ann (mk_ptr q LocCode)) u` by
    (drule_all (SRULE [expr_type_def]
       (Q.INST [`e` |-> `Pop ann bt`] immutable_ctor_pointer_post)) >> simp[]) >>
  `!tail. pop_place cx (ImmutablePlace cenv.ce_module id path)
      (es with gas_obs := tail) =
      (INL (Value (LAST vs)),fin with gas_obs := tail)` by
    (gen_tac >>
     mp_tac (Q.INST [`es` |-> `es with gas_obs := tail`,
       `src` |-> `cenv.ce_module`, `tv` |-> `itv`, `a` |-> `iv`]
       (SPEC_ALL pop_immutable_place_live)) >>
     simp[Abbr `fin`]) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl [`INL (Value (LAST vs))`, `fin`,
    `OK (u with vs_inst_idx := LENGTH r.cs_current_insts)`] >>
  `fin with gas_obs := [] = fin` by
    (simp[Abbr `fin`, evaluation_state_component_equality]) >>
  simp[]
QED

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
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Pop ann bt)` by
    fs[expr_body_pre_def] >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    fs[well_typed_expr_def] >>
  pop_assum strip_assume_tac >>
  `target_indices_pre cenv cx env bt` by
    (irule target_indices_pre_of_body >>
     fs[expr_body_pre_def, byte_widths_expr_def, alloc_limits_expr_def,
        int_calls_expr_def, expr_has_evm_run_def, supported_expr_exists_def,
        expr_abi_decode_target_root_def, expr_evm_run_root_def,
        call_operands_effect_root_def]) >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  PairCases_on `q` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr _ _ _ _ = ((hdr,loc,pt),sm)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `compile_dynarray_pop hdr ws esz T cenv.ce_imm_alloca lc sm` >>
  Cases_on
    `compile_dynarray_pop hdr ws esz T cenv.ce_imm_alloca lc sm` >>
  simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono sm r` by metis_tac[ci_mono_compile_dynarray_pop, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm r func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    metis_tac[nested_pop_target_admissible] >>
  drule_all imm_target_walk_place >>
  `eval_expr cx (Pop ann bt) = vyperState$bind (eval_target_place cx bt) (pop_place cx)` by
    simp[FUN_EQ_THM, Once evaluate_def, vyperStateTheory.bind_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists `marks`
  >- (disj1_tac >> suspend "summary") >>
  disj2_tac >> rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_place)
QED

Resume pop_nested_immutable_deploy_pure_sim[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`tres`, `tend`, `tr0`] strip_assume_tac) >>
  gvs[]
  >- suspend "normal" >>
  Cases_on `tres` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR exc) tr0` >>
  qexistsl_tac [`INR exc`, `tend`, `tr0`] >> simp[] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  metis_tac[expr_exit_INR_type]
QED

Resume pop_nested_immutable_deploy_pure_sim[normal]:
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,es with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env (Pop ann bt)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all pop_target_source_facts >> strip_tac >>
  `?iid path. p = ImmutablePlace cenv.ce_module iid path` by
    (fs[imm_target_post_def] >> Cases_on `p` >> gvs[imm_place_at_def]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  `lc = LocCode` by
    (fs[imm_target_post_def] >> Cases_on `lc` >> gvs[imm_place_at_def]) >>
  `loc = SOME LocCode /\ pt = SOME (ValPT (ArrayT ann (Dynamic n)))` by
    (qpat_x_assum `imm_target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac std_ss [imm_target_post_def] >> metis_tac[]) >>
  gvs[Abbr `lc`, Abbr `ws`, Abbr `esz`, word_scale_def,
      elem_size_in_location_def, is_slot_addressed_def] >>
  mp_tac (Q.INST [`es0` |-> `es`, `es` |-> `es with gas_obs := []`,
    `id` |-> `iid`, `pt` |-> `SOME (ValPT (ArrayT ann (Dynamic n)))`]
    nested_pop_immutable_suffix_sim) >>
  impl_tac >- simp[] >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`pres`, `pend`, `pr`]
    (CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`pres`, `pend`, `pr`] >>
  conj_tac
  >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
       |> REWRITE_RULE [APPEND_NIL]) >>
      qpat_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _`
        (irule_at Any) >> asm_rewrite_tac[]) >>
  gvs[]
QED

Finalise pop_nested_immutable_deploy_pure_sim

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
