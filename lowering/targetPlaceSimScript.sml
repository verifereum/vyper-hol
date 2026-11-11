(*
 * The target/place judgment (#636, Places)
 *
 * compile_get_target_ptr lowers an assignment target (and the array of a
 * pop) to a pointer, its location and its place type; the source evaluates
 * the target to a place (eval_base_place, then get_place for
 * eval_target_place).  target_sim relates the two: the target's fragment,
 * run from stmt_state_rel at the source state where the target is
 * evaluated, either reaches its end with stmt_state_rel at the state after
 * it and the pointer at the place the source returns (target_post), or,
 * where the source raises an error other than a type error, exits as
 * expr_exit allows.
 *
 * Where the pointer sits (place_ptr_rel), by the kind of place:
 *   - a local's place MemoryPlace x path: x's pointer plus the byte offset
 *     of path in x's type (mem_path_offset), in memory.  The offset is the
 *     type's, not the value's: a DynArray local reserves its capacity, so
 *     a place keeps its address while x's value changes (x[x.pop()]);
 *   - a storage or transient place: its slot, in storage or transient
 *     storage;
 *   - a mapping (HashMapRef): its slot, at the mapping's key and value
 *     types.
 * Immutables are left out (immutable_root): the lowering keeps them in
 * code (LocCode), which nothing relates to the source's immutables yet
 * (exprSimLeaves' compile_toplevel_immutable_sim).
 *
 * The offsets (mem_path_offset and its steps) are exprSim's, which the
 * live-locals frame locals_kept uses too.
 *
 * TOP-LEVEL:
 *   place_ptr_rel, place_readable, target_post, target_res_ok,
 *   target_sim             — the judgment
 *   target_env_ok, target_root, immutable_root, target_indices_pre,
 *   target_pre, target_case, target_idx_case — its premises and the shared
 *                          case form (as expr_vv_case: nocalls = T for
 *                          compile_expr_sim, F for the body simulation)
 *   target_name_case       — a local: its pointer, no code
 *   toplevel_target_env    — a module variable's compile env entries
 *   target_toplevel_case   — a storage or transient variable or a mapping:
 *                          its slot, no code
 * The steps (fields, subscripts) and the induction over targets are in
 * targetPlaceSimCases.
 *
 * Helpers: target_pre_sub,
 *   expr_sim_inv_local, target_post_refl, toplevel_decl_ce_vars, toplevel_target_decl
 *)

Theory targetPlaceSim
Ancestors
  exprSimFieldLayout
  targetPlaceSimDefs
  exprSimHypsDefs placeTypingProps
  loweringPosts
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimAttributeFields
  exprLowering exprLoweringProps compileEnv loweringStateRelDefs
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants vyperPlaceResultTyping
  venomState venomInst
Libs
  pairLib

(* ===== The judgment ===== *)

(* The source results the judgment speaks of: a place or a mapping, an
   error other than a type error, or an assertion. *)

(* The judgment: the target's fragment of bt, typed vt, run from a state
   related at es, reaches its end in target_post on a place, and exits as
   expr_exit allows on an error. *)

(* ===== Premises ===== *)

(* The compile environment's module tables agree with the declarations:
   a storage or transient variable is not a mapping and has its declared
   type, a mapping its declared key and value types.  The body
   simulation's body_inv gives this for the main module (build_hashmap_info,
   build_var_type_map). *)
Definition target_env_ok_def:
  target_env_ok cenv cx <=>
    !src id ts d id_str.
      get_module_code cx src = SOME ts /\
      find_var_decl_by_name id ts = SOME (d, id_str) ==>
      (!tr typ. d = StorageVarDecl tr typ ==>
                cenv.ce_hashmap_info (src,id) = NONE /\
                cenv.ce_module_var_type (src,id) = SOME typ) /\
      (!tr kt vt. d = HashMapVarDecl tr kt vt ==>
                  ?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt))
End

Definition target_root_def:
  target_root (NameTarget id) = NameTarget id /\
  target_root (TopLevelNameTarget nsid) = TopLevelNameTarget nsid /\
  target_root (AttributeTarget t fld) = target_root t /\
  target_root (SubscriptTarget t e) = target_root t
End

(* The target is inside an immutable or a constant: a module name with no
   storage declaration. *)
Definition immutable_root_def:
  immutable_root cx bt <=>
    ?src id ts. target_root bt = TopLevelNameTarget (src,id) /\
                get_module_code cx src = SOME ts /\
                find_var_decl_by_name id ts = NONE
End

(* Every index of the target meets expr_body_pre wherever expr_sim_inv
   holds, the static part of expr_body_pre, and no subscript of it is a
   rejected overlap (target_subscript_overlap). *)
Definition target_indices_pre_def:
  target_indices_pre cenv cx env (NameTarget id) = T /\
  target_indices_pre cenv cx env (TopLevelNameTarget nsid) = T /\
  target_indices_pre cenv cx env (AttributeTarget t fld) =
    target_indices_pre cenv cx env t /\
  target_indices_pre cenv cx env (SubscriptTarget t e) =
    (target_indices_pre cenv cx env t /\ ~target_subscript_overlap cenv t e /\
     !es. expr_sim_inv cenv cx env es ==> expr_body_pre cenv cx env e es)
End

Definition target_pre_def:
  target_pre cenv cx env bt es <=>
    expr_sim_inv cenv cx env es /\ ~immutable_root cx bt /\
    target_indices_pre cenv cx env bt
End

(* The shared case form, as expr_vv_case: target_sim at every state meeting
   target_pre, with no internal call in the target if nocalls. *)
Definition target_case_def:
  target_case nocalls ctx func cenv cx bt <=>
    !env es.
      target_pre cenv cx env bt es /\ (nocalls ==> int_calls_target bt = []) ==>
      target_sim ctx func cenv cx env bt es
End

(* The indices' judgments, each if its base can evaluate, as the body
   simulation's body_base_target_ok has them. *)
Definition target_idx_case_def:
  target_idx_case nocalls ctx func cenv cx (NameTarget id) = T /\
  target_idx_case nocalls ctx func cenv cx (TopLevelNameTarget nsid) = T /\
  target_idx_case nocalls ctx func cenv cx (AttributeTarget t fld) =
    target_idx_case nocalls ctx func cenv cx t /\
  target_idx_case nocalls ctx func cenv cx (SubscriptTarget t e) =
    (target_idx_case nocalls ctx func cenv cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      expr_sim_case nocalls ctx func cenv cx e /\
      expr_vv_case nocalls ctx func cenv cx e))
End

Theorem target_pre_sub:
  (!cenv cx env t fld es.
     target_pre cenv cx env (AttributeTarget t fld) es ==>
     target_pre cenv cx env t es) /\
  (!cenv cx env t e es.
     target_pre cenv cx env (SubscriptTarget t e) es ==>
     target_pre cenv cx env t es)
Proof
  rw[target_pre_def, immutable_root_def, target_root_def,
     target_indices_pre_def]
QED

(* ===== Locals ===== *)

(* A local the typing knows: its pointer variable, its scope entry, and its
   declared type evaluating to the entry's type.  As stmtSimAugAssign's
   expr_sim_inv_local, restated here so the judgment does not depend on the
   statement simulation. *)
Theorem expr_sim_inv_local[local]:
  !cenv cx env es id ty.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty ==>
    (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (?entry. lookup_scopes id es.scopes = SOME entry) /\
    !entry. lookup_scopes id es.scopes = SOME entry ==>
            evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  rpt gen_tac >> strip_tac >>
  fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
  qpat_x_assum `!id ty. _ ==> IS_SOME _` drule >>
  qpat_x_assum `!id ty. _ ==> ?p sz. _` drule >>
  simp[optionTheory.IS_SOME_EXISTS] >> rpt strip_tac >>
  qpat_x_assum `!id ty entry. _ /\ _ ==> _` drule_all >> simp[]
QED

(* ===== Leaves ===== *)

(* No code, and the post at the start state. *)
Theorem target_post_refl[local]:
  !ctx func cenv cx es sa s pv vt r.
    stmt_state_rel ctx func cenv cx es s /\
    (?w. eval_operand (FST r) s = SOME w /\
         place_ptr_rel cenv cx s pv w (FST (SND r)) vt) /\
    SND (SND r) = SOME (value_type_place vt) /\
    (!x. FST r = Var x ==> not_fresh_at sa x) /\
    place_readable cx es pv ==>
    target_post ctx func cenv cx es sa sa s es pv vt r s
Proof
  rw[target_post_def] >> metis_tac[]
QED

(* A local: its place MemoryPlace x [] at its pointer, no code. *)
Theorem target_name_case:
  !nocalls ctx func cenv cx id.
    target_case nocalls ctx func cenv cx (NameTarget id)
Proof
  rw[target_case_def, target_sim_def, target_pre_def] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  simp[compile_get_target_ptr_def, comp_return_def] >> strip_tac >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gasOutcomeTheory.gas_outcome_def, gasSummaryTheory.gas_summary_at_def] >> qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def, fragGasPathTheory.gas_path_rules,
          Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def] >>
  simp[exit_result_def] >>
  `?b. lookup_var p s0 = SOME b` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  simp[target_post_def, value_type_place_def] >>
  simp[eval_operand_def, place_ptr_rel_def, mem_path_offset_def,
       place_readable_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, wordsTheory.WORD_ADD_0]
QED

(* The compile environment holds a storage, transient or mapping variable
   at the layout's slot (storage_vars_rel, transient_vars_rel). *)
Theorem toplevel_decl_ce_vars[local]:
  !cenv cx src id ts d id_str tr slot.
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (d, id_str) /\
    var_decl_transient d = tr /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot ==>
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  rpt strip_tac >> Cases_on `tr` >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >> metis_tac[]
QED

(* A module variable target, typed: a storage or transient variable of its
   declared type, or a mapping of its declared key and value types.
   bare_global_assignable and bare_globals name immutables, which have no
   storage declaration. *)
Theorem toplevel_target_decl[local]:
  !env cx st src id vt.
    type_place_target env (TopLevelNameTarget (src,id)) = SOME vt /\
    env_consistent env cx st /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts <> NONE) ==>
    ?ts tr id_str slot.
      get_module_code cx src = SOME ts /\
      ((?ty tv. vt = Type ty /\
                find_var_decl_by_name id ts =
                  SOME (StorageVarDecl tr ty, id_str) /\
                evaluate_type (get_tenv cx) ty = SOME tv /\
                lookup_var_slot_from_layout cx tr src id_str = SOME slot) \/
       (?kt vt'. vt = HashMapT kt vt' /\
                 find_var_decl_by_name id ts =
                   SOME (HashMapVarDecl tr kt vt', id_str) /\
                 lookup_var_slot_from_layout cx tr src id_str = SOME slot))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all type_place_target_global_lookup >> strip_tac >>
  Cases_on `vt`
  >- (Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
          gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
      drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

(* A typed module variable target has its compile environment entries: a
   storage or transient variable is not a mapping and has its declared
   type, a mapping its declared key and value types (expr_sim_inv's
   storage clause and place_map_tables_agree_on_defined). *)
Theorem toplevel_target_env:
  !cenv cx env es src id vt ts d id_str.
    expr_sim_inv cenv cx env es /\
    type_place_target env (TopLevelNameTarget (src,id)) = SOME vt /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (d, id_str) ==>
    (!tr typ. d = StorageVarDecl tr typ ==>
              cenv.ce_hashmap_info (src,id) = NONE /\
              cenv.ce_module_var_type (src,id) = SOME typ) /\
    (!tr kt vt'. d = HashMapVarDecl tr kt vt' ==>
                 ?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt'))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[expr_sim_inv_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `!ts'. get_module_code cx src = SOME ts' ==>
         find_var_decl_by_name id ts' <> NONE` by gvs[] >>
  drule_all toplevel_target_decl >> strip_tac >> gvs[] >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt')` by
    metis_tac[type_place_target_global_lookup] >>
  `place_map_tables_agree_on_defined cenv env` by fs[expr_sim_inv_def] >>
  qpat_x_assum `place_map_tables_agree_on_defined _ _` mp_tac >>
  simp[place_map_tables_agree_on_defined_def] >>
  disch_then drule >>
  Cases_on `cenv.ce_hashmap_info (src,id)` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

(* A storage, transient or mapping variable: its slot, no code. *)
Theorem target_toplevel_case:
  !nocalls ctx func cenv cx nsid.
    target_case nocalls ctx func cenv cx (TopLevelNameTarget nsid)
Proof
  rw[target_case_def, target_sim_def, target_pre_def] >>
  PairCases_on `nsid` >> rename1 `TopLevelNameTarget (src,id)` >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts <> NONE` by
    (fs[immutable_root_def, target_root_def] >> metis_tac[]) >>
  drule_all toplevel_target_decl >> strip_tac >> gvs[]
  >- suspend "storage" >>
  suspend "mapping"
QED

Resume target_toplevel_case[storage]:
  `cenv.ce_hashmap_info (src,id) = NONE /\
   cenv.ce_module_var_type (src,id) = SOME ty` by
    metis_tac[toplevel_target_env] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- gvs[stmt_state_rel_def, state_rel_def] >>
  qspecl_then [`cenv`, `cx`, `src`, `id`, `ts`, `StorageVarDecl tr ty`,
               `id_str`, `tr`, `slot`] mp_tac toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gasOutcomeTheory.gas_outcome_def, gasSummaryTheory.gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tv))`, `es`, `OK s0`] >>
  conj_tac
  >- (`!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
            (INL (PlaceR (StoragePlace tr (n2w slot) tv)), es with gas_obs := gs)` by
        (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
           bind_def, lift_option_type_def, return_def, LET_THM]) >>
      simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
           fragGasPathTheory.gas_path_rules]) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exit_result_def, target_post_def] >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Resume target_toplevel_case[mapping]:
  `?tr'. cenv.ce_hashmap_info (src,id) = SOME (tr',kt,vt')` by
    metis_tac[toplevel_target_env] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- gvs[stmt_state_rel_def, state_rel_def] >>
  qspecl_then [`cenv`, `cx`, `src`, `id`, `ts`, `HashMapVarDecl tr kt vt'`,
               `id_str`, `tr`, `slot`] mp_tac toplevel_decl_ce_vars >>
  simp[var_decl_transient_def] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[gasOutcomeTheory.gas_outcome_def, gasSummaryTheory.gas_summary_at_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (HashMapRef tr (n2w slot) kt vt')`, `es`, `OK s0`] >>
  conj_tac
  >- (`!gs. eval_base_place cx (TopLevelNameTarget (src,id)) (es with gas_obs := gs) =
            (INL (HashMapRef tr (n2w slot) kt vt'), es with gas_obs := gs)` by
        (gen_tac >> asm_simp_tac (srw_ss()) [Once evaluate_def, lookup_global_def,
           bind_def, lift_option_type_def, return_def, LET_THM]) >>
      simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
           fragGasPathTheory.gas_path_rules]) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_get_target_ptr_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[exit_result_def, target_post_def] >>
  simp[eval_operand_def, place_ptr_rel_def, slot_loc_def,
       value_type_place_def, place_readable_def]
QED

Finalise target_toplevel_case
