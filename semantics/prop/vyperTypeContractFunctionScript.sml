(*
 * Checked-contract type-soundness bridge properties.
 *
 * The definitions in vyperTypeContract build a contract_type_artifact from a
 * module set and check that declarations/bodies satisfy the static rules.  This
 * theory proves that successful checking supplies the proof-facing consistency
 * predicates used by the type-soundness theorems.
 *)

Theory vyperTypeContractFunction
Ancestors
  list rich_list arithmetic finite_map alist option pair patricia_casts
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues vyperTypeBindArguments
  vyperTypeStmtSoundness vyperTypeInitialState vyperPureExpr vyperEvalPreservesScopes vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom vyperScopePreservation vyperStatePreservation
  vyperTypeContractStaticMaps vyperTypeContractContext
Libs
  wordsLib

val _ = Parse.hide "body";

Definition static_maps_transfer_env_def:
  static_maps_transfer_env env1 env2 <=>
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==>
       FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==>
       FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==>
       FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==>
       FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==>
       FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\
            FLOOKUP env1.bare_globals k = NONE ==>
       FLOOKUP env2.bare_globals k = NONE)
End
Theorem well_typed_defaults_static_maps_transfer[local]:
  well_typed_exprs (defaults_env env1) dflts /\
  env2.current_src = env1.current_src /\
  env2.type_defs = env1.type_defs /\
  (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
  (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
  (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
  (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
  (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
  (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
  well_typed_exprs (defaults_env env2) dflts
Proof
  rw[defaults_env_def] >>
  irule (cj 4 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem static_maps_transfer_env_extend_local[local]:
  static_maps_transfer_env env1 env2 ==>
  static_maps_transfer_env (extend_local env1 n ty a) (extend_local env2 n ty a)
Proof
  rw[static_maps_transfer_env_def, extend_local_def]
QED

Theorem well_typed_expr_static_maps_transfer_env[local]:
  well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 ==> well_typed_expr env2 e
Proof
  rw[static_maps_transfer_env_def] >>
  irule (cj 1 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem well_typed_exprs_static_maps_transfer_env[local]:
  well_typed_exprs env1 es /\ static_maps_transfer_env env1 env2 ==> well_typed_exprs env2 es
Proof
  rw[static_maps_transfer_env_def] >>
  irule (cj 4 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem type_place_expr_static_maps_transfer_env[local]:
  type_place_expr env1 e = SOME vt /\ static_maps_transfer_env env1 env2 ==>
  type_place_expr env2 e = SOME vt
Proof
  rw[static_maps_transfer_env_def] >>
  drule (cj 2 well_typed_static_maps_transfer) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[]
QED

Theorem type_place_target_static_maps_transfer_env[local]:
  type_place_target env1 tgt = SOME vt /\ static_maps_transfer_env env1 env2 ==>
  type_place_target env2 tgt = SOME vt
Proof
  rw[static_maps_transfer_env_def] >>
  drule (cj 3 well_typed_static_maps_transfer) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[]
QED

Theorem type_place_expr_static_maps_transfer_env_reverse_SOME[local]:
  !e env1 env2 vt.
    well_typed_expr env1 e /\
    static_maps_transfer_env env1 env2 /\
    type_place_expr env2 e = SOME vt ==>
    type_place_expr env1 e = SOME vt
Proof
  Induct >>
  rw[well_typed_expr_def, static_maps_transfer_env_def, AllCaseEqs()] >>
  gvs[] >>
  TRY (PairCases_on `p` >> gvs[well_typed_expr_def, vtype_annotation_ok_def]) >>
  gvs[well_typed_expr_def, vtype_annotation_ok_def] >>
  TRY (rename1 `FLOOKUP env1.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` >>
       `FLOOKUP env2.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by metis_tac[] >>
       gvs[]) >>
  TRY (`static_maps_transfer_env env1 env2` by rw[static_maps_transfer_env_def]) >>
  TRY (rename1 `subscript_vtype base_vt (expr_type idx) = SOME result_vt` >>
       qpat_x_assum `!env1 env2 vt. well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 /\ type_place_expr env2 e = SOME vt ==> type_place_expr env1 e = SOME vt`
         (qspecl_then [`env1`,`env2`,`base_vt`] mp_tac) >>
       simp[] >> strip_tac >>
       qexists `base_vt` >> simp[]) >>
  TRY (rename1 `type_place_expr env2 e = SOME env2_vt` >>
       qpat_x_assum `!env1 env2 vt. well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 /\ type_place_expr env2 e = SOME vt ==> type_place_expr env1 e = SOME vt`
         (qspecl_then [`env1`,`env2`,`env2_vt`] mp_tac) >>
       simp[] >> strip_tac >> gvs[]) >>
  TRY (rename1 `type_place_expr env1 e = SOME base_vt` >>
       `type_place_expr env2 e = SOME base_vt` by metis_tac[type_place_expr_static_maps_transfer_env] >>
       gvs[]) >>
  metis_tac[]
QED

Theorem type_place_expr_no_hash_static_maps_transfer_env[local]:
  well_typed_expr env1 e /\
  static_maps_transfer_env env1 env2 /\
  (!kt vt. type_place_expr env1 e <> SOME (HashMapT kt vt)) ==>
  (!kt vt. type_place_expr env2 e <> SOME (HashMapT kt vt))
Proof
  rw[] >>
  strip_tac >>
  drule_all type_place_expr_static_maps_transfer_env_reverse_SOME >>
  metis_tac[]
QED




Theorem well_typed_atarget_static_maps_transfer_env[local]:
  !env1 tgt ty.
    well_typed_atarget env1 tgt ty ==>
    !env2. static_maps_transfer_env env1 env2 ==>
      well_typed_atarget env2 tgt ty
Proof
  recInduct well_typed_atarget_ind >>
  rw[well_typed_atarget_def, well_typed_target_def]
  >- metis_tac[type_place_target_static_maps_transfer_env]
  >> gvs[LIST_REL_EL_EQN] >>
  rw[] >>
  first_x_assum irule >>
  simp[MEM_EL] >>
  conj_tac >- (qexists `n` >> simp[]) >>
  qexists `tys` >> qexists `n` >> simp[] >>
  first_x_assum irule >>
  simp[]
QED

Theorem well_typed_iterator_static_maps_transfer_env[local]:
  well_typed_iterator env1 typ it /\ static_maps_transfer_env env1 env2 ==>
  well_typed_iterator env2 typ it
Proof
  Cases_on `it` >>
  rw[well_typed_iterator_def] >>
  metis_tac[well_typed_expr_static_maps_transfer_env]
QED

Theorem type_stmt_static_maps_transfer_mutual[local]:
  (!env1 ret s env1'.
     type_stmt env1 ret s = SOME env1' ==>
     !env2.
       static_maps_transfer_env env1 env2 ==>
       ?env2'. type_stmt env2 ret s = SOME env2' /\ static_maps_transfer_env env1' env2') /\
  (!env1 ret ss env1'.
     type_stmts env1 ret ss = SOME env1' ==>
     !env2.
       static_maps_transfer_env env1 env2 ==>
       ?env2'. type_stmts env2 ret ss = SOME env2' /\ static_maps_transfer_env env1' env2')
Proof
  ho_match_mp_tac type_stmt_ind >>
  rw[type_stmt_def, AllCaseEqs()] >>
  gvs[] >>
  TRY (rename1 `well_typed_expr env1 e` >> qexists `env2` >> simp[] >>
       conj_tac >- metis_tac[type_place_expr_no_hash_static_maps_transfer_env] >>
       irule well_typed_expr_static_maps_transfer_env >> simp[]) >>
  rpt (first_x_assum (drule_then strip_assume_tac)) >>
  gvs[] >>
  rpt (first_x_assum (drule_then strip_assume_tac)) >>
  gvs[] >>
  TRY (irule_at Any static_maps_transfer_env_extend_local >> simp[]) >>
  TRY (irule_at Any well_typed_expr_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any well_typed_exprs_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any type_place_target_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any type_place_expr_no_hash_static_maps_transfer_env >> simp[]) >>
  TRY (rename1 `?env. static_maps_transfer_env env env2 /\ well_typed_expr env expr` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `?env. (!kt vt. type_place_expr env expr <> SOME (HashMapT kt vt)) /\ static_maps_transfer_env env env2 /\ well_typed_expr env expr` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `?env. static_maps_transfer_env env env2 /\ well_typed_exprs env es` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `assignable_type env2.type_defs ty` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `assignable_type env2.type_defs (expr_type e)` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `string_to_num id NOTIN FDOM env2.var_types` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `type_place_target env1 bt = SOME (Type (ArrayT ty (Dynamic n)))` >>
       qexistsl [`n`,`env1`,`env1`] >> simp[static_maps_transfer_env_def]) >>
  TRY (rename1 `well_typed_atarget env1 tgt (expr_type e)` >>
       irule well_typed_atarget_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `well_typed_target env1 bt ty` >>
       gvs[well_typed_target_def] >>
       irule type_place_target_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `IS_SOME (type_stmts env2 ret ss)` >>
       metis_tac[IS_SOME_EXISTS]) >>
  TRY (rename1 `IS_SOME (type_stmts env2 ret ss')` >>
       metis_tac[IS_SOME_EXISTS]) >>
  TRY (rename1 `IS_SOME (type_stmts (extend_local env2 (string_to_num id) typ F) ret ss)` >>
       metis_tac[IS_SOME_EXISTS, static_maps_transfer_env_extend_local]) >>
  TRY (rename1 `well_typed_iterator env2 typ it` >>
       irule well_typed_iterator_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  gvs[static_maps_transfer_env_def] >>
  metis_tac[static_maps_transfer_env_extend_local,
            well_typed_expr_static_maps_transfer_env,
            well_typed_exprs_static_maps_transfer_env,
            well_typed_atarget_static_maps_transfer_env,
            well_typed_iterator_static_maps_transfer_env,
            type_place_target_static_maps_transfer_env,
            type_place_expr_no_hash_static_maps_transfer_env]
QED


Theorem type_stmts_static_maps_transfer[local]:
  type_stmts env1 ret body = SOME env_after /\
  static_maps_transfer_env env1 env2 ==>
  ?env_after2. type_stmts env2 ret body = SOME env_after2
Proof
  rw[] >>
  drule (cj 2 type_stmt_static_maps_transfer_mutual) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[] >>
  metis_tac[]
QED

Theorem FOLDL_extend_local_args_empty_locals[local]:
  !args (base1 : typing_env) (base2 : typing_env).
    base1.var_types = base2.var_types /\
    base1.var_assignable = base2.var_assignable ==>
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base1 args).var_types =
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base2 args).var_types /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base1 args).var_assignable =
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base2 args).var_assignable
Proof
  Induct >> rw[] >>
  PairCases_on `h` >>
  first_x_assum (qspecl_then [`extend_local base1 (string_to_num h0) h1 T`,
                               `extend_local base2 (string_to_num h0) h1 T`] mp_tac) >>
  simp[extend_local_def]
QED

Theorem function_entry_env_static_maps_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx src) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx src) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx src) /\
  (!src' id ty. FLOOKUP bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src' = SOME ts /\
          FLOOKUP toplevel_vtypes (src',id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) /\
  env_body = FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
    (<| current_src := entry_src;
       var_types := FEMPTY;
       var_assignable := FEMPTY;
       bare_globals := bare_globals;
       bare_global_assignable := bare_global_assignable;
       toplevel_vtypes := toplevel_vtypes;
       type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
       fn_sigs := fn_sigs;
       flag_members := flag_members |>) args ==>
  static_maps_transfer_env (function_entry_env art mods entry_src args) env_body
Proof
  rw[static_maps_transfer_env_def]
  >- simp[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static]
  >- simp[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static,
           get_tenv_def, initial_evaluation_context_def]
  >- (rw[function_entry_env_def, artifact_env_def] >>
      irule (cj 1 FOLDL_extend_local_args_empty_locals) >> simp[])
  >- (rw[function_entry_env_def, artifact_env_def] >>
      irule (cj 2 FOLDL_extend_local_args_empty_locals) >> simp[])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_fn_sigs_lookup_transfer_initial])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_bare_globals_lookup_transfer_initial])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_bare_global_assignable_lookup_transfer_initial])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_toplevel_vtypes_lookup_transfer_initial])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_flag_members_lookup_transfer_initial])
  >> (simp[FOLDL_extend_local_args_static] >>
      PairCases_on `k` >>
      irule artifact_toplevel_non_bare_globals_NONE_transfer_initial >>
      qexistsl [`tx.target`, `args`, `art`, `src`, `entry_src`, `layouts`, `mods`, `sources`, `toplevel_vtypes`, `tx`, `vt`] >>
      simp[])
QED

Theorem function_entry_env_static_maps_transfer_initial_explicit[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx src) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx src) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx src) /\
  (!src' id ty. FLOOKUP bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src' = SOME ts /\
          FLOOKUP toplevel_vtypes (src',id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) ==>
  static_maps_transfer_env (function_entry_env art mods entry_src args)
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<| current_src := entry_src;
         var_types := FEMPTY;
         var_assignable := FEMPTY;
         bare_globals := bare_globals;
         bare_global_assignable := bare_global_assignable;
         toplevel_vtypes := toplevel_vtypes;
         type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
         fn_sigs := fn_sigs;
         flag_members := flag_members |>) args)
Proof
  rw[] >>
  irule function_entry_env_static_maps_transfer_initial >>
  qexistsl [`tx.target`, `bare_global_assignable`, `bare_globals`, `flag_members`, `fn_sigs`,
            `layouts`, `sources`, `src`, `toplevel_vtypes`, `tx`] >>
  simp[]
QED
Theorem check_function_body_static_maps_transfer_initial[local]:
  !layouts addr mods art sources tx fn_sigs bare_globals bare_global_assignable
   toplevel_vtypes flag_members entry_src mut nr args dflts ret body.
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx src) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx src) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx src) /\
  (!src' id ty. FLOOKUP bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src' = SOME ts /\
          FLOOKUP toplevel_vtypes (src',id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) /\
  check_function_body layouts addr mods art entry_src mut nr args dflts ret body ==>
  ?env_body ret_tv env_after.
    env_body.current_src = entry_src /\
    env_body.type_defs = get_tenv (initial_evaluation_context sources layouts tx src) /\
    env_body.fn_sigs = fn_sigs /\
    env_body.bare_globals = bare_globals /\
    env_body.bare_global_assignable = bare_global_assignable /\
    env_body.toplevel_vtypes = toplevel_vtypes /\
    env_body.flag_members = flag_members /\
    evaluate_type (get_tenv (initial_evaluation_context sources layouts tx src)) ret = SOME ret_tv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args)
Proof
  rpt strip_tac >>
  gns[check_function_body_def] >>
  `?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv` by
    (Cases_on `evaluate_type (type_env_all_modules mods) ret` >> gvs[]) >>
  `?env_after_art. type_stmts (function_entry_env art mods entry_src args) ret body = SOME env_after_art` by
    (Cases_on `type_stmts (function_entry_env art mods entry_src args) ret body` >> gvs[]) >>
  `static_maps_transfer_env (function_entry_env art mods entry_src args)
     (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args)` by
    (irule function_entry_env_static_maps_transfer_initial_explicit >>
     simp[]) >>
  `?env_after. type_stmts
     (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args) ret body = SOME env_after` by
    (drule type_stmts_static_maps_transfer >>
     disch_then (qspec_then `FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args` mp_tac) >>
     simp[]) >>
  qexistsl [`FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args`, `ret_tv`, `env_after`] >>
  simp[FOLDL_extend_local_args_static, get_tenv_def, initial_evaluation_context_def] >>
  conj_tac >- (irule well_typed_defaults_static_maps_transfer >>
                 qexists `function_entry_env art mods entry_src args` >>
                 gvs[static_maps_transfer_env_def, get_tenv_def, initial_evaluation_context_def]) >>
  conj_tac >- (rpt strip_tac >> gvs[params_ok_def] >>
                 drule_all FOLDL_extend_local_args_formal_lookup >> simp[]) >>
  conj_tac >- (rpt strip_tac >> gvs[params_ok_def] >>
                 drule_all FOLDL_extend_local_args_var_types_range >> simp[]) >>
  rpt strip_tac >> gvs[params_ok_def] >>
  drule_all FOLDL_extend_local_args_var_assignable_range >> simp[]
QED
Theorem check_contract_lookup_callable_function_F_body[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  lookup_callable_function F fn ts = SOME (fm,nr,args,dflts,ret,body) ==>
  check_function_body layouts addr mods art src fm nr args dflts ret body
Proof
  rw[] >>
  drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  drule_all check_contract_function_body_MEM >> simp[]
QED

Theorem check_contract_functions_well_typed_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  functions_well_typed (initial_evaluation_context sources layouts tx src)
Proof
  simp[functions_well_typed_def] >>
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `ALOOKUP mods src_id_opt = SOME ts` by
    gvs[get_module_code_def, initial_evaluation_context_def] >>
  conj_tac >-
   (`check_function_body layouts addr mods art src_id_opt fm nr args dflts ret body` by
      (irule check_contract_lookup_callable_function_F_body >>
       simp[] >>
       qexists `fn` >>
       gvs[initial_evaluation_context_def]) >>
    gvs[initial_evaluation_context_def, check_function_body_def] >>
    Cases_on `lookup_nonreentrant_slot layouts tx.target` >> gvs[] >>
    qexists `fn` >> simp[]) >>
  `check_function_body layouts addr mods art src_id_opt fm nr args dflts ret body` by
    (irule check_contract_lookup_callable_function_F_body >>
     simp[] >>
     qexists `fn` >>
     gvs[initial_evaluation_context_def]) >>
  drule_all check_function_body_static_maps_transfer_initial >>
  simp[]
QED

(* ===== Explicit external entry no-TypeError bridge for checked contracts ===== *)

Theorem functions_well_typed_stk_irrelevant[local]:
  !cx stk. functions_well_typed (cx with stk := stk) <=>
           functions_well_typed cx
Proof
  simp[functions_well_typed_def, get_module_code_def, get_tenv_def,
       fn_sigs_consistent_def, fn_sigs_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       well_formed_type_def]
QED

Theorem check_contract_functions_well_typed_initial_stk[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  functions_well_typed ((initial_evaluation_context sources layouts tx src) with stk := stk)
Proof
  rw[functions_well_typed_stk_irrelevant] >>
  irule check_contract_functions_well_typed_initial >>
  simp[]
QED

Theorem checked_contract_static_maps_transfer_inputs_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  fn_sigs_complete art.cta_fn_sigs (initial_evaluation_context sources layouts tx src) /\
  bare_globals_complete art.cta_bare_globals (initial_evaluation_context sources layouts tx src) /\
  bare_global_assignable_complete art.cta_bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  toplevel_vtypes_complete art.cta_toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  flag_members_complete art.cta_flag_members (initial_evaluation_context sources layouts tx src) /\
  (!src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src' = SOME ts /\
          FLOOKUP art.cta_toplevel_vtypes (src',id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT)
Proof
  rw[] >> rpt conj_tac
  >- (irule check_contract_fn_sigs_complete_initial >> simp[])
  >- (irule check_contract_bare_globals_complete_initial >> simp[])
  >- (irule check_contract_bare_global_assignable_complete_initial >> simp[])
  >- (irule check_contract_toplevel_vtypes_complete_initial >> simp[])
  >- (irule check_contract_flag_members_complete_initial >> simp[]) >>
  drule check_contract_bare_globals_consistent_initial >>
  simp[] >>
  disch_then (qspecl_then [`tx`, `sources`, `src'`, `id`, `ty`] mp_tac) >>
  simp[get_module_code_def, initial_evaluation_context_def]
QED

Theorem checked_explicit_external_body_typing_package:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts ==>
  ?env_body env_after.
    env_body.current_src = src /\
    env_body.type_defs = get_tenv (initial_evaluation_context am.sources am.layouts tx src) /\
    env_body.fn_sigs = art.cta_fn_sigs /\
    env_body.bare_globals = art.cta_bare_globals /\
    env_body.bare_global_assignable = art.cta_bare_global_assignable /\
    env_body.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env_body.flag_members = art.cta_flag_members /\
    type_stmts env_body ret body = SOME env_after /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T)
Proof
  rw[] >>
  `check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
    metis_tac[check_contract_function_body_MEM] >>
  `fn_sigs_complete art.cta_fn_sigs (initial_evaluation_context am.sources am.layouts tx src) /\
   bare_globals_complete art.cta_bare_globals (initial_evaluation_context am.sources am.layouts tx src) /\
   bare_global_assignable_complete art.cta_bare_global_assignable (initial_evaluation_context am.sources am.layouts tx src) /\
   toplevel_vtypes_complete art.cta_toplevel_vtypes (initial_evaluation_context am.sources am.layouts tx src) /\
   flag_members_complete art.cta_flag_members (initial_evaluation_context am.sources am.layouts tx src) /\
   (!src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ==>
      ?ts'. get_module_code (initial_evaluation_context am.sources am.layouts tx src) src' = SOME ts' /\
            FLOOKUP art.cta_toplevel_vtypes (src',id) = SOME (Type ty) /\
            is_bare_global_decl id ts' /\
            find_var_decl_by_num id ts' = NONE /\ ty <> NoneT)` by
    (irule checked_contract_static_maps_transfer_inputs_initial >> simp[]) >>
  qspecl_then
    [`am.layouts`, `tx.target`, `mods`, `art`, `am.sources`, `tx`,
     `art.cta_fn_sigs`, `art.cta_bare_globals`,
     `art.cta_bare_global_assignable`, `art.cta_toplevel_vtypes`,
     `art.cta_flag_members`, `src`, `mut`, `nr`, `args`, `dflts`, `ret`, `body`]
    mp_tac check_function_body_static_maps_transfer_initial >>
  simp[] >> rw[] >>
  qexistsl [`env_body`, `env_after`] >> simp[] >> metis_tac[]
QED

Theorem checked_explicit_external_entry_establishes_type_soundness_preconditions[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts /\
  context_well_typed
    ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)]) /\
  machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)])
    am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals ==>
  ?env_body env_after st.
    st = initial_state am [scope] /\
    functions_well_typed
      ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)]) /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body
      ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)]) st /\
    type_stmts env_body ret body = SOME env_after
Proof
  strip_tac >> gvs[] >>
  drule_all checked_explicit_external_body_typing_package >>
  strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  qexistsl [`env_body`, `env_after`] >>
  rw[initial_state_accounts_well_typed, initial_state_single_scope_well_typed] >-
    (irule check_contract_functions_well_typed_initial_stk >> simp[]) >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art mods env_body.current_src` >>
      rpt (conj_tac >- simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_with_current_src >>
      simp[])
  >- (`env_scopes_consistent env_body
         ((initial_evaluation_context am.sources am.layouts tx env_body.current_src) with stk := [(env_body.current_src,fn)])
         ((initial_state am []) with scopes := [scope])` suffices_by
        simp[initial_state_def] >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[])
  >- (irule immutables_ready_env_immutables_consistent >>
      qexists `artifact_env art mods src` >>
      gvs[artifact_env_def])
QED

Theorem check_contract_explicit_external_entry_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts /\
  context_well_typed
    ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)]) /\
  machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)])
    am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals ==>
  no_type_error_eval
    (eval_stmts
      ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)])
      body
      (initial_state am [scope]))
Proof
  metis_tac[
    checked_explicit_external_entry_establishes_type_soundness_preconditions,
    eval_stmts_no_type_error]
QED

Theorem checked_explicit_external_post_prefix_body_no_type_error_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_stmts cx body st)
Proof
  strip_tac >> gvs[] >>
  drule_all checked_explicit_external_body_typing_package >>
  strip_tac >>
  `functions_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    (irule check_contract_functions_well_typed_initial >> simp[]) >>
  irule eval_stmts_no_type_error >>
  simp[] >>
  rpt (conj_tac >- simp[]) >>
  qexistsl [`env_body`, `env_after`, `ret`] >> simp[] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art mods env_body.current_src` >>
      rpt (conj_tac >- simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_src >>
      simp[])
  >- (`(st with scopes := [scope]) = st` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[])
  >- (gvs[env_immutables_consistent_def] >>
      rw[] >>
      qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
      simp[immutables_ready_def] >>
      strip_tac >>
      first_x_assum drule_all >>
      simp[])
QED

Theorem immutables_ready_initial_evaluation_context_source:
  immutables_ready bare_globals toplevel_vtypes
    (initial_evaluation_context sources layouts tx NONE) imms ==>
  immutables_ready bare_globals toplevel_vtypes
    (initial_evaluation_context sources layouts tx src) imms
Proof
  rw[immutables_ready_def, get_tenv_def, get_module_code_def,
     initial_evaluation_context_def] >> metis_tac[]
QED

