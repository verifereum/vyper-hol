(*
 * Initial-context consistency for checked contracts.
 *
 * This theory turns the static maps produced by check_contract into the
 * env/context consistency facts and transfer helpers needed by checked function
 * body soundness.
 *)

Theory vyperTypeContractContext
Ancestors
  list rich_list arithmetic finite_map alist option pair patricia_casts
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues vyperTypeBindArguments
  vyperTypeStmtSoundness vyperTypeInitialState vyperPureExpr vyperEvalPreservesScopes vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom vyperScopePreservation vyperStatePreservation
  vyperTypeContractStaticMaps
Libs
  wordsLib

val _ = Parse.hide "body";

(* ===== Env-context bridge for initial contexts ===== *)

Theorem check_contract_env_context_consistent_initial_NONE:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  env_context_consistent (artifact_env art mods NONE)
    (initial_evaluation_context sources layouts tx NONE)
Proof
  rw[env_context_consistent_def, artifact_env_def]
  >- simp[get_tenv_def, initial_evaluation_context_def]
  >- simp[current_module_def, initial_evaluation_context_def]
  >- (irule check_contract_fn_sigs_consistent_initial >> simp[])
  >- (irule check_contract_fn_sigs_complete_initial >> simp[])
  >- (irule check_contract_toplevel_vtypes_complete_initial >> simp[])
  >- (irule check_contract_bare_globals_complete_initial >> simp[])
  >- (irule check_contract_bare_global_assignable_complete_initial >> simp[])
  >- (irule check_contract_flag_members_complete_initial >> simp[])
  >- (dxrule check_contract_bare_globals_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`,`src`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_bare_global_assignable_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`,`src`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, lookup_var_slot_from_layout_def,
           get_tenv_def, initial_evaluation_context_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, lookup_var_slot_from_layout_def,
           get_tenv_def, initial_evaluation_context_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, lookup_var_slot_from_layout_def,
           get_tenv_def, initial_evaluation_context_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_flag_members_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src`,`fid`,`ls`] mp_tac) >>
      simp[get_module_code_def, get_tenv_def, initial_evaluation_context_def])
QED

Theorem get_tenv_stk[local]:
  !cx stk. get_tenv (cx with stk := stk) = get_tenv cx
Proof
  simp[get_tenv_def]
QED

Theorem get_module_code_stk[local]:
  !cx stk src. get_module_code (cx with stk := stk) src = get_module_code cx src
Proof
  simp[get_module_code_def]
QED

Theorem lookup_var_slot_from_layout_stk[local]:
  !cx stk is_transient src id.
    lookup_var_slot_from_layout (cx with stk := stk) is_transient src id =
    lookup_var_slot_from_layout cx is_transient src id
Proof
  simp[lookup_var_slot_from_layout_def]
QED

Theorem fn_sigs_consistent_stk[local]:
  !sigs cx stk.
    fn_sigs_consistent sigs (cx with stk := stk) <=> fn_sigs_consistent sigs cx
Proof
  simp[fn_sigs_consistent_def, get_module_code_stk]
QED

Theorem fn_sigs_complete_stk[local]:
  !sigs cx stk.
    fn_sigs_complete sigs (cx with stk := stk) <=> fn_sigs_complete sigs cx
Proof
  simp[fn_sigs_complete_def, get_module_code_stk]
QED

Theorem toplevel_vtypes_complete_stk[local]:
  !m cx stk.
    toplevel_vtypes_complete m (cx with stk := stk) <=>
    toplevel_vtypes_complete m cx
Proof
  simp[toplevel_vtypes_complete_def, get_module_code_stk]
QED

Theorem bare_globals_complete_stk[local]:
  !m cx stk.
    bare_globals_complete m (cx with stk := stk) <=> bare_globals_complete m cx
Proof
  simp[bare_globals_complete_def, get_module_code_stk]
QED

Theorem bare_global_assignable_complete_stk[local]:
  !m cx stk.
    bare_global_assignable_complete m (cx with stk := stk) <=>
    bare_global_assignable_complete m cx
Proof
  simp[bare_global_assignable_complete_def, get_module_code_stk]
QED

Theorem flag_members_complete_stk[local]:
  !m cx stk.
    flag_members_complete m (cx with stk := stk) <=> flag_members_complete m cx
Proof
  simp[flag_members_complete_def, get_module_code_stk]
QED

Theorem check_contract_env_context_consistent_initial_src:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  env_context_consistent (artifact_env art mods src)
    (initial_evaluation_context sources layouts tx src)
Proof
  rw[env_context_consistent_def, artifact_env_def]
  >- simp[get_tenv_def, initial_evaluation_context_def]
  >- simp[current_module_def, initial_evaluation_context_def]
  >- (irule check_contract_fn_sigs_consistent_initial >> simp[])
  >- (irule check_contract_fn_sigs_complete_initial >> simp[])
  >- (irule check_contract_toplevel_vtypes_complete_initial >> simp[])
  >- (irule check_contract_bare_globals_complete_initial >> simp[])
  >- (irule check_contract_bare_global_assignable_complete_initial >> simp[])
  >- (irule check_contract_flag_members_complete_initial >> simp[])
  >- (dxrule check_contract_bare_globals_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_bare_global_assignable_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_def, get_tenv_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_tenv_def, initial_evaluation_context_def,
           get_module_code_def, lookup_var_slot_from_layout_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_flag_members_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`fid`,`ls`] mp_tac) >>
      simp[get_tenv_def, initial_evaluation_context_def, get_module_code_def])
QED

Theorem check_contract_env_context_consistent_initial_with_current_src:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  env_context_consistent (artifact_env art mods src)
    ((initial_evaluation_context sources layouts tx src) with stk := [(src, fn)])
Proof
  rw[env_context_consistent_def, artifact_env_def]
  >- simp[get_tenv_stk, get_tenv_def, initial_evaluation_context_def]
  >- simp[current_module_def]
  >- (simp[fn_sigs_consistent_stk] >>
      irule check_contract_fn_sigs_consistent_initial >> simp[])
  >- (simp[fn_sigs_complete_stk] >>
      irule check_contract_fn_sigs_complete_initial >> simp[])
  >- (simp[toplevel_vtypes_complete_stk] >>
      irule check_contract_toplevel_vtypes_complete_initial >> simp[])
  >- (simp[bare_globals_complete_stk] >>
      irule check_contract_bare_globals_complete_initial >> simp[])
  >- (simp[bare_global_assignable_complete_stk] >>
      irule check_contract_bare_global_assignable_complete_initial >> simp[])
  >- (simp[flag_members_complete_stk] >>
      irule check_contract_flag_members_complete_initial >> simp[])
  >- (dxrule check_contract_bare_globals_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_stk, get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_bare_global_assignable_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_stk, get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_stk, get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_stk, lookup_var_slot_from_layout_def,
           get_tenv_stk, get_tenv_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_tenv_stk, get_tenv_def, initial_evaluation_context_def,
           get_module_code_stk, get_module_code_def,
           lookup_var_slot_from_layout_stk, lookup_var_slot_from_layout_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_stk, get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_stk, lookup_var_slot_from_layout_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_flag_members_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`fid`,`ls`] mp_tac) >>
      simp[get_tenv_stk, get_tenv_def, initial_evaluation_context_def,
           get_module_code_stk, get_module_code_def])
QED

(* ===== Static-map transfer helpers ===== *)

Theorem check_contract_toplevel_body_MEM[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM tl ts ==>
  check_toplevel_body layouts addr mods art src tl
Proof
  rw[check_contract_def] >> gvs[] >>
  `MEM (src,ts) mods` by metis_tac[ALOOKUP_MEM] >>
  `check_module layouts addr mods (build_contract_type_artifact F mods) (src,ts)` by
    metis_tac[EVERY_MEM] >>
  pop_assum mp_tac >>
  simp[check_module_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem check_contract_function_body_MEM:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts ==>
  check_function_body layouts addr mods art src mut nr args dflts ret body
Proof
  rw[] >>
  drule_all check_contract_toplevel_body_MEM >>
  simp[check_toplevel_body_def]
QED

Theorem FOLDL_extend_local_args_not_mem[local]:
  !args (base : typing_env) n.
    ~MEM n (MAP (string_to_num o FST) args) ==>
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_types n =
      FLOOKUP base.var_types n /\
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_assignable n =
      FLOOKUP base.var_assignable n
Proof
  Induct >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[extend_local_def] >>
  qpat_x_assum `!base n. _` (qspecl_then [`extend_local base' (string_to_num h0) h1 T`,`n`] mp_tac) >>
  simp[extend_local_def, FLOOKUP_UPDATE]
QED

Theorem FOLDL_extend_local_args_formal_lookup:
  !args (base : typing_env) id typ.
    ALL_DISTINCT (MAP (string_to_num o FST) args) /\
    MEM (id,typ) args ==>
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_types
      (string_to_num id) = SOME typ /\
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_assignable
      (string_to_num id) = SOME T
Proof
  Induct >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[extend_local_def, FLOOKUP_UPDATE] >-
    (qspecl_then [`args`,`extend_local base' (string_to_num h0) h1 T`,`string_to_num h0`]
       mp_tac FOLDL_extend_local_args_not_mem >>
     simp[extend_local_def, FLOOKUP_UPDATE] >>
     strip_tac >> gvs[]) >-
    (qspecl_then [`args`,`extend_local base' (string_to_num h0) h1 T`,`string_to_num h0`]
       mp_tac FOLDL_extend_local_args_not_mem >>
     simp[extend_local_def, FLOOKUP_UPDATE] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `!base id typ. _`
    (qspecl_then [`extend_local base' (string_to_num h0) h1 T`,`id`,`typ`] mp_tac) >>
  simp[extend_local_def]
QED

Theorem FOLDL_extend_local_args_var_types_range:
  !args (base : typing_env) n ty.
    ALL_DISTINCT (MAP (string_to_num o FST) args) /\
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_types n = SOME ty ==>
    FLOOKUP base.var_types n = SOME ty \/
    ?id. MEM (id,ty) args /\ n = string_to_num id
Proof
  Induct >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[extend_local_def] >>
  last_x_assum drule >>
  simp[extend_local_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  Cases_on `string_to_num h0 = n` >> gvs[] >>
  metis_tac[]
QED

Theorem FOLDL_extend_local_args_var_assignable_range:
  !args (base : typing_env) n b.
    ALL_DISTINCT (MAP (string_to_num o FST) args) /\
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_assignable n = SOME b ==>
    FLOOKUP base.var_assignable n = SOME b \/
    ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T
Proof
  Induct >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[extend_local_def] >>
  last_x_assum drule >>
  simp[extend_local_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  Cases_on `string_to_num h0 = n` >> gvs[] >>
  metis_tac[]
QED

Theorem FOLDL_extend_local_args_lookup[local]:
  !args (base : typing_env) env.
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  env = FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args /\
  base.var_types = FEMPTY /\ base.var_assignable = FEMPTY ==>
  (!id typ. MEM (id,typ) args ==>
     FLOOKUP env.var_types (string_to_num id) = SOME typ /\
     FLOOKUP env.var_assignable (string_to_num id) = SOME T) /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==>
     ?id. MEM (id,ty) args /\ n = string_to_num id) /\
  (!n b. FLOOKUP env.var_assignable n = SOME b ==>
     ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T)
Proof
  rw[] >-
    (drule_all FOLDL_extend_local_args_formal_lookup >> simp[])
  >- (drule_all FOLDL_extend_local_args_formal_lookup >> simp[])
  >- (drule_all FOLDL_extend_local_args_var_types_range >> rw[] >> gvs[])
  >- (drule_all FOLDL_extend_local_args_var_assignable_range >> rw[] >> gvs[])
QED

Theorem FOLDL_extend_local_args_static:
  !args (base : typing_env).
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).current_src = base.current_src /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).bare_globals = base.bare_globals /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).bare_global_assignable = base.bare_global_assignable /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).toplevel_vtypes = base.toplevel_vtypes /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).type_defs = base.type_defs /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).fn_sigs = base.fn_sigs /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).flag_members = base.flag_members
Proof
  Induct >> simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[extend_local_def]
QED

Theorem artifact_fn_sigs_lookup_transfer_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).fn_sigs k = SOME sig ==>
  FLOOKUP fn_sigs k = SOME sig
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_fn_sigs_sound >> rw[] >>
  Cases_on `sig` >>
  gvs[fn_sigs_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  first_x_assum drule >> disch_then drule >> simp[fn_sig_component_equality]
QED

Theorem artifact_bare_globals_lookup_transfer_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).bare_globals k = SOME ty ==>
  FLOOKUP bare_globals k = SOME ty
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_bare_globals_sound >> rw[] >>
  gvs[bare_globals_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem artifact_bare_global_assignable_lookup_transfer_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).bare_global_assignable k = SOME ty ==>
  FLOOKUP bare_global_assignable k = SOME ty
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_bare_global_assignable_sound >> rw[] >>
  gvs[bare_global_assignable_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem artifact_toplevel_vtypes_lookup_transfer_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).toplevel_vtypes k = SOME vt ==>
  FLOOKUP toplevel_vtypes k = SOME vt
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_toplevel_vtypes_sound >> rw[] >>
  gvs[toplevel_vtypes_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem artifact_flag_members_lookup_transfer_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).flag_members k = SOME members ==>
  FLOOKUP flag_members k = SOME members
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_flag_members_sound >> rw[] >>
  gvs[flag_members_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[lookup_flag_MEM_FlagDecl, contract_namespaces_ok_module_flag_member_keys, ALOOKUP_MEM]
QED

Theorem artifact_toplevel_non_bare_globals_NONE_transfer_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\ tx.target = addr /\
  (!src' id ty. FLOOKUP bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx cx_src) src' = SOME ts /\
          FLOOKUP toplevel_vtypes (src',id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) /\
  FLOOKUP (function_entry_env art mods entry_src args).toplevel_vtypes (src,id) = SOME vt /\
  FLOOKUP (function_entry_env art mods entry_src args).bare_globals (src,id) = NONE ==>
  FLOOKUP bare_globals (src,id) = NONE
Proof
  rw[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static] >>
  Cases_on `FLOOKUP bare_globals (src,id)` >> simp[] >>
  rename1 `FLOOKUP bare_globals (src,id) = SOME bare_ty` >>
  first_x_assum drule >>
  simp[get_module_code_def, initial_evaluation_context_def] >>
  strip_tac >> gvs[] >>
  gvs[check_contract_def] >>
  drule_all build_contract_type_artifact_toplevel_vtypes_sound >>
  strip_tac >> gvs[] >-
   (Cases_on `mut` >> gvs[] >-
     (rw[] >>
      `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals
         (src,string_to_num id_str) = SOME ty` by
        (irule build_contract_type_artifact_bare_globals_complete >> simp[] >> metis_tac[]) >>
      gvs[]) >-
     (rw[] >>
      `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals
         (src,string_to_num id_str) = SOME ty` by
        (irule build_contract_type_artifact_bare_globals_complete >> simp[] >> metis_tac[]) >>
      gvs[]) >-
     (rw[] >>
      `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
      `find_var_decl_by_num (string_to_num id_str) ts =
         SOME (StorageVarDecl T ty,id_str)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient] >>
      gvs[]) >>
     rw[] >>
     `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
     `find_var_decl_by_num (string_to_num id_str) ts =
        SOME (StorageVarDecl F ty,id_str)` by
       metis_tac[find_var_decl_by_num_SOME_storage_var_Storage] >>
     gvs[]) >>
  rw[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
     metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
  `find_var_decl_by_num (string_to_num id_str) ts =
     SOME (HashMapVarDecl is_transient kt vty,id_str)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  gvs[]
QED
Theorem well_typed_static_maps_transfer:
  (!env1 e. well_typed_expr env1 e ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    well_typed_expr env2 e) /\
  (!env1 e vt. type_place_expr env1 e = SOME vt ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    type_place_expr env2 e = SOME vt) /\
  (!env1 tgt vt. type_place_target env1 tgt = SOME vt ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    type_place_target env2 tgt = SOME vt) /\
  (!env1 es. well_typed_exprs env1 es ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    well_typed_exprs env2 es) /\
  (!env1 opt. well_typed_opt env1 opt ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    well_typed_opt env2 opt) /\
  (!env1 kes. well_typed_named_exprs env1 kes ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    well_typed_named_exprs env2 kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >>
  rw[well_typed_expr_def, AllCaseEqs()] >>
  gvs[] >>
  metis_tac[]
QED
