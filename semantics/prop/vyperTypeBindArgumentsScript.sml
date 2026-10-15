(*
 * Bind-argument setup lemmas for Vyper type soundness.
 *
 * This theory factors call-argument binding infrastructure out of the large
 * statement-soundness development so it can be built/debugged independently.
 *)

Theory vyperTypeBindArguments
Ancestors
  list rich_list arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeValues vyperTypeEnv
  vyperTypeExprSoundness
Libs
  wordsLib intLib

Theorem bind_arguments_scope_lookup:
  !tenv params vs sc n entry.
    bind_arguments tenv params vs = SOME sc /\
    FLOOKUP sc n = SOME entry ==>
    ?id typ. n = string_to_num id /\ MEM (id,typ) params /\
             evaluate_type tenv typ = SOME entry.type /\ entry.assignable
Proof
  Induct_on `params` >> simp[Once bind_arguments_def] >>
  Cases >> simp[Once bind_arguments_def] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE] >>
  Cases_on `n = string_to_num q` >> gvs[]
  >- (qexists_tac `q` >> qexists_tac `r` >> simp[]) >>
  first_x_assum drule_all >> rw[] >>
  qexists_tac `id` >> qexists_tac `typ` >> simp[]
QED

Theorem bind_arguments_scope_covers_params:
  !tenv params vs sc id typ.
    bind_arguments tenv params vs = SOME sc /\ MEM (id,typ) params /\
    (!id' typ'. MEM (id',typ') params /\ string_to_num id' = string_to_num id ==> typ' = typ) ==>
    ?entry. FLOOKUP sc (string_to_num id) = SOME entry /\
            evaluate_type tenv typ = SOME entry.type /\ entry.assignable
Proof
  Induct_on `params` >> simp[Once bind_arguments_def] >>
  Cases >> simp[Once bind_arguments_def] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac
  >- (qexists_tac `<|assignable := T; type := tv; value := v'|>` >>
      qpat_x_assum `id = q` SUBST_ALL_TAC >>
      qpat_x_assum `typ = r` SUBST_ALL_TAC >>
      rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  Cases_on `string_to_num q = string_to_num id`
  >- (qexists_tac `<|assignable := T; type := tv; value := v'|>` >>
      `r = typ` by metis_tac[] >>
      qpat_x_assum `r = typ` SUBST_ALL_TAC >>
      asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  first_x_assum (qspecl_then [`tenv`, `t`, `m`, `id`, `typ`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!id'' typ''. _` (qspecl_then [`id'`, `typ'`] mp_tac) >>
      simp[]) >>
  strip_tac >>
  qexists_tac `entry` >> asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]
QED

Theorem param_var_types_key_agree:
  !vt args id typ id' typ'.
    (!x ty. MEM (x,ty) args ==> FLOOKUP vt (string_to_num x) = SOME ty) /\
    MEM (id,typ) args /\ MEM (id',typ') args /\
    string_to_num id' = string_to_num id ==>
    typ' = typ
Proof
  rpt strip_tac >>
  `FLOOKUP vt (string_to_num id) = SOME typ` by metis_tac[] >>
  `FLOOKUP vt (string_to_num id) = SOME typ'` by metis_tac[] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem bind_arguments_env_var_type_scope_entry:
  !tenv args vs sc env_body n ty.
    bind_arguments tenv args vs = SOME sc /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    FLOOKUP env_body.var_types n = SOME ty ==>
    ?entry. FLOOKUP sc n = SOME entry /\
            evaluate_type tenv ty = SOME entry.type /\ entry.assignable
Proof
  rpt strip_tac >>
  qpat_x_assum `!n ty. FLOOKUP env_body.var_types n = SOME ty ==> _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  rename1 `MEM (pid,ty) args` >>
  qspecl_then [`tenv`, `args`, `vs`, `sc`, `pid`, `ty`] mp_tac
    bind_arguments_scope_covers_params >>
  simp[] >>
  impl_tac
  >- (rpt strip_tac >>
      irule param_var_types_key_agree >>
      qexists_tac `args` >>
      qexists_tac `pid` >>
      qexists_tac `id'` >>
      qexists_tac `env_body.var_types` >>
      simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!id typ. MEM (id,typ) args ==> _`
        (qspecl_then [`x`, `ty'`] mp_tac) >>
      simp[]) >>
  strip_tac >> gvs[]
QED

Theorem bind_arguments_scope_entry_env_var_type:
  !tenv args vs sc env_body n entry.
    bind_arguments tenv args vs = SOME sc /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    FLOOKUP sc n = SOME entry ==>
    ?ty. FLOOKUP env_body.var_types n = SOME ty /\
         evaluate_type tenv ty = SOME entry.type /\ entry.assignable
Proof
  rpt strip_tac >>
  qspecl_then [`tenv`, `args`, `vs`, `sc`, `n`, `entry`] mp_tac
    bind_arguments_scope_lookup >>
  simp[] >>
  strip_tac >> gvs[] >>
  rename1 `MEM (pid,typ) args` >>
  qpat_x_assum `!id typ. MEM (id,typ) args ==> _`
    (qspecl_then [`pid`, `typ`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `typ` >> simp[]
QED

Theorem bind_arguments_env_var_assignable_scope_entry:
  !tenv args vs sc env_body n.
    bind_arguments tenv args vs = SOME sc /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
    FLOOKUP env_body.var_assignable n = SOME T ==>
    ?entry. FLOOKUP sc n = SOME entry /\ entry.assignable
Proof
  rpt strip_tac >>
  qpat_x_assum `!n b. FLOOKUP env_body.var_assignable n = SOME b ==> _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  rename1 `MEM (pid,typ) args` >>
  qpat_assum `!id typ. MEM (id,typ) args ==> _`
    (drule_then strip_assume_tac) >>
  qspecl_then [`tenv`, `args`, `vs`, `sc`, `pid`, `typ`] mp_tac
    bind_arguments_scope_covers_params >>
  simp[] >>
  impl_tac
  >- (rpt strip_tac >>
      irule param_var_types_key_agree >>
      qexists_tac `args` >>
      qexists_tac `pid` >>
      qexists_tac `id'` >>
      qexists_tac `env_body.var_types` >>
      simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!id typ. MEM (id,typ) args ==> _`
        (qspecl_then [`x`, `ty'`] mp_tac) >>
      simp[]) >>
  strip_tac >>
  qexists_tac `entry` >> simp[]
QED

Theorem bind_arguments_env_scopes_consistent:
  !tenv args vs sc env_body cx.
    bind_arguments tenv args vs = SOME sc /\ tenv = get_tenv cx /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) ==>
    env_scopes_consistent env_body cx (st with scopes := [sc])
Proof
  rw[env_scopes_consistent_def, lookup_scopes_def]
  >- (drule_all bind_arguments_env_var_type_scope_entry >>
      strip_tac >> simp[IS_SOME_EXISTS])
  >- (Cases_on `FLOOKUP sc id` >> gvs[] >>
      drule_all bind_arguments_scope_entry_env_var_type >>
      strip_tac >> simp[IS_SOME_EXISTS])
  >- (Cases_on `FLOOKUP sc id` >> gvs[] >>
      drule_all bind_arguments_scope_entry_env_var_type >>
      strip_tac >> gvs[])
  >- (qpat_x_assum `!n b. FLOOKUP env_body.var_assignable n = SOME b ==> _`
        (drule_then strip_assume_tac) >>
      gvs[] >>
      qpat_assum `!id typ. MEM (id,typ) args ==> _`
        (drule_then strip_assume_tac) >>
      simp[IS_SOME_EXISTS]) >>
  qspecl_then [`get_tenv cx`, `args`, `vs`, `sc`, `env_body`, `id`] mp_tac
    bind_arguments_env_var_assignable_scope_entry >>
  simp[] >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_assum `!id typ. MEM (id,typ) args ==> _`
        (qspecl_then [`id'`, `typ`] mp_tac) >>
      simp[]) >>
  strip_tac >>
  qexists_tac `entry` >> gvs[]
QED

Theorem bind_arguments_scope_well_typed_stmt:
  !tenv params vs sc.
    bind_arguments tenv params vs = SOME sc /\
    (!i tv. i < LENGTH params /\ i < LENGTH vs /\
            evaluate_type tenv (SND (EL i params)) = SOME tv ==>
            value_has_type tv (EL i vs)) ==>
    scope_well_typed sc
Proof
  MAP_EVERY qid_spec_tac [`sc`, `vs`, `params`, `tenv`] >>
  Induct_on `params`
  >- (rpt gen_tac >> Cases_on `vs` >>
      simp[Once bind_arguments_def, scope_well_typed_def, FLOOKUP_DEF]) >>
  simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `safe_cast tv0 hval = SOME v0` >>
  rename1 `evaluate_type tenv _ = SOME tv0` >>
  `value_has_type tv0 hval` by
    (first_x_assum (qspecl_then [`0`, `tv0`] mp_tac) >> simp[]) >>
  imp_res_tac safe_cast_preserves_well_typed >>
  `well_formed_type_value tv0` by metis_tac[evaluate_type_well_formed] >>
  rename1 `bind_arguments tenv params tl = SOME sc0` >>
  `scope_well_typed sc0` by (
    first_x_assum (qspecl_then [`tenv`, `tl`, `sc0`] mp_tac) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`SUC i`, `tv`] mp_tac) >> simp[]) >>
  gvs[scope_well_typed_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >> res_tac
QED

(* TOP-LEVEL: once safe_cast is a typed boundary, successful binding of raw
   call arguments establishes the ordinary scope invariant directly. *)
Theorem bind_arguments_scope_well_typed_from_success:
  !tenv params vs sc.
    bind_arguments tenv params vs = SOME sc ==> scope_well_typed sc
Proof
  MAP_EVERY qid_spec_tac [`sc`, `vs`, `params`, `tenv`] >>
  Induct_on `params`
  >- (rpt gen_tac >> Cases_on `vs` >>
      simp[Once bind_arguments_def, scope_well_typed_def, FLOOKUP_DEF]) >>
  simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `safe_cast tv0 hval = SOME v0` >>
  `value_has_type tv0 v0` by metis_tac[safe_cast_result_well_typed] >>
  `well_formed_type_value tv0` by metis_tac[evaluate_type_well_formed] >>
  rename1 `bind_arguments tenv params tl = SOME sc0` >>
  `scope_well_typed sc0` by metis_tac[] >>
  gvs[scope_well_typed_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >> res_tac
QED

Theorem bind_arguments_state_scopes_well_typed:
  !tenv params vals scope st.
    bind_arguments tenv params vals = SOME scope /\
    state_well_typed st ==>
    state_well_typed (st with scopes := [scope])
Proof
  rw[state_well_typed_def] >>
  irule bind_arguments_scope_well_typed_from_success >>
  goal_assum drule
QED

Theorem exprs_runtime_typed_value_expr_LIST_REL:
  !env es vs.
    exprs_runtime_typed env es vs ==>
    LIST_REL (\v e. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
                         value_has_type tv v) vs es
Proof
  rw[exprs_runtime_typed_def, listTheory.LIST_REL_EL_EQN] >>
  gvs[]
QED

Theorem args_dflts_typing_to_el_stmt:
  !tenv (params: (string # type) list) args vs dflt_vs needed_dflts.
    LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                         value_has_type tv v) vs args /\
    LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                         value_has_type tv v) dflt_vs needed_dflts /\
    MAP expr_type args = TAKE (LENGTH args) (MAP SND params) /\
    MAP expr_type needed_dflts = MAP SND (DROP (LENGTH args) params) /\
    LENGTH args + LENGTH needed_dflts = LENGTH params ==>
    !i tv. i < LENGTH params /\ i < LENGTH (vs ++ dflt_vs) /\
           evaluate_type tenv (SND (EL i params)) = SOME tv ==>
           value_has_type tv (EL i (vs ++ dflt_vs))
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `LENGTH vs = LENGTH args` by
    (qpat_x_assum `LIST_REL _ vs args` mp_tac >>
     simp[listTheory.LIST_REL_EL_EQN]) >>
  `LENGTH dflt_vs = LENGTH needed_dflts` by
    (qpat_x_assum `LIST_REL _ dflt_vs needed_dflts` mp_tac >>
     simp[listTheory.LIST_REL_EL_EQN]) >>
  Cases_on `i < LENGTH args`
  >- (simp[rich_listTheory.EL_APPEND1] >>
      qpat_x_assum `LIST_REL _ vs args` mp_tac >>
      simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      `expr_type (EL i args) = SND (EL i params)` by (
        `EL i (MAP expr_type args) =
         EL i (TAKE (LENGTH args) (MAP SND params))` by metis_tac[] >>
        gvs[listTheory.EL_MAP, rich_listTheory.EL_TAKE]) >>
      gvs[]) >>
  `i >= LENGTH vs` by simp[] >>
  `i - LENGTH vs < LENGTH dflt_vs` by decide_tac >>
  simp[rich_listTheory.EL_APPEND2] >>
  qpat_x_assum `LIST_REL _ dflt_vs needed_dflts` mp_tac >>
  simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >> gvs[] >>
  `expr_type (EL (i - LENGTH vs) needed_dflts) = SND (EL i params)` by (
    `EL (i - LENGTH args) (MAP expr_type needed_dflts) =
     EL (i - LENGTH args) (MAP SND (DROP (LENGTH args) params))` by
      metis_tac[] >>
    gvs[listTheory.EL_MAP, listTheory.EL_DROP]) >>
  first_x_assum (qspec_then `i - LENGTH args` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[]
QED

Theorem bind_arguments_succeeds_stmt:
  !tenv params vs.
    LENGTH params = LENGTH vs /\
    (!i. i < LENGTH params ==>
      ?tv. evaluate_type tenv (SND (EL i params)) = SOME tv /\
           value_has_type tv (EL i vs)) ==>
    ?sc. bind_arguments tenv params vs = SOME sc
Proof
  Induct_on `params`
  >- (rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def]) >>
  simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  strip_tac >>
  `?tv. evaluate_type tenv p_2 = SOME tv /\ value_has_type tv h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  imp_res_tac safe_cast_well_typed >> simp[] >>
  first_assum irule >> simp[] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem args_dflts_bind_arguments_stmt:
  !tenv (params: (string # type) list) args vs dflt_vs needed_dflts.
    LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                         value_has_type tv v) vs args /\
    LIST_REL (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                         value_has_type tv v) dflt_vs needed_dflts /\
    MAP expr_type args = TAKE (LENGTH args) (MAP SND params) /\
    MAP expr_type needed_dflts = MAP SND (DROP (LENGTH args) params) /\
    LENGTH args + LENGTH needed_dflts = LENGTH params ==>
    ?sc. bind_arguments tenv params (vs ++ dflt_vs) = SOME sc
Proof
  rpt strip_tac >>
  imp_res_tac LIST_REL_LENGTH >>
  irule bind_arguments_succeeds_stmt >>
  reverse conj_tac >- simp[LENGTH_APPEND] >>
  gen_tac >> strip_tac >>
  Cases_on `i < LENGTH args`
  >- (qpat_x_assum `LIST_REL _ vs args` mp_tac >>
      simp[listTheory.LIST_REL_EL_EQN] >> disch_then drule >> strip_tac >>
      `EL i (MAP expr_type args) = EL i (MAP SND params)` by
        simp[rich_listTheory.EL_TAKE] >>
      qexists_tac `tv` >>
      gvs[listTheory.EL_MAP, rich_listTheory.EL_APPEND1]) >>
  `i - LENGTH args < LENGTH needed_dflts` by decide_tac >>
  qpat_x_assum `LIST_REL _ dflt_vs needed_dflts` mp_tac >>
  simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `EL (i - LENGTH args) (MAP expr_type needed_dflts) =
   EL (i - LENGTH args) (MAP SND (DROP (LENGTH args) params))` by simp[] >>
  qexists_tac `tv` >>
  gvs[listTheory.EL_MAP, listTheory.EL_DROP, rich_listTheory.EL_APPEND2]
QED

Theorem intcall_defaults_map_param_types_length_le:
  !(params: (string # type) list) (dflts: expr list).
    MAP expr_type dflts = MAP SND (DROP (LENGTH params - LENGTH dflts) params) ==>
    LENGTH dflts <= LENGTH params
Proof
  rpt strip_tac >>
  `LENGTH (MAP expr_type dflts) =
   LENGTH (MAP SND (DROP (LENGTH params - LENGTH dflts) params))` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP, listTheory.LENGTH_DROP] >>
  decide_tac
QED

Theorem intcall_needed_defaults_param_types:
  !(params: (string # type) list) (dflts: expr list) (es: expr list) (needed_dflts: expr list).
    needed_dflts = DROP (LENGTH dflts - (LENGTH params - LENGTH es)) dflts /\
    LENGTH es <= LENGTH params /\ LENGTH params - LENGTH es <= LENGTH dflts /\
    LENGTH dflts <= LENGTH params /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH params - LENGTH dflts) params) ==>
    MAP expr_type needed_dflts = MAP SND (DROP (LENGTH es) params)
Proof
  rpt strip_tac >> gvs[listTheory.MAP_DROP] >>
  rewrite_tac[rich_listTheory.DROP_DROP_T] >>
  `LENGTH params - LENGTH dflts + (LENGTH dflts - (LENGTH params - LENGTH es)) = LENGTH es` by
    decide_tac >>
  simp[]
QED

Theorem intcall_needed_defaults_length:
  !(params: (string # type) list) (dflts: expr list) (es: expr list) (needed_dflts: expr list).
    needed_dflts = DROP (LENGTH dflts - (LENGTH params - LENGTH es)) dflts /\
    LENGTH es <= LENGTH params /\ LENGTH params - LENGTH es <= LENGTH dflts ==>
    LENGTH es + LENGTH needed_dflts = LENGTH params
Proof
  rw[listTheory.LENGTH_DROP] >> decide_tac
QED

Theorem intcall_bind_arguments_from_runtime_typed:
  !cx env env_body params dflts es actual_vs dflt_vs needed_dflts st.
    exprs_runtime_typed env es actual_vs /\
    exprs_runtime_typed (defaults_env env_body) needed_dflts dflt_vs /\
    env.type_defs = get_tenv cx /\ env_body.type_defs = get_tenv cx /\
    MAP expr_type es = TAKE (LENGTH es) (MAP SND params) /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH params - LENGTH dflts) params) /\
    needed_dflts = DROP (LENGTH dflts - (LENGTH params - LENGTH es)) dflts /\
    LENGTH es <= LENGTH params /\ LENGTH params - LENGTH es <= LENGTH dflts /\
    (!id typ. MEM (id,typ) params ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) params /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) params /\ n = string_to_num id /\ b = T) ==>
    ?call_env.
      bind_arguments (get_tenv cx) params (actual_vs ++ dflt_vs) = SOME call_env /\
      scope_well_typed call_env /\
      env_scopes_consistent env_body cx (st with scopes := [call_env])
Proof
  rpt strip_tac >>
  `LENGTH dflts <= LENGTH params` by
    metis_tac[intcall_defaults_map_param_types_length_le] >>
  mp_tac (Q.SPECL [`params : (string # type) list`, `dflts : expr list`,
                     `es : expr list`, `needed_dflts : expr list`]
            intcall_needed_defaults_param_types) >>
  (impl_tac >- simp[]) >> strip_tac >>
  mp_tac (Q.SPECL [`params : (string # type) list`, `dflts : expr list`,
                     `es : expr list`, `needed_dflts : expr list`]
            intcall_needed_defaults_length) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LIST_REL (\v e. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
                       value_has_type tv v) actual_vs es` by
    metis_tac[exprs_runtime_typed_value_expr_LIST_REL] >>
  `LIST_REL (\v e. ?tv. evaluate_type (defaults_env env_body).type_defs (expr_type e) = SOME tv /\
                       value_has_type tv v) dflt_vs needed_dflts` by
    metis_tac[exprs_runtime_typed_value_expr_LIST_REL] >>
  `LIST_REL (\v e. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                       value_has_type tv v) actual_vs es` by
    metis_tac[] >>
  `LIST_REL (\v e. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                       value_has_type tv v) dflt_vs needed_dflts` by (
    qpat_x_assum `LIST_REL _ dflt_vs needed_dflts` mp_tac >>
    simp[defaults_env_def]) >>
  mp_tac (Q.SPECL [`get_tenv cx`, `params : (string # type) list`,
                     `es : expr list`, `actual_vs`, `dflt_vs`,
                     `needed_dflts : expr list`]
            args_dflts_bind_arguments_stmt) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `sc` >> simp[] >>
  conj_tac
  >- (mp_tac (Q.SPECL [`get_tenv cx`, `params`, `actual_vs ++ dflt_vs`, `sc`]
                bind_arguments_scope_well_typed_stmt) >>
      simp[] >> disch_then irule >>
      mp_tac (Q.SPECL [`get_tenv cx`, `params`, `es`, `actual_vs`, `dflt_vs`, `needed_dflts`]
                args_dflts_typing_to_el_stmt) >>
      (impl_tac >- simp[]) >> simp[]) >>
  mp_tac (Q.SPECL [`get_tenv cx`, `params`, `actual_vs ++ dflt_vs`,
                     `sc`, `env_body`, `cx`]
            bind_arguments_env_scopes_consistent) >>
  disch_then irule >> metis_tac[]
QED


