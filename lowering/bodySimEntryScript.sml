(*
 * The body simulation of S1: ce_locals_declared at a body's entry (#637)
 *
 * build_compile_env binds the parameters, and the prologues rebind
 * parameters only, so a body's compile env binds only parameters at its
 * entry.  With a type environment that has the parameters,
 * ce_locals_declared (bodySim) holds there.
 *
 * TOP-LEVEL:
 *   ce_locals_declared_params    — ce_locals_declared from the bound names
 *   external_entry_declared, constructor_entry_declared,
 *   fallback_entry_declared, internal_entry_declared
 *                                — each entry's compile env binds the
 *                                  parameters only
 *   build_compile_env_bare_globals
 *                                — expr_sim_inv's immutable clause
 *                                  for build_compile_env
 *)

Theory bodySimEntry
Ancestors
  loweringStateRelDefs list finite_map bodySim compileEnv compileVyper moduleLowering
  intCallCallee supportedDecls supportedProgram vyperTypeInvariants
  immutableLocationProps immutableSectionRel immutableRelation option pair
  bodyStorageMetadata structFieldsProps bodyInvSplit bodyInvCodeProps
  bodySimModsProps compileUnit vyperTypeContract vyperTypeContractStaticMaps alist
Libs
  monadsyntax

Theorem build_compile_env_module_pins:
  !tops vis mut fname args ret fbody use_trans.
    cenv_module_pins tops
      (build_compile_env tops vis mut fname args ret fbody use_trans)
Proof
  rpt gen_tac >> simp[cenv_module_pins_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* Rebuilding an internal callee's environment uses the same checked
   module metadata as its caller. *)
Theorem body_inv_build_internal_env_mods:
  contract_inv mods exps ctx caller cx /\ ALOOKUP mods src = SOME tops /\
  cenv = (build_compile_env_unit mods src Internal mut fname args ret stmts use_trans)
    with <| ce_target := caller.ce_target; ce_is_ctor := caller.ce_is_ctor |> ==>
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx
Proof
  strip_tac >>
  qpat_x_assum `(cenv:compile_env) = _` SUBST_ALL_TAC >>
  `caller.ce_module_vars =
    add_immutable_locations_unit
      (get_struct_fields (make_struct_fields_map_mods mods)) mods
      (add_module_var_locations_mods mods FEMPTY)` by
    (qpat_assum `contract_inv mods exps ctx caller cx`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [contract_inv_def]) >>
     qpat_assum `cenv_module_pins_mods mods caller`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [cenv_module_pins_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `contract_inv mods exps ctx caller cx` mp_tac >>
  simp[contract_inv_def, cenv_module_pins_mods_def, module_body_inv_def,
       immutable_section_layout_mods_def, build_compile_env_unit_def,
       pairTheory.ELIM_UNCURRY] >>
  strip_tac >> rpt conj_tac >> simp[]
  >- (qx_gen_tac `sid` >> qx_gen_tac `tls` >> disch_tac >>
      qpat_assum
        `!s ts. ALOOKUP mods s = SOME ts ==>
           supported_module_headers ts /\
           (s = NONE ==> supported_program ts /\
              (cx.in_deploy ==> supported_program_deploy ts)) /\
           ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel s) ts))`
        (qspecl_then [`sid`,`tls`] mp_tac) >>
      simp[])
  >~ [`acyclic_struct_metadata (make_struct_fields_map_mods mods)`]
  >- (qpat_assum `caller.ce_struct_fields = _` (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Theorem body_inv_ce_vars_update[local,simp]:
  body_inv tops ctx (cenv with ce_vars updated_by f) cx <=> body_inv tops ctx cenv cx
Proof
  simp[body_inv_split_def, contract_inv_def, module_body_inv_def,
       cenv_module_pins_mods_def, cenv_module_pins_def,
       immutable_section_layout_mods_def]
QED

Theorem body_inv_ce_return_update[local,simp]:
  body_inv tops ctx (cenv with <|ce_return_buf := rb; ce_return_pc := rpc|>) cx
  <=> body_inv tops ctx cenv cx
Proof
  simp[body_inv_split_def, contract_inv_def, module_body_inv_def,
       cenv_module_pins_mods_def, cenv_module_pins_def,
       immutable_section_layout_mods_def]
QED

Theorem compile_register_positional_args_body_inv:
  !args cenv off st cenv' st'.
    body_inv tops ctx cenv cx /\
    compile_register_positional_args cenv args off st = (cenv',st') ==>
    body_inv tops ctx cenv' cx
Proof
  Induct >- simp[compile_register_positional_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[Once compile_register_positional_args_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem materialize_internal_params_body_inv[local]:
  !caps cenv st cenv' st'.
    body_inv tops ctx cenv cx /\
    materialize_internal_params cenv caps st = (cenv',st') ==>
    body_inv tops ctx cenv' cx
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[Once materialize_internal_params_def] >>
  Cases_on `h1` >> simp[LET_THM] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_internal_prologue_body_inv:
  !cenv params has_rb ret_type st cenv' rpc st'.
    body_inv tops ctx cenv cx /\
    compile_internal_prologue cenv params has_rb ret_type st =
      ((cenv',rpc),st') ==>
    body_inv tops ctx cenv' cx
Proof
  rpt gen_tac >>
  simp[compile_internal_prologue_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[] >>
  drule_at (Pat `materialize_internal_params _ _ _ = _`)
    materialize_internal_params_body_inv >>
  disch_then (qspecl_then [`tops`, `cx`, `ctx`] mp_tac) >>
  simp[]
QED

(* A compile env that binds only parameters, with a type environment that
   has the parameters. *)
Theorem ce_locals_declared_params:
  !cenv env fargs.
    (!n l. FLOOKUP cenv.ce_vars n = SOME l ==>
           MEM n (MAP FST fargs)) /\
    (!n. MEM n (MAP FST fargs) ==> n IN FDOM env.var_types) ==>
    ce_locals_declared cenv env
Proof
  rw[ce_locals_declared_def] >> metis_tac[]
QED

Theorem build_compile_env_bound:
  !tops vis mut fname args ret body use_trans n l.
    FLOOKUP (build_compile_env tops vis mut fname args ret body
               use_trans).ce_vars n = SOME l ==>
    MEM n (MAP FST args)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `MEM n (MAP FST args)` >> simp[] >>
  drule_all allocate_args_FLOOKUP_other >> strip_tac >> gvs[]
QED

fun register_args_bound_tac def =
  Induct >- simp[def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[Once def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  first_x_assum drule_all >> simp[FLOOKUP_UPDATE] >> rw[] >> gvs[];

Theorem compile_register_positional_args_bound:
  !args cenv off st cenv' st' n l.
    compile_register_positional_args cenv args off st = (cenv', st') /\
    FLOOKUP cenv'.ce_vars n = SOME l ==>
    ?l0. FLOOKUP cenv.ce_vars n = SOME l0
Proof
  register_args_bound_tac compile_register_positional_args_def
QED

Theorem compile_register_constructor_args_bound[local]:
  !args cenv off dsz st cenv' st' n l.
    compile_register_constructor_args cenv args off dsz st = (cenv', st') /\
    FLOOKUP cenv'.ce_vars n = SOME l ==>
    ?l0. FLOOKUP cenv.ce_vars n = SOME l0
Proof
  register_args_bound_tac compile_register_constructor_args_def
QED

Theorem external_entry_declared:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   lbl cenv0 pos_args rest st cenv st' n l.
    package_external_fn tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, fbody) =
      (lbl, cenv0, pos_args, rest) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, st') /\
    FLOOKUP cenv.ce_vars n = SOME l ==>
    MEM n (MAP FST fargs)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops External mut fname fargs ret fbody
                      use_trans).ce_vars` by
    (gvs[package_external_fn_def, update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def]) >>
  drule_all compile_register_positional_args_bound >> strip_tac >>
  gvs[] >> drule build_compile_env_bound >> simp[]
QED

Theorem constructor_entry_declared:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   cenv0 pos_args rest dsz st cenv st' n l.
    package_constructor tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, fbody) =
      (cenv0, pos_args, rest) /\
    compile_register_constructor_args cenv0 pos_args 0 dsz st = (cenv, st') /\
    FLOOKUP cenv.ce_vars n = SOME l ==>
    MEM n (MAP FST fargs)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops Deploy mut fname fargs ret fbody
                      use_trans).ce_vars` by
    gvs[package_constructor_def, update_cenv_nonreentrant_def] >>
  drule_all compile_register_constructor_args_bound >> strip_tac >>
  gvs[] >> drule build_compile_env_bound >> simp[]
QED

Theorem fallback_entry_declared:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody cenv rest n
   l.
    package_fallback_fn tops use_trans nkey_map
      (SOME (mut, nr, rr, fname, fargs, dflts, ret, fbody)) =
      SOME (cenv, rest) /\
    FLOOKUP cenv.ce_vars n = SOME l ==>
    MEM n (MAP FST fargs)
Proof
  rpt gen_tac >> simp[package_fallback_fn_def, update_cenv_nonreentrant_def] >> strip_tac >>
  Cases_on `ret = NoneT` >> gvs[update_cenv_ret_abi_def] >>
  drule build_compile_env_bound >> simp[]
QED

Theorem materialize_internal_params_bound:
  !caps cenv st cenv' st' n l.
    materialize_internal_params cenv caps st = (cenv', st') /\
    FLOOKUP cenv'.ce_vars n = SOME l ==>
    (?l0. FLOOKUP cenv.ce_vars n = SOME l0) \/ MEM n (MAP FST caps)
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  qx_gen_tac `p` >> PairCases_on `p` >> rename1 `(nm,is_stack,op)::caps` >>
  rpt gen_tac >> simp[Once materialize_internal_params_def] >>
  Cases_on `is_stack` >> simp[LET_THM] >|
  [Cases_on `FLOOKUP cenv.ce_vars nm` >> simp[] >|
   [ALL_TAC,
    rename1 `FLOOKUP cenv.ce_vars nm = SOME loc` >> Cases_on `loc` >> simp[]],
   ALL_TAC] >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  first_x_assum drule_all >> simp[FLOOKUP_UPDATE] >> rw[] >> gvs[]
QED

Theorem internal_entry_declared:
  !tops use_trans nkey_map is_ctor_context immutables_len mut nr rr fname
   fargs dflts ret body fn_lbl cenv params has_rb is_nr nkey use_tr is_view
   is_ctor imm_len body' ret_type st0 cenv2 return_pc st1 n l.
    package_internal_fn tops use_trans nkey_map is_ctor_context immutables_len
      (mut, nr, rr, fname, fargs, dflts, ret, body) =
      (fn_lbl, cenv, params, has_rb, is_nr, nkey, use_tr, is_view, is_ctor,
       imm_len, body', ret_type) /\
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2, return_pc), st1) /\
    FLOOKUP cenv2.ce_vars n = SOME l ==>
    MEM n (MAP FST fargs)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[package_internal_fn_def, update_cenv_nonreentrant_def] >>
  qmatch_asmsub_abbrev_tac `compile_internal_prologue ce params` >>
  `MAP FST params = MAP FST fargs` by
    simp[Abbr `params`, MAP_ZIP, LENGTH_compute_pass_via_stack] >>
  qpat_x_assum `compile_internal_prologue _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_prologue_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  PairCases_on `params_result` >> fs[] >>
  dxrule internal_param_decls_projection >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  drule_all materialize_internal_params_bound >> strip_tac >> gvs[] >>
  gvs[Abbr `ce`] >> drule build_compile_env_bound >> simp[]
QED

Theorem bare_global_variable_decl:
  !ts id. is_bare_global_decl id ts ==>
    ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) ts /\
                      (mut = Immutable \/ ?e. mut = Constant e)
Proof
  Induct >> simp[is_bare_global_decl_def] >> Cases >>
  simp[is_bare_global_decl_def] >>
  rename1 `VariableDecl dvis dmut dname dty dslot` >>
  Cases_on `dmut` >> rw[is_bare_global_decl_def] >> metis_tac[]
QED

(* A bare global outside the constants' substitution map is an
   immutable: is_bare_global_decl covers only immutables and constants. *)
Theorem bare_global_not_const_immutable[local]:
  !ts acc id.
    is_bare_global_decl id ts /\
    ~MEM id (MAP FST (module_consts_env ts acc)) ==>
    ?vis ty slot. MEM (VariableDecl vis Immutable id ty slot) ts
Proof
  Induct >> simp[is_bare_global_decl_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[is_bare_global_decl_def, constSubstTheory.module_consts_env_def]
  >~ [`VariableDecl dvis dmut dname dty dslot`]
  >- (Cases_on `dmut` >>
      simp[is_bare_global_decl_def, constSubstTheory.module_consts_env_def]
      >~ [`subst_consts_expr acc ce`]
      >- (`MEM dname (MAP FST (module_consts_env ts
             (acc ++ [(dname, fold_const_expr (subst_consts_expr acc ce))])))` by
            (qspecl_then [`ts`, `acc ++ [(dname, fold_const_expr (subst_consts_expr acc ce))]`]
               strip_assume_tac constSubstTheory.module_consts_env_acc_prefix >> simp[]) >>
          rpt strip_tac >> gvs[] >> metis_tac[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem is_immutable_decl_variable_decl[local]:
  !ts id. is_immutable_decl id ts ==>
    ?vis ty slot. MEM (VariableDecl vis Immutable id ty slot) ts
Proof
  Induct >> rw[vyperInterpreterTheory.is_immutable_decl_def] >>
  Cases_on `h` >> gvs[vyperInterpreterTheory.is_immutable_decl_def] >>
  Cases_on `v0` >> gvs[vyperInterpreterTheory.is_immutable_decl_def] >>
  metis_tac[]
QED

(* The names expr_sim_inv's immutable clause covers, a bare global that
   is no constant or is assignable, are immutables of the module. *)
Theorem bare_global_clause_immutable:
  !env cx es tops id.
    env_consistent env cx es /\ get_module_code cx NONE = SOME tops /\
    is_bare_global_decl id tops /\
    (~cx_const_name cx (NONE,id) \/
     IS_SOME (FLOOKUP env.bare_global_assignable (NONE,id))) ==>
    ?vis ty slot. MEM (VariableDecl vis Immutable id ty slot) tops
Proof
  rpt strip_tac
  >- (irule bare_global_not_const_immutable >> simp[] >> qexists `[]` >>
      `cx_tops cx = tops` by metis_tac[gasContextTheory.cx_tops_module] >>
      gvs[exprSimHypsDefsTheory.cx_const_name_def]) >>
  `?ts. get_module_code cx NONE = SOME ts /\ is_immutable_decl id ts` by
    (gvs[IS_SOME_EXISTS, env_consistent_def, env_context_consistent_def] >>
     qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = SOME _ ==> _`
       drule >> strip_tac >> gvs[]) >>
  gvs[] >> metis_tac[is_immutable_decl_variable_decl]
QED

(* expr_sim_inv's immutable clause at a body's entry: build_compile_env
   places every immutable of a supported single-module program, and the
   installed immutables section, whose length is below 2 ** 256, holds
   each one's bytes (immutables_section_rel). *)
Theorem build_compile_env_bare_globals:
  !tops vis mut fname args ret body locks cenv cx env es imms section.
    cenv = build_compile_env tops vis mut fname args ret body locks /\
    get_module_code cx NONE = SOME tops /\
    (!src ts. get_module_code cx src = SOME ts ==> src = NONE) /\
    env_consistent env cx es /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    immutables_section_rel tops imms section /\
    LENGTH section < dimword (:256) ==>
    !src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
      (~cx_const_name cx (src,id) \/
       IS_SOME (FLOOKUP env.bare_global_assignable (src,id))) ==>
      src = cenv.ce_module /\
      ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
            !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                 off + type_memory_size tv < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >>
  `src = NONE` by metis_tac[] >> gvs[build_compile_env_module_vars] >>
  `?dvis dty dslot. MEM (VariableDecl dvis Immutable id dty dslot) tops` by
    metis_tac[bare_global_clause_immutable] >>
  drule immutable_build_compile_env_declared >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  gvs[build_compile_env_module_vars] >>
  rpt strip_tac >>
  mp_tac (Q.SPEC `tops` immutable_build_compile_env_layout) >>
  simp[immutable_section_layout_def, build_compile_env_module_vars] >>
  disch_then drule >> strip_tac >>
  `env_immutables_consistent env cx es` by fs[env_consistent_def] >>
  `IS_SOME (FLOOKUP (get_source_immutables NONE imms) id) /\
   !itv iv. FLOOKUP (get_source_immutables NONE imms) id = SOME (itv,iv) ==>
            evaluate_type (get_tenv cx) ty = SOME itv` by
    (qpat_x_assum `env_immutables_consistent _ _ _` mp_tac >>
     simp[env_immutables_consistent_def] >> rpt strip_tac >> metis_tac[SOME_11]) >>
  `?itv iv. FLOOKUP (get_source_immutables NONE imms) id = SOME (itv,iv)` by
    (gvs[IS_SOME_EXISTS] >> metis_tac[PAIR]) >>
  qpat_x_assum `tops = _`
    (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule_all immutables_section_rel_lookup >> strip_tac >>
  `tv = itv` by (res_tac >> gvs[]) >>
  qpat_x_assum `tops = _` kall_tac >>
  gvs[] >> decide_tac
QED

(* A bare global has its declared type in the compiler environment. *)
Theorem build_var_type_map_src_other[local]:
  src <> other ==> build_var_type_map_src src tops later (other,id) = later (other,id)
Proof
  Induct_on `tops` >> simp[build_var_type_map_src_def] >>
  Cases >> simp[build_var_type_map_src_def]
QED

Theorem build_var_type_map_src_has_decl[local]:
  !tops.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) /\
    MEM (VariableDecl vis mut id ty init) tops ==>
    build_var_type_map_src src tops later (src,id) = SOME ty
Proof
  Induct >> simp[] >> Cases >>
  simp[build_var_type_map_src_def, toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[] >> metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem build_var_type_map_mods_has_decl[local]:
  !mods tops. ALOOKUP mods src = SOME tops /\
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) /\
    MEM (VariableDecl vis mut id ty init) tops ==>
    build_var_type_map_mods mods (src,id) = SOME ty
Proof
  Induct >> simp[] >> PairCases >>
  rw[build_var_type_map_mods_def] >>
  gvs[build_var_type_map_src_other] >> metis_tac[build_var_type_map_src_has_decl]
QED

Theorem contract_inv_module_var_types[local]:
  contract_inv mods exps ctx cenv cx ==>
  cenv.ce_module_var_type = build_var_type_map_mods mods
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def]
QED

Theorem body_inv_bare_global_type_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods active tops cenv cx /\
  env_consistent env cx es /\ FLOOKUP env.bare_globals (src,id) = SOME ty ==>
  cenv.ce_module_var_type (src,id) = SOME ty
Proof
  strip_tac >>
  drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
  drule_all_then strip_assume_tac body_inv_modules_aligned_mods >>
  drule_then (assume_tac o SPEC_ALL) contract_inv_module_codes >>
  drule bare_global_variable_decl >>
  disch_then (qx_choosel_then [`dvis`, `dmut`, `dty`, `dslot`]
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `bare_globals_complete env.bare_globals cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `dty = ty` by
    (fs[bare_globals_complete_def] >> metis_tac[SOME_11]) >>
  drule_then assume_tac contract_inv_module_var_types >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by metis_tac[] >>
  gvs[] >> irule build_var_type_map_mods_has_decl >> simp[] >> metis_tac[]
QED

Theorem body_inv_bare_global_type:
  !tops ctx cenv cx env es src id ty.
    body_inv tops ctx cenv cx /\ env_consistent env cx es /\
    FLOOKUP env.bare_globals (src,id) = SOME ty ==>
    src = NONE /\ cenv.ce_module_var_type (src,id) = SOME ty
Proof
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac body_inv_contract >> drule_then assume_tac body_inv_module >>
  drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
  drule_then (assume_tac o SPEC_ALL) contract_inv_module_codes >>
  conj_tac >- (Cases_on `src` >> gvs[ALOOKUP_def]) >>
  drule_all body_inv_bare_global_type_mods >> simp[]
QED

(* Distinct immutables placed as build_compile_env places them occupy
   disjoint regions at their declared types. *)
Theorem cenv_module_pins_immutables_disjoint:
  !tops cenv cx id1 id2 ty1 ty2 off1 off2 tv1 tv2.
    cenv_module_pins tops cenv /\
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    get_tenv cx = type_env tops /\ id1 <> id2 /\
    FLOOKUP cenv.ce_module_vars (NONE,id1) = SOME (ImmutableLoc off1) /\
    FLOOKUP cenv.ce_module_vars (NONE,id2) = SOME (ImmutableLoc off2) /\
    cenv.ce_module_var_type (NONE,id1) = SOME ty1 /\
    cenv.ce_module_var_type (NONE,id2) = SOME ty2 /\
    evaluate_type (get_tenv cx) ty1 = SOME tv1 /\
    evaluate_type (get_tenv cx) ty2 = SOME tv2 ==>
    regions_disjoint off1 (type_memory_size tv1) off2 (type_memory_size tv2)
Proof
  rpt strip_tac >>
  `immutable_section_layout cenv tops` by
    metis_tac[cenv_module_pins_immutable_section_layout] >>
  `cenv.ce_module_var_type = build_var_type_map tops` by
    fs[cenv_module_pins_def] >>
  fs[immutable_section_layout_def] >>
  qpat_assum `!name off. _` (qspecl_then [`id1`,`off1`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`pre1`,`post1`,`v1`,`d1`,`s1`]
                strip_assume_tac) >>
  qpat_x_assum `!name off. _` (qspecl_then [`id2`,`off2`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`pre2`,`post2`,`v2`,`d2`,`s2`]
                strip_assume_tac) >>
  `MEM (VariableDecl v1 Immutable id1 d1 s1) tops` by
    metis_tac[MEM_APPEND, MEM] >>
  `MEM (VariableDecl v2 Immutable id2 d2 s2) tops` by
    metis_tac[MEM_APPEND, MEM] >>
  `d1 = ty1 /\ d2 = ty2` by metis_tac[build_maps_variable, SOME_11] >>
  `type_memory_size tv1 =
     type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty1 /\
   type_memory_size tv2 =
     type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty2` by
    metis_tac[evaluated_type_mem_bytes] >>
  ntac 2 (pop_assum SUBST1_TAC) >> rpt BasicProvers.VAR_EQ_TAC >>
  irule immutable_layout_disjoint >>
  qexistsl_tac [`id1`,`id2`,`post1`,`post2`,`s1`,`s2`,`v1`,`v2`] >> fs[]
QED
