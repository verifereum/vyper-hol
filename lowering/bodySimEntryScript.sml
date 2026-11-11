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
  list finite_map bodySim compileEnv compileVyper moduleLowering
  intCallCallee supportedDecls supportedProgram vyperTypeInvariants
  immutableLocationProps immutableSectionRel immutableRelation option pair
Libs
  monadsyntax

(* Rebuilding an internal callee's environment uses the same checked
   module metadata as its caller. *)
Theorem body_inv_build_internal_env:
  body_inv tops ctx caller cx ==>
  body_inv tops ctx
    ((build_compile_env tops Internal mut fname args ret stmts use_trans)
       with <| ce_target := caller.ce_target;
               ce_is_ctor := caller.ce_is_ctor |>) cx
Proof
  rw[body_inv_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
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
  goal_assum (drule_at Any) >> simp[] >>
  gvs[body_inv_def] >> metis_tac[]
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
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  TRY (rename1 `SOME loc` >> Cases_on `loc` >> simp[]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[body_inv_def] >> metis_tac[]
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
  (impl_tac >- (gvs[body_inv_def] >> metis_tac[])) >> simp[]
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
  gvs[] >> drule build_compile_env_bound >> simp[]
QED

Theorem materialize_internal_params_bound[local]:
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

(* A supported program declares no constants, so every bare global of it
   is an immutable. *)
Theorem supported_bare_global_immutable:
  !tops id.
    supported_declaration_headers tops /\ is_bare_global_decl id tops ==>
    ?vis ty slot. MEM (VariableDecl vis Immutable id ty slot) tops
Proof
  simp[supported_declaration_headers_def] >>
  `!ts tops id.
     EVERY (supported_declaration_header tops) ts /\
     is_bare_global_decl id ts ==>
     ?vis ty slot. MEM (VariableDecl vis Immutable id ty slot) ts`
    suffices_by metis_tac[] >>
  Induct >> simp[is_bare_global_decl_def] >> rpt strip_tac >>
  Cases_on `h` >> gvs[is_bare_global_decl_def]
  >~ [`VariableDecl dvis dmut dname dty dslot`]
  >- (Cases_on `dmut` >> Cases_on `dvis` >> Cases_on `dslot` >>
      Cases_on `dname = id` >>
      gvs[is_bare_global_decl_def, supported_declaration_header_def] >>
      metis_tac[]) >>
  metis_tac[]
QED

(* expr_sim_inv's immutable clause at a body's entry: build_compile_env
   places every immutable of a supported single-module program, and the
   installed immutables section, whose length is below 2 ** 256, holds
   each one's bytes (immutables_section_rel). *)
Theorem build_compile_env_bare_globals:
  !tops vis mut fname args ret body locks cenv cx env es imms section.
    cenv = build_compile_env tops vis mut fname args ret body locks /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    (!src ts. get_module_code cx src = SOME ts ==> src = NONE) /\
    env_consistent env cx es /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    immutables_section_rel tops imms section /\
    LENGTH section < dimword (:256) ==>
    !src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==>
      src = cenv.ce_module /\
      ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
            !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
                 off + type_memory_size tv < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >>
  `src = NONE` by metis_tac[] >> gvs[build_compile_env_module_vars] >>
  `?dvis dty dslot. MEM (VariableDecl dvis Immutable id dty dslot) tops` by
    metis_tac[supported_bare_global_immutable, supported_program_def] >>
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
