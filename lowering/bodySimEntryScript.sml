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
 *)

Theory bodySimEntry
Ancestors
  list finite_map bodySim compileEnv compileVyper moduleLowering
  intCallCallee
Libs
  monadsyntax

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

Theorem build_compile_env_bound[local]:
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

Theorem compile_register_positional_args_bound[local]:
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
  rpt gen_tac >> simp[package_fallback_fn_def] >> strip_tac >>
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
  Cases_on `is_stack` >> simp[LET_THM] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
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
