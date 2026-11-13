(*
 * The runtime entry prefix fuel bounds of fragFuelRuntime for the packaged
 * functions lower_vyper_runtime_unit passes: its premises about the external
 * functions, selectors, groups and fallback hold for the package_* and
 * set_*_package_target forms.  A packaged environment's variables are the
 * arguments' memory slots, so it holds no pointer variable and no
 * constructor exit label.
 *
 * TOP-LEVEL:
 *   fuel_okS_runtime_unit_prefix, fuel_okS_grouped_runtime_unit_prefix,
 *   package_external_fn_ok, package_fallback_fn_ok, build_selectors_labels,
 *   package_external_groups_ok
 *)

Theory fragFuelRuntimePackage
Ancestors
  fragFuel fragFuelStmtBase fragFuelRuntime compileVyper moduleLowering
  compileEnv finite_map list pair
Libs
  fragFuelLib

val hstmts = ``!cenv' lctx ty ss Wv E.
    cenv_ptrs_in Wv cenv' /\ stmt_exits_in E cenv' lctx ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv {} E
      (compile_stmts cenv' lctx ty ss)``

val hexpr = ``!c t e Wv E. fuel_ok Wv {} E (compile_expr c t e)``

fun bn t = rhs (concl (QCONV (DEPTH_CONV BETA_CONV) t))

(* As in fragFuelRuntime. *)
val glabel = ``\g. case g of
    ExternalSingle sl pk => FST pk
  | ExternalDefaults cm ents specs hoff => cm.ec_common_label``

val gsel = ``\g. case g of
    ExternalSingle sl pk => FST (SND sl)
  | ExternalDefaults cm ents specs hoff => cm.ec_common_label``

val gstatic = ``\g. case g of
    ExternalSingle sl pk =>
      cenv_ptrs_below 0 (FST (SND pk)) /\
      (FST (SND pk)).ce_ctor_exit_label = NONE
  | ExternalDefaults cm ents specs hoff =>
      cenv_ptrs_below 0 cm.ec_env /\ cm.ec_env.ce_ctor_exit_label = NONE``

(* ===== Packaged environments ===== *)

Theorem allocate_args_no_ptr[local]:
  !ags sft off vars vs e.
    allocate_args sft ags off vars = (vs, e) /\
    (!id p sz. FLOOKUP vars id <> SOME (PtrVar p sz)) ==>
    !id p sz. FLOOKUP vs id <> SOME (PtrVar p sz)
Proof
  Induct >- simp[allocate_args_def] >>
  PairCases >> rpt gen_tac >> simp[allocate_args_def] >> strip_tac >>
  first_x_assum drule >> impl_tac >- rw[FLOOKUP_UPDATE] >> simp[]
QED

Theorem build_compile_env_ok[local]:
  !tps vs mt fnm ags rt bd ut.
    (!id p sz.
       FLOOKUP (build_compile_env tps vs mt fnm ags rt bd ut).ce_vars id <>
       SOME (PtrVar p sz)) /\
    (build_compile_env tps vs mt fnm ags rt bd ut).ce_ctor_exit_label = NONE
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> simp[]) >>
  drule allocate_args_no_ptr >> simp[]
QED

Theorem package_external_fn_ok:
  !tps ut nk tgt f.
    cenv_ptrs_below 0
      (FST (SND (set_external_package_target tgt
                   (package_external_fn tps ut nk f)))) /\
    (FST (SND (set_external_package_target tgt
                 (package_external_fn tps ut nk f)))).ce_ctor_exit_label =
      NONE /\
    FST (set_external_package_target tgt (package_external_fn tps ut nk f)) =
      "fn_" ++ FST (SND (SND (SND f)))
Proof
  rpt gen_tac >> PairCases_on `f` >> Cases_on `f6 = NoneT` >>
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       cenv_ptrs_below_def, build_compile_env_ok]
QED

Theorem package_fallback_fn_ok:
  !tps ut nk tgt fb fbc.
    set_fallback_package_target tgt (package_fallback_fn tps ut nk fb) =
      SOME fbc ==>
    cenv_ptrs_below 0 (FST fbc) /\ (FST fbc).ce_ctor_exit_label = NONE
Proof
  rpt gen_tac >> Cases_on `fb`
  >- simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  PairCases_on `x` >>
  simp[package_fallback_fn_def, set_fallback_package_target_def,
       update_cenv_nonreentrant_def] >>
  rpt strip_tac >> gvs[cenv_ptrs_below_def, build_compile_env_ok]
QED

Theorem build_selectors_labels:
  !tenv tps ut nk tgt fns.
    EVERY (\s. MEM (FST (SND s))
                 (MAP FST (MAP (set_external_package_target tgt o
                                package_external_fn tps ut nk) fns)))
      (build_selectors tenv fns)
Proof
  ntac 5 gen_tac >> Induct >- simp[build_selectors_def] >>
  PairCases >>
  simp[build_selectors_def, compute_selector_def, package_external_fn_ok] >>
  fs[EVERY_MEM]
QED

val pkg_group_st = bn ``!tps tgt ut nk f.
    ^gstatic (package_external_group tps tgt ut nk f) /\
    ^gsel (package_external_group tps tgt ut nk f) =
      ^glabel (package_external_group tps tgt ut nk f)``

Theorem package_external_group_ok[local]:
  ^pkg_group_st
Proof
  rpt gen_tac >> PairCases_on `f` >> Cases_on `f6 = NoneT` >>
  Cases_on `NULL f5` >>
  simp[package_external_group_def, package_external_fn_def,
       set_external_package_target_def, update_cenv_nonreentrant_def,
       update_cenv_ret_abi_def, cenv_ptrs_below_def, build_compile_env_ok,
       compute_selector_def]
QED

val pkg_groups_st = bn ``!tps tgt ut nk fns.
    EVERY ^gstatic (MAP (package_external_group tps tgt ut nk) fns) /\
    EVERY (\g. ^gsel g = ^glabel g)
      (MAP (package_external_group tps tgt ut nk) fns)``

Theorem package_external_groups_ok:
  ^pkg_groups_st
Proof
  rw[EVERY_MEM, MEM_MAP] >> simp[package_external_group_ok]
QED

(* ===== The prefixes for lower_vyper_runtime_unit's packages ===== *)

Theorem fuel_okS_runtime_unit_prefix:
  ^hstmts ==>
  !tps tenv tgt ut nk ext_fns fb_fn selectors external_fns fallback_fn.
    selectors = build_selectors tenv ext_fns /\
    external_fns =
      MAP (set_external_package_target tgt o package_external_fn tps ut nk)
        ext_fns /\
    fallback_fn =
      set_fallback_package_target tgt (package_fallback_fn tps ut nk fb_fn) ==>
    fuel_okS (\st. T) UNIV {} {}
      (do fallback_lbl <- fresh_label "fallback";
          compile_selector_dispatch_linear
            (MAP (\(sel, lbl, z). (sel, lbl)) selectors) fallback_lbl;
          compile_external_fn_bodies external_fns;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
                   fb_ty) =>
               compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans
                 fb_view fb_body fb_ty)
       od)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  match_mp_tac (UNDISCH fuel_okS_runtime_entry_prefix) >>
  rpt conj_tac
  >- simp[EVERY_MAP, package_external_fn_ok]
  >- MATCH_ACCEPT_TAC build_selectors_labels >>
  rpt strip_tac >> drule package_fallback_fn_ok >> simp[]
QED

Theorem fuel_okS_grouped_runtime_unit_prefix:
  ^hexpr /\ ^hstmts ==>
  !tps tgt ut nk ext_fns fb_fn groups fallback_fn.
    groups = MAP (package_external_group tps tgt ut nk) ext_fns /\
    fallback_fn =
      set_fallback_package_target tgt (package_fallback_fn tps ut nk fb_fn) ==>
    fuel_okS (\st. T) UNIV {} {}
      (do fallback_lbl <- fresh_label "fallback";
          jobs <- compile_group_dispatch_linear groups fallback_lbl;
          compile_external_jobs jobs;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
                   fb_ty) =>
               compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans
                 fb_view fb_body fb_ty)
       od)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  match_mp_tac (UNDISCH fuel_okS_grouped_runtime_entry_prefix) >>
  rpt conj_tac
  >- MATCH_ACCEPT_TAC (GEN_ALL (CONJUNCT1 (SPEC_ALL package_external_groups_ok)))
  >- MATCH_ACCEPT_TAC (GEN_ALL (CONJUNCT2 (SPEC_ALL package_external_groups_ok))) >>
  rpt strip_tac >> drule package_fallback_fn_ok >> simp[]
QED
