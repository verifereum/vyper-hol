(*
 * A fuel bound for a lowered runtime unit's runs.
 *
 * Every function of the unit is fuel-stable once its callees are
 * (extract_context_fuel_stable, from the fragment bounds of the generator's
 * entry code and of each internal function).  The call graph is acyclic, so
 * the whole context is fuel-stable from some G (run_context_fuel_stable).
 * A run that ends at some fuel f then ends at G as well: at f >= G it gives
 * the same result, and at f < G more fuel changes nothing once it ended
 * (run_blocks_fuel_mono).
 *
 * TOP-LEVEL:
 *   run_context_terminates_uniform
 *   allocate_args_vars, package_internal_fn_cenv_ptrs_below
 *   generated_ctx_fns_stable    - a unit generated as entry code then internal
 *                                 functions has every function stable
 *)

Theory fragFuelUnit
Ancestors
  fragFuel fragFuelCtx fragFuelPackage fragFuelStmtBase fragFuelFunction
  fragFuelStmt fragFuelRuntime fragFuelRuntimePackage loweringShapeRules
  compileVyper vyperCompiler moduleLowering loweringShapeProps loweringShapeDefs
  supportedProgram supportedNames loweringShapeSource fragFuelExpr compileEnv
  crossBlockSimProofs passSimulationDefs venomExecSemantics finite_map list
  entryBodyBoundLabels boundLabelRules rich_list

(* ===== From per-function stability to one fuel for every run ===== *)

Theorem run_context_terminates_uniform:
  !ctx entry efn.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME entry /\
    lookup_function entry ctx.ctx_functions = SOME efn /\
    (!fn. MEM fn ctx.ctx_functions ==>
          ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn) ==>
    ?G. !f s. terminates (run_context f ctx s) ==>
              terminates (run_context G ctx s)
Proof
  rpt strip_tac >> drule_all run_context_fuel_stable >> strip_tac >>
  qexists_tac `G` >> rpt strip_tac >>
  Cases_on `G <= f` >- metis_tac[] >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[run_context_def, run_function_def] >>
  Cases_on `fn_entry_label efn` >- simp[terminates_def] >>
  simp[] >> strip_tac >> drule run_blocks_fuel_mono >>
  disch_then (qspec_then `G - f` mp_tac) >>
  `f + (G - f) = G` by decide_tac >> simp[]
QED

(* ===== The packaged internal functions' environments ===== *)

Theorem allocate_args_vars:
  !args sft off vars vars' off' id v.
    allocate_args sft args off vars = (vars', off') /\
    FLOOKUP vars' id = SOME v ==>
    FLOOKUP vars id = SOME v \/ ?off2 sz. v = MemLoc off2 sz
Proof
  Induct >- simp[allocate_args_def] >>
  Cases >> simp[allocate_args_def] >> rpt strip_tac >>
  first_x_assum drule_all >> rw[FLOOKUP_UPDATE] >> gvs[]
QED

(* A packaged internal function's locals are its parameters, at fixed
   memory locations: no local is a pointer variable. *)
Theorem package_internal_fn_cenv_ptrs_below:
  !tops use_trans nkey_map is_ctor imm_len src target n.
    cenv_ptrs_below n
      (FST (SND (set_internal_package_target target
                   (package_internal_fn tops use_trans nkey_map is_ctor
                      imm_len src))))
Proof
  rpt gen_tac >> PairCases_on `src` >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def, build_compile_env_def,
       cenv_ptrs_below_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  drule_all allocate_args_vars >> simp[]
QED

(* ===== The internal functions ===== *)

Theorem cenv_ptrs_below_pre[local]:
  !cenv. (!n. cenv_ptrs_below n cenv) ==>
         (\st:compile_state. cenv_ptrs_below st.cs_next_var cenv) = (\st. T)
Proof
  simp[FUN_EQ_THM]
QED

Theorem package_internal_fn_ctor_exit[local]:
  !tops use_trans nkey_map is_ctor imm_len src target.
    (FST (SND (set_internal_package_target target
                 (package_internal_fn tops use_trans nkey_map is_ctor imm_len
                    src)))).ce_ctor_exit_label = NONE
Proof
  rpt gen_tac >> PairCases_on `src` >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* Each internal function's code is a closed fragment, from any state, for
   any constructor flag and immutables length. *)
Theorem package_internal_fns_fuel:
  !tops ut nkm ic il target srcs.
    EVERY (\(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
             is_view, is_ctor, imm_len, body, ret_type).
             ?Wv. fuel_okS (\st. T) Wv {} {}
                    (compile_internal_function cenv params has_ret_buf is_nr
                       nkey use_trans is_view is_ctor imm_len body ret_type))
      (MAP (set_internal_package_target target o
            package_internal_fn tops ut nkm ic il) srcs)
Proof
  rpt gen_tac >> simp[EVERY_MAP, EVERY_MEM] >> qx_gen_tac `src` >> strip_tac >>
  qspecl_then [`tops`, `ut`, `nkm`, `ic`, `il`, `src`, `target`] mp_tac
    package_internal_fn_ctor_exit >>
  qspecl_then [`tops`, `ut`, `nkm`, `ic`, `il`, `src`, `target`]
    mp_tac package_internal_fn_cenv_ptrs_below >>
  Cases_on `set_internal_package_target target
              (package_internal_fn tops ut nkm ic il src)` >>
  PairCases_on `r` >> simp[] >> rpt strip_tac >>
  qexists_tac `UNIV` >>
  drule cenv_ptrs_below_pre >> disch_then (SUBST1_TAC o SYM) >>
  irule fuel_okS_compile_internal_function >> simp[] >>
  rpt strip_tac >> irule (CONJUNCT2 fuel_okS_compile_stmt) >> simp[]
QED

(* ===== A generated unit ===== *)

(* A unit whose generator is entry code (prefix) followed by the internal
   functions: each of its functions is stable once its callees are.  The
   entry code's shape keeps the internal labels out of its blocks. *)
Theorem generated_ctx_fns_stable:
  !prefix ifns P0 Wv mid r st1 ctx data.
    prefix (initial_compile_state "__entry") = ((), mid) /\
    EVERY (\l. l = "__entry" \/ jump_label_ok l)
      (MAP (\bb. bb.bb_label)
        (all_blocks (SND (prefix (initial_compile_state "__entry"))))) /\
    fuel_okS P0 Wv {} {} prefix /\ P0 (initial_compile_state "__entry") /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns)) /\
    EVERY (\(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
             is_view, is_ctor, imm_len, body, ret_type).
             ?Wv. fuel_okS (\st. T) Wv {} {}
                    (compile_internal_function cenv params has_ret_buf is_nr
                       nkey use_trans is_view is_ctor imm_len body ret_type))
      ifns /\
    compile_internal_fn_bodies ifns mid = (r, st1) /\
    extract_context_with_internals "__entry" ifns st1 = SOME (ctx, data) /\
    lowering_context_ok ctx ==>
    !fn. MEM fn ctx.ctx_functions ==>
         ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\d. internal_label_ok (FST d) /\
               ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks mid)))
     (internal_fn_descriptors ifns)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     `FST d <> "__entry"` by (strip_tac >> gvs[internal_label_ok_def]) >>
     metis_tac[jump_label_ok_names]) >>
  `EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions` by
    fs[lowering_context_ok_def, EVERY_MEM] >>
  qspecl_then [`prefix`, `P0`, `\st. T`, `"__entry"`, `ifns`, `()`, `mid`,
               `r`, `st1`, `ctx`, `data`, `Wv`] mp_tac
    extract_context_fuel_stable_from_labels >>
  impl_tac >- simp[next_stable_def] >> simp[]
QED

(* A unit generated as entry code then the internal functions, by a
   generator split that way: each of its functions is stable. *)
Theorem split_unit_fns_stable:
  !prefix ifns st1 ctx data.
    comp_ignore_bind (prefix : unit compiler)
      (comp_bind (compile_internal_fn_bodies ifns) (\x. comp_return ()))
      (initial_compile_state "__entry") = ((), st1) /\
    EVERY (\l. l = "__entry" \/ jump_label_ok l)
      (MAP (\bb. bb.bb_label)
        (all_blocks (SND (prefix (initial_compile_state "__entry"))))) /\
    fuel_okS (\st. T) UNIV {} {} prefix /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns)) /\
    EVERY (\(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
             is_view, is_ctor, imm_len, body, ret_type).
             ?Wv. fuel_okS (\st. T) Wv {} {}
                    (compile_internal_function cenv params has_ret_buf is_nr
                       nkey use_trans is_view is_ctor imm_len body ret_type))
      ifns /\
    extract_context_with_internals "__entry" ifns st1 = SOME (ctx, data) /\
    lowering_context_ok ctx ==>
    !fn. MEM fn ctx.ctx_functions ==>
         ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `prefix (initial_compile_state "__entry")` >>
  rename1 `prefix _ = (u, mid)` >> Cases_on `u` >>
  qspecl_then [`prefix`, `ifns`, `\st. T`, `UNIV`, `mid`] mp_tac
    generated_ctx_fns_stable >>
  simp[] >> strip_tac >>
  qpat_x_assum `comp_ignore_bind _ _ _ = _` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

(* ===== The lowered runtime unit ===== *)

Theorem empty_internal_suffix_state[local]:
  !prefix : unit compiler. !st.
    SND (comp_ignore_bind prefix
      (comp_bind (compile_internal_fn_bodies []) (\x. comp_return ())) st) =
    SND (prefix st)
Proof
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, pairTheory.ELIM_UNCURRY]
QED

Theorem package_external_group_labels_ok[local]:
  !tops target use_trans nkeys src.
    external_group_labels_ok (\l. l = "__entry" \/ jump_label_ok l)
      (package_external_group tops target use_trans nkeys src)
Proof
  rpt gen_tac >> PairCases_on `src` >> simp[package_external_group_def] >>
  IF_CASES_TAC >>
  simp[external_group_labels_ok_def, package_external_fn_def,
       set_external_package_target_def, jump_label_ok_def, IS_PREFIX_APPEND,
       external_common_label_def] >>
  simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD, external_prefix_label_def,
       compute_selector_def, IS_PREFIX_APPEND]
QED

Theorem lower_vyper_runtime_unit_fns_stable:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops ==>
    !fn. MEM fn unit.cu_context.ctx_functions ==>
         ?Kf. !G. callees_stable G unit.cu_context fn ==>
                  fuel_stable (G + Kf) unit.cu_context fn
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
                   (FST (SND (classify_functions tops))))` by
    (irule supported_names_internal_names_distinct >>
     fs[supported_program_def, supported_declaration_names_def]) >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts, ints, fb, ctor)` >>
  qspecl_then [`tops`, `F`] mp_tac internal_descriptors_ok >>
  impl_tac >- fs[] >>
  qpat_assum `classify_functions tops = _`
    (fn th => REWRITE_TAC [th, pairTheory.FST, pairTheory.SND]) >>
  strip_tac >>
  `EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt).
      lbl = "__entry" \/ jump_label_ok lbl)
    (MAP (set_external_package_target rpolicy.rpol_target o
           package_external_fn tops T (K global_nonreentrant_slot)) exts)` by
    (simp[EVERY_MAP, EVERY_MEM] >> gen_tac >> PairCases_on `x` >>
     simp[package_external_fn_def, set_external_package_target_def,
          jump_label_ok_def, IS_PREFIX_APPEND]) >>
  `EVERY (external_group_labels_ok (\l. l = "__entry" \/ jump_label_ok l))
    (MAP (package_external_group tops rpolicy.rpol_target T
          (K global_nonreentrant_slot)) exts)` by
    (simp[EVERY_MAP, EVERY_MEM] >> metis_tac[package_external_group_labels_ok]) >>
  qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`,
               `F`, `0`, `rpolicy.rpol_target`,
               `order_internals (runtime_internal_order tops ints) ints`]
    assume_tac package_internal_fns_fuel >>
  `ALL_DISTINCT (MAP FST (MAP (source_internal_fn_descriptor tops F)
     (order_internals (runtime_internal_order tops ints) ints)))`
    by (REWRITE_TAC [listTheory.MAP_MAP_o] >>
        irule ALL_DISTINCT_order_runtime_internals >> fs[listTheory.MAP_MAP_o]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  qpat_x_assum `classify_functions tops = _` (fn th => REWRITE_TAC [th]) >>
  simp[] >> rpt (disch_then strip_assume_tac)
  >~ [`run_grouped_lowering`]
  >- (qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` mp_tac >>
      simp[run_grouped_lowering_def] >> pairarg_tac >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      qpat_x_assum `compile_generate_grouped_runtime _ _ _ _ = _` mp_tac >>
      REWRITE_TAC [compile_generate_grouped_runtime_split] >> strip_tac >>
      mp_tac (INST_TYPE [alpha |-> ``:expr list``] fuel_okS_grouped_runtime_unit_prefix) >>
      impl_tac >- simp[fuel_okS_compile_stmt, fuel_ok_compile_expr] >>
      strip_tac >>
      `fuel_okS (\st. T) UNIV {} {}
         (do fallback_lbl <- fresh_label "fallback";
            jobs <- compile_group_dispatch_linear
                      (MAP (package_external_group tops rpolicy.rpol_target T
                              (K global_nonreentrant_slot)) exts) fallback_lbl;
            compile_external_jobs jobs;
            new_block fallback_lbl;
            (case set_fallback_package_target rpolicy.rpol_target
                  (package_fallback_fn tops T (K global_nonreentrant_slot) fb) of
               NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
             | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
                     fb_ty) =>
                 compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans
                   fb_view fb_body fb_ty)
          od)` by
        (first_x_assum irule >>
         qexistsl_tac [`exts`, `fb`, `K global_nonreentrant_slot`,
                       `rpolicy.rpol_target`, `tops`, `T`] >> simp[]) >>
      `EVERY (\l. l = "__entry" \/ jump_label_ok l)
         (MAP (\bb. bb.bb_label) (all_blocks
           (SND (compile_generate_grouped_runtime
             (MAP (package_external_group tops rpolicy.rpol_target T
                    (K global_nonreentrant_slot)) exts) []
             (set_fallback_package_target rpolicy.rpol_target
               (package_fallback_fn tops T (K global_nonreentrant_slot) fb))
             (initial_compile_state "__entry")))))` by
        (irule bound_labels_runtime_grouped_no_internals >>
         simp[jump_label_ok_def, initial_compile_state_def, all_blocks_def]) >>
      pop_assum (assume_tac o REWRITE_RULE
        [compile_generate_grouped_runtime_split, empty_internal_suffix_state]) >>
      drule split_unit_fns_stable >>
      disch_then (qspecl_then [`ctx`, `data`] assume_tac) >>
      rpt strip_tac >> first_x_assum irule >> rpt conj_tac >>
      gs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
         internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP,
         EVERY_MEM] >>
      fs[MEM_MAP, PULL_EXISTS]) >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def] >> pairarg_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pop_assum (fn th => REWRITE_TAC [th, compile_generate_runtime_linear_split]) >>
  strip_tac >>
  mp_tac (INST_TYPE [alpha |-> ``:expr``, beta |-> ``:expr list``]
            fuel_okS_runtime_unit_prefix) >>
  impl_tac >- simp[fuel_okS_compile_stmt] >>
  strip_tac >>
  `fuel_okS (\st. T) UNIV {} {}
     (do fallback_lbl <- fresh_label "fallback";
        compile_selector_dispatch_linear
          (MAP (\(sel, lbl, z). (sel, lbl))
             (build_selectors (type_env tops) exts)) fallback_lbl;
        compile_external_fn_bodies
          (MAP (set_external_package_target rpolicy.rpol_target o
                package_external_fn tops T (K global_nonreentrant_slot)) exts);
        new_block fallback_lbl;
        (case set_fallback_package_target rpolicy.rpol_target
              (package_fallback_fn tops T (K global_nonreentrant_slot) fb) of
           NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
         | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
                 fb_ty) =>
             compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans
               fb_view fb_body fb_ty)
      od)` by
    (first_x_assum irule >>
     qexistsl_tac [`exts`, `fb`, `K global_nonreentrant_slot`, `type_env tops`,
                   `rpolicy.rpol_target`, `tops`, `T`] >> simp[]) >>
  `EVERY (\l. l = "__entry" \/ jump_label_ok l)
     (MAP (\bb. bb.bb_label) (all_blocks
       (SND (compile_generate_runtime (build_selectors (type_env tops) exts)
         (MAP (set_external_package_target rpolicy.rpol_target o
               package_external_fn tops T (K global_nonreentrant_slot)) exts)
         []
         (set_fallback_package_target rpolicy.rpol_target
           (package_fallback_fn tops T (K global_nonreentrant_slot) fb))
         Linear bc mb db ei (initial_compile_state "__entry")))))` by
    (irule bound_labels_runtime_linear_no_internals >>
     simp[initial_compile_state_def, all_blocks_def] >>
     simp[jump_label_ok_def]) >>
  pop_assum (assume_tac o REWRITE_RULE
    [compile_generate_runtime_linear_split, empty_internal_suffix_state]) >>
  drule split_unit_fns_stable >>
  disch_then (qspecl_then [`ctx`, `data`] assume_tac) >>
  rpt strip_tac >> first_x_assum irule >> rpt conj_tac >>
  gs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
     internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP, EVERY_MEM] >>
  fs[MEM_MAP, PULL_EXISTS]
QED
