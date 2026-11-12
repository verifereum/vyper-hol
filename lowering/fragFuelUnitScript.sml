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
  !tops use_trans nkey_map imm_len src target.
    (FST (SND (set_internal_package_target target
                 (package_internal_fn tops use_trans nkey_map F imm_len src)))).
      ce_ctor_exit_label = NONE
Proof
  rpt gen_tac >> PairCases_on `src` >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* Each runtime internal function's code is a closed fragment, from any
   state. *)
Theorem package_internal_fns_fuel:
  !tops use_trans nkey_map target srcs.
    EVERY (\(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
             is_view, is_ctor, imm_len, body, ret_type).
             ?Wv. fuel_okS (\st. T) Wv {} {}
                    (compile_internal_function cenv params has_ret_buf is_nr
                       nkey use_trans is_view is_ctor imm_len body ret_type))
      (MAP (set_internal_package_target target o
            package_internal_fn tops use_trans nkey_map F 0) srcs)
Proof
  rpt gen_tac >> simp[EVERY_MAP, EVERY_MEM] >> qx_gen_tac `src` >> strip_tac >>
  qspecl_then [`tops`, `use_trans`, `nkey_map`, `0`, `src`, `target`] mp_tac
    package_internal_fn_ctor_exit >>
  qspecl_then [`tops`, `use_trans`, `nkey_map`, `F`, `0`, `src`, `target`]
    mp_tac package_internal_fn_cenv_ptrs_below >>
  Cases_on `set_internal_package_target target
              (package_internal_fn tops use_trans nkey_map F 0 src)` >>
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
    shape_step F jump_label_ok (\st. T) prefix (\u st. T) /\
    fuel_okS P0 Wv {} {} prefix /\ P0 (initial_compile_state "__entry") /\
    EVERY internal_fn_shape_ok ifns /\
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
  `shape_extends F jump_label_ok (initial_compile_state "__entry") mid /\
   shape_state mid` by
    (qpat_x_assum `shape_step _ _ _ prefix _` mp_tac >>
     simp[shape_step_def] >> disch_then drule >>
     simp[shape_state_initial_compile_state]) >>
  drule initial_entry_blocks_shape >> strip_tac >>
  `!d. MEM d (internal_fn_descriptors ifns) ==> internal_label_ok (FST d)` by
    fs[EVERY_MEM] >>
  `EVERY (\d. ~compiler_label (FST d) /\
              ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks mid)))
     (internal_fn_descriptors ifns)` by
    (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
     first_x_assum drule >> strip_tac >>
     qspecl_then [`FST d`, `all_blocks mid`] mp_tac
       internal_name_not_entry_label >> simp[]) >>
  `EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions` by
    fs[lowering_context_ok_def, EVERY_MEM] >>
  qspecl_then [`prefix`, `P0`, `\st. T`, `"__entry"`, `ifns`, `()`, `mid`,
               `r`, `st1`, `ctx`, `data`, `Wv`] mp_tac
    extract_context_fuel_stable >>
  impl_tac >- simp[next_stable_def] >> simp[]
QED

(* grouped_runtime_entry_prefix_shape of loweringShapeProps, which is local
   there. *)
Theorem grouped_prefix_shape[local]:
  !groups fallback_fn.
    EVERY external_group_shape_ok groups /\ fallback_shape_ok fallback_fn ==>
    shape_step F jump_label_ok (\st. T)
      (do fallback_lbl <- fresh_label "fallback";
          jobs <- compile_group_dispatch_linear groups fallback_lbl;
          compile_external_jobs jobs;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (ce,pay,nr,key,trans,view,stmts,ret) =>
               compile_fallback_body ce pay nr key trans view stmts ret)
       od) (\u st. T)
Proof
  rpt gen_tac >> strip_tac >>
  irule shape_step_bind >>
  qexists_tac `\lbl st. T /\ compiler_label lbl /\ label_sfx "fallback" lbl` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >> simp[shape_stable_def]) >>
  qx_gen_tac `lbl` >> BETA_TAC >>
  reverse (Cases_on `compiler_label lbl /\ label_sfx "fallback" lbl`)
  >- simp[shape_step_def] >>
  `~label_sfx "dispatch" lbl` by
    (strip_tac >> `lbl <> lbl` suffices_by simp[] >>
     irule label_sfx_distinct >> qexistsl_tac [`"fallback"`, `"dispatch"`] >>
     simp[]) >>
  irule shape_step_bind >>
  qexists_tac `\jobs st. EVERY (external_job_shape_ok st) jobs` >> reverse conj_tac
  >- (irule shape_step_conseq >>
      qexistsl_tac [`jump_label_ok`, `\st. T`,
        `\jobs st. EVERY (external_job_shape_ok st) jobs`] >> simp[] >>
      irule compile_group_dispatch_linear_shape >> fs[jump_label_ok_def]) >>
  qx_gen_tac `jobs` >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> reverse conj_tac
  >- irule compile_external_jobs_shape >>
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >> qexists_tac `\u st. T` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_new_block >> simp[shape_stable_def, jump_label_ok_def]) >>
  gen_tac >> BETA_TAC >> irule runtime_fallback_shape >> simp[]
QED

(* A unit generated as entry code then the internal functions, by a
   generator split that way: each of its functions is stable. *)
Theorem split_unit_fns_stable:
  !prefix ifns st1 ctx data.
    comp_ignore_bind (prefix : unit compiler)
      (comp_bind (compile_internal_fn_bodies ifns) (\x. comp_return ()))
      (initial_compile_state "__entry") = ((), st1) /\
    shape_step F jump_label_ok (\st. T) prefix (\u st. T) /\
    fuel_okS (\st. T) UNIV {} {} prefix /\
    EVERY internal_fn_shape_ok ifns /\
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

Theorem lower_vyper_runtime_unit_fns_stable:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops ==>
    !fn. MEM fn unit.cu_context.ctx_functions ==>
         ?Kf. !G. callees_stable G unit.cu_context fn ==>
                  fuel_stable (G + Kf) unit.cu_context fn
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
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
  `EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl)
     (build_selectors (type_env tops) exts)`
    by REWRITE_TAC [build_selectors_fn_labels] >>
  `!x. MEM x exts ==>
       external_fn_shape_ok
         (set_external_package_target rpolicy.rpol_target
            (package_external_fn tops T (K global_nonreentrant_slot) x))`
    by (rpt strip_tac >> irule package_external_fn_shape_ok >> gs[]) >>
  `!x. MEM x exts ==>
       external_group_shape_ok
         (package_external_group tops rpolicy.rpol_target T
           (K global_nonreentrant_slot) x)`
    by (rpt strip_tac >> irule package_external_group_shape_ok >> gs[]) >>
  `!x. MEM x ints ==>
       internal_fn_shape_ok
         (set_internal_package_target rpolicy.rpol_target
            (package_internal_fn tops T (K global_nonreentrant_slot) F 0 x))`
    by (rpt strip_tac >> irule package_internal_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok
     (set_fallback_package_target rpolicy.rpol_target
        (package_fallback_fn tops T (K global_nonreentrant_slot) fb))`
    by (qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`,
                     `rpolicy.rpol_target`] mp_tac package_fallback_fn_shape_ok >>
        gs[]) >>
  `shape_step F jump_label_ok (\st. T)
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
      od) (\x st. T)` by
    (irule runtime_entry_prefix_shape >> simp[EVERY_MAP, EVERY_MEM]) >>
  `shape_step F jump_label_ok (\st. T)
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
      od) (\u st. T)` by
    (irule grouped_prefix_shape >> simp[EVERY_MAP, EVERY_MEM]) >>
  qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`,
               `rpolicy.rpol_target`, `ints`] assume_tac package_internal_fns_fuel >>
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
  drule split_unit_fns_stable >>
  disch_then (qspecl_then [`ctx`, `data`] assume_tac) >>
  rpt strip_tac >> first_x_assum irule >> rpt conj_tac >>
  gs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
     internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP, EVERY_MEM] >>
  fs[MEM_MAP, PULL_EXISTS]
QED
