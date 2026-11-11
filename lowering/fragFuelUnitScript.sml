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
 *   package_internal_fn_cenv_ptrs_below
 *   generated_ctx_fns_stable    - a unit generated as entry code then internal
 *                                 functions has every function stable
 *)

Theory fragFuelUnit
Ancestors
  fragFuel fragFuelCtx fragFuelPackage fragFuelStmtBase fragFuelFunction
  compileVyper vyperCompiler moduleLowering loweringShapeProps loweringShapeDefs
  supportedProgram
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

Theorem allocate_args_vars[local]:
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

(* ===== The lowered runtime unit ===== *)

Theorem lower_vyper_runtime_unit_fns_stable:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops ==>
    !fn. MEM fn unit.cu_context.ctx_functions ==>
         ?Kf. !G. callees_stable G unit.cu_context fn ==>
                  fuel_stable (G + Kf) unit.cu_context fn
Proof
  cheat
QED
