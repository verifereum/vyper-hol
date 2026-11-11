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
 *)

Theory fragFuelUnit
Ancestors
  fragFuel fragFuelCtx fragFuelPackage fragFuelStmtBase fragFuelFunction
  compileVyper vyperCompiler crossBlockSimProofs passSimulationDefs
  venomExecSemantics finite_map list

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

