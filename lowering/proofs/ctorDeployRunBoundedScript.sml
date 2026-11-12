(*
 * Fuel bounds for the lowered deploy unit: every function of
 * dunit.cu_context is stable once its callees are, so one fuel bounds every
 * terminating run of the unit.
 *
 * The deploy-only code (payable check, immutables region, constructor
 * argument registration, the constructor body's exit block and the
 * runtime-code copy-out, or the constructor-less copy-out) is chained
 * segment by segment; statements and internal functions use the fragFuel
 * bounds shared with the runtime unit.
 *
 * TOP-LEVEL:
 *   deploy_unit_fns_fuel_stable, deploy_unit_context_ok,
 *   run_context_uniform_fuel,
 *   fuel_ok_compile_constructor_epilogue, fuel_ok_compile_simple_deploy,
 *   fuel_ok_compile_register_constructor_args,
 *   compile_register_constructor_args_ptrs,
 *   package_constructor_cenv_ptrs_below, package_internal_fns_fuel_any
 *)

Theory ctorDeployRunBounded
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelPackage moduleLowering
  emitHelper context venomInst ctxLookupAgree compileEnv compileVyper
  vyperCompiler ctorDeployDefs ctorGeneratorShape loweringShapeDefs
  ctorDeployLoweringCode fragFuelCtx passSimulationDefs venomExecProps
  venomExecSemantics fragFuelStmtBase fragFuelExprHelpers fragFuelRuntimeBody
  fragFuelFunction fragFuelStmt fragFuelUnit finite_map option list
  ctorDeployLoweringCodeShape ctorUnitShape
Libs
  fragFuelLib

Theorem fuel_ok_compile_constructor_epilogue:
  !rt imm buf Wv E.
    fuel_ok Wv {} E (compile_constructor_epilogue rt imm buf)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_constructor_epilogue_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_halt,
             fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_simple_deploy:
  !rt imm Wv E. fuel_ok Wv {} E (compile_simple_deploy rt imm)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_simple_deploy_def] >>
  fuel_auto [fuel_ok_emit_void, fuel_ok_emit_inst_halt,
             fuel_ok_compile_alloc_buffer] >>
  simp[is_terminator_def]
QED

(* The deploy lowering's install_immutable_reservation only sets
   ctx_global_reserved, which no run reads. *)
Theorem ctx_agree_global_reserved[local]:
  ctx_agree (\x. T) ctx (ctx with ctx_global_reserved := r)
Proof
  simp[ctx_agree_def, fn_calls_within_def, inst_calls_within_def,
       listTheory.EVERY_MEM]
QED

Theorem fuel_stable_global_reserved:
  fuel_stable G (ctx with ctx_global_reserved := r) fn <=> fuel_stable G ctx fn
Proof
  `!f s. run_blocks f (ctx with ctx_global_reserved := r) fn s =
         run_blocks f ctx fn s`
    by (rpt gen_tac >> irule EQ_SYM >>
        irule (cj 3 (MATCH_MP run_defs_ctx_agree ctx_agree_global_reserved)) >>
        simp[fn_calls_within_def, inst_calls_within_def,
             listTheory.EVERY_MEM]) >>
  simp[fuel_stable_def]
QED

Theorem callees_stable_global_reserved:
  callees_stable G (ctx with ctx_global_reserved := r) fn <=>
  callees_stable G ctx fn
Proof
  simp[callees_stable_def, fuel_stable_global_reserved]
QED

(* ===== Closed segments between two concrete states ===== *)

(* fuel_okS ((=) st) UNIV L E (\s. ((), st')) says the code emitted from st
   to st' is a fragment (entries L, exits E) of bounded fuel. *)

Theorem fuel_ok_at:
  !m st x st'.
    m st = (x, st') ==>
    !L E. fuel_ok UNIV L E m ==> fuel_okS ((=) st) UNIV L E (\s. ((), st'))
Proof
  rw[fuel_okS_def, fuel_ok_def] >> metis_tac[]
QED

Theorem fuel_okS_at:
  !P Wv m st x st' L E.
    fuel_okS P Wv L E m /\ P st /\ m st = (x, st') ==>
    fuel_okS ((=) st) UNIV L E (\s. ((), st'))
Proof
  rw[fuel_okS_def] >> first_x_assum drule_all >> strip_tac >> simp[] >>
  qexists_tac `Kb` >> irule frag_fuel_mono >>
  qexistsl_tac [`E`, `Kb`, `L`, `Wv`] >> simp[]
QED

Theorem fuel_okS_at_seq:
  !a b c L1 L2 E1 E2 E.
    fuel_okS ((=) a) UNIV L1 E1 (\s. ((), b)) /\
    fuel_okS ((=) b) UNIV L2 E2 (\s. ((), c)) /\
    E1 SUBSET E UNION L2 /\ E2 SUBSET E ==>
    fuel_okS ((=) a) UNIV (L1 UNION L2) E (\s. ((), c))
Proof
  rpt strip_tac >>
  `cs_extends a b /\ a.cs_next_var <= b.cs_next_var /\
   (cs_no_phi a ==> cs_no_phi b) /\ ?n1. frag_fuel UNIV L1 E1 a b n1` by
    (fs[fuel_okS_def] >> metis_tac[]) >>
  `cs_extends b c /\ b.cs_next_var <= c.cs_next_var /\
   (cs_no_phi b ==> cs_no_phi c) /\ ?n2. frag_fuel UNIV L2 E2 b c n2` by
    (fs[fuel_okS_def] >> metis_tac[]) >>
  `cs_extends a c` by metis_tac[cs_extends_trans] >>
  `a.cs_next_var <= c.cs_next_var` by decide_tac >>
  `frag_fuel UNIV (L1 UNION L2) E a c (n1 + n2)` by
    (irule frag_fuel_seq >> metis_tac[]) >>
  simp[fuel_okS_def] >> metis_tac[]
QED

Theorem fuel_okS_at_mono:
  !a b L L' E E'.
    fuel_okS ((=) a) UNIV L E (\s. ((), b)) /\ L' SUBSET L /\ E SUBSET E' ==>
    fuel_okS ((=) a) UNIV L' E' (\s. ((), b))
Proof
  rpt strip_tac >> irule fuel_okS_mono >>
  qexistsl_tac [`E`, `L`, `(=) a`, `UNIV`] >> simp[]
QED

(* ===== The constructor's entry code ===== *)

(* Turn the assumption m st = (x, st') matching pat into a segment goal
   fuel_ok UNIV L E m. *)
fun seg_tac pat =
  qpat_x_assum pat (assume_tac o MATCH_MP fuel_ok_at) >> pop_assum irule

(* The deploy function's code with a constructor, from the payable check to
   the epilogue, chained from its pieces.  The argument registration
   (st1 to st2), the lock (st2 to st3), the body (sa to sb, which may jump
   to the exit label) and the unlock (st_exit to st_epilogue) come in as
   segments. *)
Theorem deploy_ctor_entry_fuel:
  !pay cap rt imm exit_lbl old_bb st0 st_pay st1 st2 st3 sa sb sj st_exit
   st_epilogue st_final.
    (if pay then comp_return () else
       comp_bind (emit_op CALLVALUE []) (\cv.
         comp_bind (emit_op ISZERO [cv]) (\v. emit_void ASSERT [v])))
      st0 = ((), st_pay) /\
    (if cap > 0 then
       comp_bind (compile_fixed_region_with_id cap)
         (\r. comp_return (SND r).buf_operand)
     else comp_return (Lit 0w)) st_pay = (imm, st1) /\
    fuel_okS ((=) st1) UNIV {} {} (\s. ((), st2)) /\
    fuel_okS ((=) st2) UNIV {} {} (\s. ((), st3)) /\
    fresh_label "ctor_exit" st3 = (exit_lbl, sa) /\
    fuel_okS ((=) sa) UNIV {} {exit_lbl} (\s. ((), sb)) /\
    (if block_is_terminated sb then comp_return ()
     else emit_inst JMP [Label exit_lbl] []) sb = ((), sj) /\
    new_block exit_lbl sj = (old_bb, st_exit) /\
    fuel_okS ((=) st_exit) UNIV {} {} (\s. ((), st_epilogue)) /\
    compile_constructor_epilogue rt cap imm st_epilogue = ((), st_final) ==>
    fuel_okS ((=) st0) UNIV {} {} (\s. ((), st_final))
Proof
  rpt strip_tac >>
  `fuel_okS ((=) st0) UNIV {} {} (\s. ((), st_pay))` by
    (seg_tac `_ st0 = ((), st_pay)` >>
     fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void] >> simp[is_terminator_def]) >>
  `fuel_okS ((=) st_pay) UNIV {} {} (\s. ((), st1))` by
    (seg_tac `_ st_pay = (imm, st1)` >>
     fuel_auto [fuel_ok_compile_fixed_region_with_id]) >>
  `fuel_okS ((=) st3) UNIV {} {} (\s. ((), sa))` by
    (seg_tac `fresh_label _ st3 = _` >> simp[fuel_ok_prims]) >>
  `fuel_okS ((=) sb) UNIV {} {exit_lbl} (\s. ((), sj))` by
    (seg_tac `_ sb = ((), sj)` >>
     irule fuel_ok_if >> simp[fuel_ok_return, fuel_ok_emit_inst_jmp]) >>
  `fuel_okS ((=) sj) UNIV {exit_lbl} {} (\s. ((), st_exit))` by
    (seg_tac `new_block _ sj = _` >>
     simp[fuel_ok_new_block]) >>
  `fuel_okS ((=) st_epilogue) UNIV {} {} (\s. ((), st_final))` by
    (seg_tac `compile_constructor_epilogue _ _ _ st_epilogue = _` >>
     simp[fuel_ok_compile_constructor_epilogue]) >>
  (* the exit block onwards: entered at exit_lbl *)
  `fuel_okS ((=) sj) UNIV {exit_lbl} {} (\s. ((), st_final))` by
    (`fuel_okS ((=) sj) UNIV ({exit_lbl} UNION {}) {} (\s. ((), st_epilogue))`
       by (irule fuel_okS_at_seq >> qexistsl_tac [`{}`, `{}`, `st_exit`] >>
           simp[]) >>
     `fuel_okS ((=) sj) UNIV ({exit_lbl} UNION {} UNION {}) {}
        (\s. ((), st_final))`
       by (irule fuel_okS_at_seq >> qexistsl_tac [`{}`, `{}`, `st_epilogue`] >>
           simp[]) >>
     fs[]) >>
  (* the entry up to the jump to exit_lbl *)
  `!a b c. fuel_okS ((=) a) UNIV {} {} (\s. ((), b)) /\
           fuel_okS ((=) b) UNIV {} {exit_lbl} (\s. ((), c)) ==>
           fuel_okS ((=) a) UNIV {} {exit_lbl} (\s. ((), c))` by
    (rpt strip_tac >>
     `fuel_okS ((=) a) UNIV ({} UNION {}) {exit_lbl} (\s. ((), c))`
       suffices_by simp[] >>
     irule fuel_okS_at_seq >> qexistsl_tac [`{}`, `{exit_lbl}`, `b`] >>
     simp[]) >>
  `fuel_okS ((=) sa) UNIV {} {exit_lbl} (\s. ((), sj))` by
    (`fuel_okS ((=) sa) UNIV ({} UNION {}) {exit_lbl} (\s. ((), sj))`
       suffices_by simp[] >>
     irule fuel_okS_at_seq >>
     qexistsl_tac [`{exit_lbl}`, `{exit_lbl}`, `sb`] >> simp[]) >>
  `fuel_okS ((=) st3) UNIV {} {exit_lbl} (\s. ((), sj))` by metis_tac[] >>
  `fuel_okS ((=) st2) UNIV {} {exit_lbl} (\s. ((), sj))` by metis_tac[] >>
  `fuel_okS ((=) st1) UNIV {} {exit_lbl} (\s. ((), sj))` by metis_tac[] >>
  `fuel_okS ((=) st_pay) UNIV {} {exit_lbl} (\s. ((), sj))` by metis_tac[] >>
  `fuel_okS ((=) st0) UNIV {} {exit_lbl} (\s. ((), sj))` by metis_tac[] >>
  `fuel_okS ((=) st0) UNIV ({} UNION {exit_lbl}) {} (\s. ((), st_final))` by
    (irule fuel_okS_at_seq >> qexistsl_tac [`{exit_lbl}`, `{}`, `sj`] >>
     simp[]) >>
  irule fuel_okS_at_mono >> qexistsl_tac [`{}`, `{exit_lbl}`] >> fs[]
QED

(* ===== From the extracted context to the deploy unit's ===== *)

Theorem install_reservation_fns_fuel_stable:
  !n ctx.
    (!fn. MEM fn ctx.ctx_functions ==>
          ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn) ==>
    !fn. MEM fn (install_immutable_reservation n ctx).ctx_functions ==>
         ?Kf. !G. callees_stable G (install_immutable_reservation n ctx) fn ==>
                  fuel_stable (G + Kf) (install_immutable_reservation n ctx) fn
Proof
  simp[install_immutable_reservation_def, fuel_stable_global_reserved,
       callees_stable_global_reserved]
QED

(* ===== Without a constructor ===== *)

(* No internal functions, at the type the deploy lowering uses (the
   descriptor tuple is polymorphic, so a bare [] would not match). *)
Overload deploy_no_ifns =
  ``\tops rpolicy. MAP (set_internal_package_target rpolicy.rpol_target o
       package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops)) []``

Theorem deploy_no_ctor_lowering_trace:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  ?st1 ctx data.
    compile_simple_deploy (LENGTH runtime_bc) (imm_len tops)
      (initial_compile_state "__deploy") = ((), st1) /\
    extract_context_with_internals "__deploy" (deploy_no_ifns tops rpolicy) st1 =
      SOME (ctx, data) /\
    lowering_context_ok (install_immutable_reservation (imm_len tops) ctx) /\
    dunit.cu_context = install_immutable_reservation (imm_len tops) ctx
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def, GSYM imm_len_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def] >>
  pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[compile_generate_deploy_def, comp_ignore_bind_def, comp_bind_def,
      comp_return_def] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem deploy_no_ctor_fns_fuel_stable:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops = (exts, ints, fb, NONE) ==>
  !fn. MEM fn dunit.cu_context.ctx_functions ==>
       ?Kf. !G. callees_stable G dunit.cu_context fn ==>
                fuel_stable (G + Kf) dunit.cu_context fn
Proof
  strip_tac >> drule_all deploy_no_ctor_lowering_trace >> strip_tac >>
  `shape_state st1` by
    (qspecl_then [`F`, `LENGTH runtime_bc`, `imm_len tops`, `[]`, `0`, `[]`,
                  `ARB`, `[]`, `F`, `F`, `0`, `F`, `st1`] mp_tac
       compile_generate_deploy_shape >>
     simp[compile_generate_deploy_def, comp_ignore_bind_def, comp_bind_def,
          comp_return_def]) >>
  qpat_x_assum `dunit.cu_context = _` SUBST1_TAC >>
  simp[install_immutable_reservation_def, fuel_stable_global_reserved,
       callees_stable_global_reserved] >>
  qspecl_then [`compile_simple_deploy (LENGTH runtime_bc) (imm_len tops)`,
                `\st. T`, `\st. T`, `"__deploy"`, `deploy_no_ifns tops rpolicy`,
                `()`, `st1`, `()`,
                `st1`, `ctx`, `data`, `UNIV`] mp_tac extract_context_fuel_stable >>
  impl_tac >- (
    fs[lowering_context_ok_def, install_immutable_reservation_def,
       internal_fn_descriptors_def, compile_internal_fn_bodies_def,
       comp_return_def, next_stable_def] >>
    conj_tac
    >- (irule fuel_okS_of_ok >> simp[fuel_ok_compile_simple_deploy])
    >> fs[listTheory.EVERY_MEM]) >>
  simp[]
QED

(* ===== Uniform fuel for the whole context ===== *)

Theorem run_context_fuel_stable_any:
  !ctx.
    lowering_context_ok ctx /\
    (!fn. MEM fn ctx.ctx_functions ==>
          ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn) ==>
    ?G. !f s. G <= f ==> run_context f ctx s = run_context G ctx s
Proof
  rpt strip_tac >>
  Cases_on `ctx.ctx_entry` >- simp[run_context_def] >>
  rename1 `ctx.ctx_entry = SOME entry` >>
  Cases_on `lookup_function entry ctx.ctx_functions`
  >- simp[run_context_def] >>
  irule run_context_fuel_stable >> metis_tac[]
QED

Theorem run_context_terminates_mono:
  !f f' ctx s.
    terminates (run_context f ctx s) /\ f <= f' ==>
    run_context f' ctx s = run_context f ctx s
Proof
  rpt strip_tac >>
  Cases_on `ctx.ctx_entry` >> fs[run_context_def, terminates_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >>
  fs[run_function_def, terminates_def] >>
  rename1 `lookup_function nm _ = SOME efn` >>
  Cases_on `fn_entry_label efn` >> fs[terminates_def] >>
  irule (cj 3 fuel_mono) >> conj_tac
  >- (rpt strip_tac >> fs[]) >>
  qexists_tac `f` >> simp[]
QED

(* One fuel for every start state: whatever terminates at some fuel
   terminates at F. *)
Theorem run_context_uniform_fuel:
  !ctx.
    lowering_context_ok ctx /\
    (!fn. MEM fn ctx.ctx_functions ==>
          ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn) ==>
    ?fuel. !s f. terminates (run_context f ctx s) ==>
                 terminates (run_context fuel ctx s)
Proof
  rpt strip_tac >> drule_all run_context_fuel_stable_any >> strip_tac >>
  qexists_tac `G` >> rpt strip_tac >>
  Cases_on `f <= G`
  >- metis_tac[run_context_terminates_mono] >>
  `G <= f` by decide_tac >> metis_tac[]
QED

Theorem deploy_unit_context_ok:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit ==>
  lowering_context_ok dunit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  Cases_on `r2`
  >- (drule_all deploy_no_ctor_lowering_trace >> strip_tac >> simp[]) >>
  drule_all deploy_ctor_lowering_trace >> strip_tac >> simp[]
QED

(* ===== Constructor argument registration ===== *)

Theorem fuel_ok_decode_dload[local]:
  !cenv args off hi adj Wv E.
    fuel_ok Wv {} E (compile_decode_args cenv args off DLOAD hi adj)
Proof
  rpt gen_tac >> irule fuel_ok_compile_decode_args >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_register_constructor_args:
  !args cenv off sz Wv E.
    fuel_ok Wv {} E (compile_register_constructor_args cenv args off sz)
Proof
  Induct >- simp[compile_register_constructor_args_def, fuel_ok_return] >>
  PairCases >> rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp_tac std_ss [option_case_def] >>
  TRY (rename1 `FLOOKUP _ _ = SOME loc` >>
       Cases_on `var_location_memory_size loc` >>
       simp_tac std_ss [option_case_def]) >>
  fuel_auto [fuel_ok_return, fuel_ok_compile_alloc_buffer, fuel_ok_decode_dload]
QED

(* The registered arguments' buffers are allocated by the end. *)
Theorem compile_register_constructor_args_ptrs:
  !args cenv off sz st c st'.
    compile_register_constructor_args cenv args off sz st = (c, st') /\
    cenv_ptrs_below st.cs_next_var cenv ==>
    cenv_ptrs_below st'.cs_next_var c
Proof
  Induct
  >- (rw[compile_register_constructor_args_def, comp_return_def] >> fs[]) >>
  PairCases >> rpt gen_tac >>
  simp[Once compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_alloc_buffer _ st = (buf, s1)` >>
  rename1 `compile_decode_args _ _ _ _ _ _ s1 = (u, s2)` >>
  drule compile_alloc_buffer_var >> strip_tac >>
  `s1.cs_next_var <= s2.cs_next_var` by
    metis_tac[fuel_ok_next, fuel_ok_decode_dload] >>
  first_x_assum drule >> impl_tac
  >- (match_mp_tac cenv_ptrs_below_update >>
      qexists_tac `st.cs_next_var` >> rpt conj_tac >> simp[] >>
      metis_tac[var_below_le]) >>
  simp[]
QED

(* ===== The packaged environments ===== *)

(* The constructor's packaged locals are its parameters, at fixed memory
   locations: no local is a pointer variable. *)
Theorem package_constructor_cenv_ptrs_below:
  !tops ut nkm cf target n cenv0 pos pay nr nkey ut' body ret.
    set_constructor_package_target target (package_constructor tops ut nkm cf) =
      (cenv0, pos, pay, nr, nkey, ut', body, ret) ==>
    cenv_ptrs_below n cenv0
Proof
  rpt gen_tac >> PairCases_on `cf` >>
  simp[package_constructor_def, set_constructor_package_target_def,
       update_cenv_nonreentrant_def, build_compile_env_def,
       cenv_ptrs_below_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  drule_all allocate_args_vars >> simp[]
QED

(* fragFuelUnit's package_internal_fn_ctor_exit, for any constructor flag
   and immutables length. *)
Theorem package_internal_fn_ctor_exit_any[local]:
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

(* fragFuelUnit's package_internal_fns_fuel, for any constructor flag and
   immutables length: the deploy unit's internal functions. *)
Theorem package_internal_fns_fuel_any:
  !tops ut nkm ic il target srcs.
    EVERY (\(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
             is_view, is_ctor, imm_len, body, ret_type).
             ?Wv. fuel_okS (\st. T) Wv {} {}
                    (compile_internal_function cenv params has_ret_buf is_nr
                       nkey use_trans is_view is_ctor imm_len body ret_type))
      (MAP (set_internal_package_target target o
            package_internal_fn tops ut nkm ic il) srcs)
Proof
  rpt gen_tac >> simp[EVERY_MAP, listTheory.EVERY_MEM] >>
  qx_gen_tac `src` >> strip_tac >>
  qspecl_then [`tops`, `ut`, `nkm`, `ic`, `il`, `src`,
               `target`] mp_tac package_internal_fn_ctor_exit_any >>
  qspecl_then [`tops`, `ut`, `nkm`, `ic`, `il`, `src`,
               `target`] assume_tac package_internal_fn_cenv_ptrs_below >>
  Cases_on `set_internal_package_target target
              (package_internal_fn tops ut nkm ic il src)` >>
  PairCases_on `r` >> fs[] >> rpt strip_tac >>
  qexists_tac `UNIV` >>
  `(\st:compile_state. cenv_ptrs_below st.cs_next_var r0) = (\st. T)` by
    simp[FUN_EQ_THM] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule fuel_okS_compile_internal_function >> simp[] >>
  rpt strip_tac >> irule (CONJUNCT2 fuel_okS_compile_stmt) >> simp[]
QED

(* ===== The deploy unit with a constructor ===== *)

(* Local in ctorDeployLoweringCode. *)
Theorem ctor_code_cond_not[local]:
  !p a b. (if ~p then a else b) = (if p then b else a)
Proof
  Cases >> simp[]
QED

Theorem deploy_ctor_fns_fuel_stable:
  !tops rpolicy runtime_bc dunit am tx exts ints fb cf.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    deploy_source_ok tops am tx /\
    classify_functions tops = (exts, ints, fb, SOME cf) ==>
    !fn. MEM fn dunit.cu_context.ctx_functions ==>
         ?Kf. !G. callees_stable G dunit.cu_context fn ==>
                  fuel_stable (G + Kf) dunit.cu_context fn
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_lowering_trace >> strip_tac >>
  drule_all deploy_constructor_package_shape >> strip_tac >>
  drule_all deploy_constructor_package_not_view >> strip_tac >>
  qpat_x_assum `cenv0.ce_nonreentrant = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, pairTheory.SND])) >>
  (* the four segments deploy_ctor_entry_fuel takes *)
  `!n. cenv_ptrs_below n cenv0` by
    metis_tac[package_constructor_cenv_ptrs_below] >>
  `cenv_ptrs_below st1.cs_next_var
     (cenv0 with ce_imm_alloca :=
        (if imm_len tops > 0 then SOME imm else NONE))` by
    (fs[cenv_ptrs_below_def] >> metis_tac[]) >>
  `cenv_ptrs_below st2.cs_next_var cenv1` by
    metis_tac[compile_register_constructor_args_ptrs] >>
  `fuel_okS ((=) st1) UNIV {} {} (\s. ((), st2))` by
    (seg_tac `compile_register_constructor_args _ _ _ _ st1 = _` >>
     simp[fuel_ok_compile_register_constructor_args]) >>
  `!k t. fuel_ok UNIV {} {}
           (if nr then compile_nonreentrant_lock k t F else comp_return ()) /\
         fuel_ok UNIV {} {}
           (if nr then compile_nonreentrant_unlock k t F else comp_return ())` by
    (Cases_on `nr` >> simp[fuel_ok_return, fuel_ok_context_storage]) >>
  `fuel_okS ((=) st2) UNIV {} {} (\s. ((), st3))` by
    (seg_tac `_ st2 = ((), st3)` >> simp[]) >>
  `fuel_okS ((=) st_exit) UNIV {} {} (\s. ((), st_epilogue))` by
    (seg_tac `_ st_exit = ((), st_epilogue)` >> simp[]) >>
  `st2.cs_next_var <= st3.cs_next_var` by
    metis_tac[fuel_ok_next] >>
  `sa.cs_next_var = st3.cs_next_var` by
    (qpat_x_assum `fresh_label _ st3 = _` mp_tac >>
     rw[fresh_label_def] >> simp[]) >>
  `fuel_okS ((=) sa) UNIV {} {exit_lbl} (\s. ((), sb))` by
    (irule (INST_TYPE [alpha |-> ``:unit``] fuel_okS_at) >>
     qexistsl_tac [`\st. cenv_ptrs_below st.cs_next_var
                     (cenv1 with ce_ctor_exit_label := SOME exit_lbl)`,
                   `UNIV`,
                   `compile_stmts (cenv1 with ce_ctor_exit_label := SOME exit_lbl)
                      NoLoop NoneT body'`, `()`] >>
     simp[] >> conj_tac
     >- (fs[cenv_ptrs_below_def] >> metis_tac[var_below_le]) >>
     irule (CONJUNCT2 fuel_okS_compile_stmt) >>
     simp[cenv_ptrs_in_def, stmt_exits_in_def]) >>
  `fuel_okS ((=) (initial_compile_state "__deploy")) UNIV {} {}
     (\s. ((), st_final))` by
    (qspecl_then [`pay`, `imm_len tops`, `LENGTH runtime_bc`, `imm`,
                  `exit_lbl`, `old_bb`, `initial_compile_state "__deploy"`,
                  `st_pay`, `st1`, `st2`, `st3`, `sa`, `sb`, `sj`, `st_exit`,
                  `st_epilogue`, `st_final`] mp_tac deploy_ctor_entry_fuel >>
     simp[]) >>
  (* the shape facts extract_context_fuel_stable takes *)
  `(do (if ~pay then
           do cv <- emit_op CALLVALUE []; v <- emit_op ISZERO [cv];
              emit_void ASSERT [v] od else return ());
        imm <- (if imm_len tops > 0 then
                  do p <- compile_fixed_region_with_id (imm_len tops);
                     return (SND p).buf_operand od else return (Lit 0w));
        ce <- compile_register_constructor_args
          (cenv0 with ce_imm_alloca :=
            (if imm_len tops > 0 then SOME imm else NONE)) pos_args 0 0;
        (if nr then compile_nonreentrant_lock nkey ut F else return ());
        lbl <- fresh_label "ctor_exit";
        compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT body';
        cs <- comp_get;
        (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
        new_block lbl;
        (if nr then compile_nonreentrant_unlock nkey ut F else return ());
        compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm od)
      (initial_compile_state "__deploy") = ((),st_final)` by
    (rewrite_tac[ctor_code_cond_not] >>
     simp[comp_ignore_bind_def, comp_bind_def, comp_get_def]) >>
  drule_all ctor_code_prefix_certificates >> strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  qmatch_asmsub_abbrev_tac `compile_internal_fn_bodies ifns st_final` >>
  `ifns = MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops))
      (FST (SND (classify_functions tops)))` by simp[Abbr `ifns`] >>
  drule_all deploy_internal_package_certificates >> strip_tac >>
  qpat_x_assum `ifns = _` kall_tac >>
  `EVERY (\d. ~compiler_label (FST d) /\
              ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks st_final)))
     (internal_fn_descriptors ifns)` by
    (irule listTheory.EVERY_MONOTONIC >>
     qexists_tac `\d. internal_label_ok (FST d)` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     gen_tac >> BETA_TAC >> strip_tac >>
     irule deploy_internal_label_separate >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions` by
    (qpat_x_assum `lowering_context_ok _` mp_tac >>
     simp_tac (srw_ss()) [lowering_context_ok_def,
                          install_immutable_reservation_def] >>
     strip_tac >> irule listTheory.EVERY_MONOTONIC >>
     qexists_tac `\fn. ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  qunabbrev_tac `ifns` >>
  qpat_x_assum `dunit = _` SUBST1_TAC >>
  simp_tac (srw_ss()) [install_immutable_reservation_def,
                       fuel_stable_global_reserved,
                       callees_stable_global_reserved] >>
  qspecl_then [`\s. ((), st_final)`,
               `(=) (initial_compile_state "__deploy")`, `\st. T`,
               `"__deploy"`,
               `MAP (set_internal_package_target rpolicy.rpol_target o
                     package_internal_fn tops T (K global_nonreentrant_slot) T
                       (imm_len tops)) ints`,
               `()`, `st_final`, `()`, `post`,
               `ctx`, `data`, `UNIV`] mp_tac extract_context_fuel_stable >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    simp[next_stable_def, package_internal_fns_fuel_any]) >>
  simp[]
QED

(* Every function of a lowered deploy unit is stable once its callees are. *)
Theorem deploy_unit_fns_fuel_stable:
  !tops rpolicy runtime_bc dunit am tx.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    deploy_source_ok tops am tx ==>
    !fn. MEM fn dunit.cu_context.ctx_functions ==>
         ?Kf. !G. callees_stable G dunit.cu_context fn ==>
                  fuel_stable (G + Kf) dunit.cu_context fn
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  Cases_on `r2` >>
  metis_tac[GEN_ALL deploy_no_ctor_fns_fuel_stable, deploy_ctor_fns_fuel_stable]
QED
