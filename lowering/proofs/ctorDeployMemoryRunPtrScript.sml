(* The raw deployment unit's run is pointer-safe, with its taint confined to
 * deploy_dead's bytes and its accesses below imm_len exempt (the immutables
 * fixed region, addressed by literal offsets).  The deploy twin of
 * lower_vyper_runtime_unit_run_ptr_safe_composed, at PG = [] (__deploy has
 * no parameters).  Composed like deploy_unit_run_mem_safe: without a
 * constructor (RunPtrNoCtor); a source that fails before the body
 * (RunPtrPrefix); otherwise the prefix reaches the body start with
 * deploy_ptr_inv (RunPtrEntry), and the body (RunPtrBody) either exits, a
 * return going through the exit block (RunPtrFrameRet), or falls off its
 * end into it (RunPtrFallthrough).
 * TOP-LEVEL: deploy_unit_run_ptr_safe.
 *)
Theory ctorDeployMemoryRunPtr
Ancestors
  ctorDeployDefs gasSummary ptrSafeRun ptrDiscipline venomInst
  ctorDeployLoweringDefs ctorDeployLoweringCode ctorDeployLoweringEntry
  ctorDeployLoweringFrame e2eDeployDefs
  ctorDeployMemoryRunPtrDefs ctorDeployMemoryRunPtrNoCtor fragExecPtr
  ctorDeployMemoryRunPtrPrefix ctorDeployMemoryRunPtrEntry
  ctorDeployMemoryRunPtrBody ctorDeployMemoryRunPtrFrameRet
  ctorDeployMemoryRunPtrFallthrough
  loweringPtrCorrect fragExec stmtSimDefs bodySim compileEnv

val _ = Parse.hide "body";

Theorem deploy_unit_run_ptr_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. ptr_safe_blocks (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel dunit.cu_context fn
             [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt strip_tac >>
  `?exts ints fb cfo. classify_functions tops = (exts, ints, fb, cfo)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  Cases_on `cfo`
  >- (drule_all deploy_no_ctor_run_ptr_safe >> simp[]) >>
  drule_all deploy_ctor_code_exists >> strip_tac >>
  reverse (Cases_on `?mut nr' body' am_c es0.
                       deploy_ctor_start tops am tx (mut, nr', body', am_c, es0)`)
  >- (fs[] >> drule_all deploy_ctor_prefix_fail_run_ptr_safe >> simp[]) >>
  pop_assum strip_assume_tac >>
  `nr' = nr /\ body' = body` by
    (drule_all deploy_ctor_entry_reaches_body >> strip_tac >> simp[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  drule_all deploy_ctor_entry_run_ptr >> strip_tac >>
  `call_outcomes_ok am tx (MAP SND (call_trace es))` by
    fs[deploy_state_rel_def] >>
  drule_all deploy_ctor_body_frame >> strip_tac >>
  `~ctx_has_dalloca dunit.cu_context` by
    (drule_all ctorDeployShapeTheory.deploy_unit_shape_ok >> strip_tac >>
     simp[o1PipelineCorrectTheory.o1_source_unit_ok_no_dalloca]) >>
  `st_exit.cs_current_insts = [] /\
   (if nr then compile_nonreentrant_unlock nkey ut F else comp_return ())
     st_exit = ((), st_epilogue) /\
   compile_constructor_epilogue (LENGTH runtime_bc) (imm_len tops) imm
     st_epilogue = ((), st_final) /\
   fn_has_code st_exit st_final func /\ fn_inst_ids_distinct func` by
    (qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
     simp[deploy_ctor_code_def, new_block_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `(!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _) ==> _` irule >>
  qspecl_then [`policy`, `tops`, `deploy_bc`, `runtime_bc`, `rpolicy`, `dunit`,
               `dout`, `prog`, `cplan`, `am`, `tx`, `es`, `vs`, `body`, `cenv`,
               `nr`, `nkey`, `ut`, `imm`, `exit_lbl`, `sa`, `sb`, `sj`,
               `st_exit`, `st_epilogue`, `st_final`, `func`, `mut`, `am_c`,
               `es0`, `s0`, `G0`, `tn0`] mp_tac deploy_ctor_body_ptr >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      irule constructor_exit_run_ptr >> simp[] >>
      qexistsl_tac [`body_cenv`, `cenv`, `ee`, `imm`, `nkey`, `nr`, `st_epilogue`,
                    `st_exit`, `st_final`, `ut`] >>
      simp[]) >>
  strip_tac
  >- ((* the body falls off its end *)
      qspecl_then [`tops`, `rpolicy`, `runtime_bc`, `am`, `tx`, `dunit`, `body`,
                   `cenv`, `nr`, `nkey`, `ut`, `imm`, `exit_lbl`, `sa`, `sb`,
                   `sj`, `st_exit`, `st_epilogue`, `st_final`, `func`, `cenv'`,
                   `ee`, `s`, `G`, `tn`] mp_tac deploy_ctor_fallthrough_ptr >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum `!fuel r. run_from _ _ _ s = r /\ _ ==> _`
        (qspecl_then [`fuel`, `Halt final`] mp_tac) >>
      simp[] >> strip_tac >> gen_tac >>
      irule ptr_safe_run_all_fuel >> simp[] >>
      qexists_tac `fuel'` >> simp[]) >>
  (* the body exits *)
  gen_tac >> irule ptr_safe_run_all_fuel >> simp[] >>
  qexists_tac `fuel` >> simp[] >> metis_tac[exit_result_not_error]
QED
