Theory readonlyInvokeCopyFwdExecutionFamily
Ancestors
  readonlyInvokeCopyFwdExecutionDispatch readonlyInvokeCopyFwdExecutionAssembly
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdDefs invokeCopyFwdCommonDefs
  reachableFnSim passSimulationDefs ptrDiscipline contextCodegenRel
  o1PassContract unitShapeDefs venomWf venomInst list finite_map pair

Theorem ricf_execution_family:
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ricf_full_alloca_copies C.ctx_functions /\
  EVERY ricf_no_derived_mutable_sibling C.ctx_functions /\
  EVERY ricf_src_alloca C.ctx_functions /\
  EVERY ricf_param_order_ok C.ctx_functions /\
  ptr_discipline lo C vs /\ mem_inv raw_mem_ok C vs /\
  vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\
  ~ctx_has_dalloca C /\ taint_within D C vs /\ dead_wf D /\
  R = (\(a,U,B0,E0,outer_history,outer_certificates,sites,maps,targets).
    ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets) /\
  Rret = (\(a,U,B0,E0,outer_history,outer_certificates,sites,maps,targets).
    ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets) /\
  (!f. MEM f C.ctx_functions ==>
    ricf_logged_function_trace
      (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) f)
      f (log_of f) (mid_of f) /\ ricf_function_edit f (mid_of f) /\
    ?f'. lookup_function f.fn_name Ct.ctx_functions = SOME f' /\
      fn_entry_label f' = fn_entry_label f) /\
  (!fn fn'. MEM fn C.ctx_functions /\
    lookup_function fn.fn_name Ct.ctx_functions = SOME fn' ==>
    fn' = if (mid_of fn).fn_blocks <> fn.fn_blocks
          then clear_nops_function (mid_of fn) else mid_of fn) ==>
  !n idx. fn_sim_below D vs C Ct (R idx) (Rret idx) n
Proof
  strip_tac >>
  mp_tac (SPEC_ALL ricf_execution_family_from_raw_blocks) >>
  (impl_tac
   >- (simp[] >> rpt gen_tac >> strip_tac >> PairCases_on `idx` >> gvs[] >>
       `!a1 U1 B1 E1 history1 certificates1 sites1 maps1 targets1.
         fn_sim_below D vs C Ct
           (ricf_execution_boundary vs C mid_of log_of D a1 U1 B1 E1 history1 certificates1
             sites1 maps1 targets1)
           (ricf_execution_return vs C Ct mid_of log_of D a1 U1 B1 E1 history1 certificates1
             sites1 maps1 targets1) (SUC k)` by
         (rpt gen_tac >> fs[pairTheory.FORALL_PROD] >> metis_tac[]) >>
       `wf_function fn /\ opaque_use_ok fn /\ ricf_function_edit fn (mid_of fn)` by
         (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
       irule (Q.INST [`lo` |-> `lo`] ricf_execution_run_block_actual) >>
       rpt conj_tac
       >~ [`?lo0. ptr_discipline lo0 C vs`] >- metis_tac[]
       >~ [`?G0 tn0. ricf_execution_boundary _ _ _ _ _ _ _ _
              _ _ _ _ _ _ _ _ G0 tn0 _ _ _`] >- metis_tac[] >>
       simp[] >> rpt gen_tac >> strip_tac
       >- (drule_all ricf_execution_point_next >> simp[]) >>
       drule_all ricf_execution_terminal >> simp[])) >> simp[]
QED
