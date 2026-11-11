(* Callee entry control follows from the lowered unit's shape interface. *)
Theory bodyIntCallPackageControl
Ancestors
  bodyIntCallEntryPhi bodySim loweringShapeProps loweringShapeSource
  ctorDeployShape supportedProgram supportedNames unitShapeDefs
  venomExecProps venomInst list

Theorem body_inv_function_entry_label:
  body_inv tops ctx cenv cx /\
  lookup_function label ctx.ctx_functions = SOME func ==>
  func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = label
Proof
  strip_tac >>
  `?unit. ctx = unit.cu_context /\ o1_source_unit_ok unit` by
    (fs[body_inv_def] >>
     Cases_on `cx.in_deploy` >> gvs[]
     >- (drule_all lower_vyper_deploy_unit_source_unit_ok >> metis_tac[]) >>
     `runtime_bodies_shape_ok tops` by
       metis_tac[supported_program_runtime_bodies_shape_ok] >>
     `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
        (FST (SND (classify_functions tops))))` by
       (irule supported_names_internal_names_distinct >>
        fs[supported_program_def, supported_declaration_names_def]) >>
     drule_all lower_vyper_runtime_unit_source_unit_ok_shape >> metis_tac[]) >>
  drule lookup_function_MEM >> strip_tac >>
  drule vyperCompilerTheory.lookup_function_result_name >> strip_tac >>
  gvs[o1_source_unit_ok_def, unit_shape_ok_def, EVERY_MEM] >>
  qpat_x_assum `!e. MEM e _ ==> fn_shape_ok e` drule >>
  Cases_on `func.fn_blocks` >>
  simp[fn_shape_ok_def, fn_entry_label_def, entry_block_def]
QED

Theorem internal_entry_counted_resources:
  compile_internal_function_entry ce params has_rb ctor ilen rt st0 =
    ((ce2,rpc,imm),st1) /\ st0.cs_current_insts = [] /\
  st0.cs_current_bb = (HD func.fn_blocks).bb_label /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME setup /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) ==>
  ?u mr.
    run_inst_seq (emitted_insts st0 st1) setup = OK u /\
    gas_path ctx func setup
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st0 st1)))
      (OK (u with vs_inst_idx := LENGTH st1.cs_current_insts)) /\
    ~u.vs_halted /\ u.vs_current_bb = st1.cs_current_bb /\
    mat_inv func ce2 env st1 u caller.vs_alloca_next mr /\
    mat_frame st0 setup u /\
    (!n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\
        FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL ((if has_rb then 1 else 0) + i) args))
Proof
  strip_tac >>
  drule_all bodyIntCallActualEntryResourceTheory.internal_entry_resource_run >>
  strip_tac >> drule intCallCalleeTheory.setup_callee_frontier >> strip_tac >>
  `setup.vs_current_bb = st0.cs_current_bb /\
   setup.vs_inst_idx = LENGTH st0.cs_current_insts` by gvs[] >>
  drule_all bodyIntCallActualEntryFieldsTheory.internal_entry_counted_landing >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> qexists_tac `mr` >>
  simp[arithmeticTheory.ADD_COMM]
QED
