Theory bodyPtrStructLitOwnershipUnits
Ancestors bodyPtrStructLitOwnershipRunClosure
  bodyPtrStructLitOwnershipSelectedPackages compileVyper vyperCompiler
  venomInst loweringShapeProps list pair

Theorem structlit_runtime_unit_ownership:
  supported_program tops /\ lower_vyper_runtime_unit tops rp = SOME u /\
  lookup_function name u.cu_context.ctx_functions = SOME func ==>
  !i j x. MEM i (fn_insts func) /\ MEM j (fn_insts func) /\
    i.inst_opcode = ALLOCA /\ MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >> strip_tac >>
  drule_all structlit_selected_runtime_packages >>
  disch_then (qspecl_then [`F`, `assign_nkeys tops 0`, `rp.rpol_target`]
    strip_assume_tac) >>
  metis_tac[structlit_run_lowering_ownership]
QED

Theorem structlit_deploy_unit_ownership:
  supported_program tops /\ lower_vyper_deploy_unit tops rp bytes = SOME u /\
  lookup_function name u.cu_context.ctx_functions = SOME func ==>
  !i j x. MEM i (fn_insts func) /\ MEM j (fn_insts func) /\
    i.inst_opcode = ALLOCA /\ MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >>
  drule_all structlit_selected_deploy_packages >>
  disch_then (qspecl_then [`F`, `assign_nkeys tops 0`, `rp.rpol_target`,
    `compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops`]
    assume_tac) >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >>
  Cases_on `ctor`
  >- (simp[set_constructor_package_target_def] >> strip_tac >>
      metis_tac[structlit_run_deploy_lowering_ownership]) >>
  gvs[] >>
  Cases_on `set_constructor_package_target rp.rpol_target
    (package_constructor tops F (assign_nkeys tops 0) x)` >>
  PairCases_on `r` >> gvs[] >> strip_tac >>
  drule_at (Pat `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    structlit_run_deploy_lowering_ownership >>
  simp[] >> metis_tac[]
QED
