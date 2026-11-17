(* CREATE opcodes can only come from source create calls, outside the gate. *)
Theory loweringRuntimeNoCreate
Ancestors
  loweringRuntimeOpcodes loweringPackageInsts ctorCallFreeExpr ctorCallFreeStmt
  loweringShapeProps loweringShapeDefs supportedStmtTraverse supportedExprTraverse
  supportedDecls compileVyper vyperCompiler context unitShapeDefs venomInst list pair

Theorem compile_runtime_stmts_no_create:
  ~supported_stmts_expr_exists expr_shape_root ss /\
  EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmts ce lc ty ss st)))
Proof
  `!ce ty e st. ~supported_expr_exists expr_shape_root e ==>
    EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_expr ce ty e st)))` by
    (mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`,
                    `R` |-> `expr_shape_root`] compile_expr_opcode_every) >> simp[]) >>
  mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`,
                  `R` |-> `expr_shape_root`] compile_stmts_opcode_every_from_expr) >>
  simp[]
QED

Theorem run_lowering_no_create:
  run_lowering sels exts ints fb rp buckets metadata dense info entry = SOME unit ==>
  EVERY external_fn_shape_ok exts /\ EVERY internal_fn_shape_ok ints /\
  fallback_shape_ok fb ==>
  EVERY (\fn. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (fn_insts fn)) unit.cu_context.ctx_functions
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def, AllCaseEqs()] >> rpt strip_tac >>
  `rp.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >> gvs[] >>
  `!st. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_generate_runtime sels exts ints fb Linear
        buckets metadata dense info st)))` by
    (mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`]
      opcode_every_generate_runtime_linear) >> simp[compile_runtime_stmts_no_create]) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  drule extract_context_with_internals_every >> disch_then irule >>
  metis_tac[every_state_insts_initial, SND]
QED

Theorem lower_vyper_runtime_unit_no_create:
  !tops rp unit. supported_program tops /\
    lower_vyper_runtime_unit tops rp = SOME unit ==>
    !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
      inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
  `~EXISTS external_has_defaults (FST (classify_functions tops))` by
    metis_tac[supported_program_no_external_defaults] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts, ints, fb, ctor)` >>
  `!x. MEM x exts ==> external_fn_shape_ok
    (set_external_package_target rp.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot) x))` by
    (rpt strip_tac >> irule package_external_fn_shape_ok >> gs[]) >>
  `!x. MEM x ints ==> internal_fn_shape_ok
    (set_internal_package_target rp.rpol_target
      (package_internal_fn tops T (K global_nonreentrant_slot) F 0 x))` by
    (rpt strip_tac >> irule package_internal_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok (set_fallback_package_target rp.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot) fb))` by
    (qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`, `rp.rpol_target`]
      mp_tac package_fallback_fn_shape_ok >> gs[]) >>
  `~EXISTS external_has_defaults exts` by fs[] >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  drule_all lower_vyper_runtime_unit_no_external_defaults >>
  disch_then (fn eq => REWRITE_TAC [eq]) >>
  simp[] >> rpt strip_tac >>
  drule run_lowering_no_create >>
  simp[EVERY_MAP, EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED
