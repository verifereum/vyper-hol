(* CREATE opcodes can only come from source create calls, through the expression generator. *)
Theory loweringRuntimeNoCreate
Ancestors
  loweringRuntimeOpcodes loweringGroupedOpcodes loweringCreatePackages
  loweringPackageInsts ctorCallFreeExpr ctorCallFreeStmt
  loweringShapeSource loweringCreateSource loweringShapeProps loweringShapeDefs supportedStmtTraverse supportedExprTraverse
  supportedDecls compileVyper vyperCompiler context unitShapeDefs venomInst list pair

Theorem avoids_create_and_short_builtin[local]:
  (!e. ~supported_expr_exists create_or_short_builtin_root e ==>
       ~supported_expr_exists expr_create_root e /\
       ~supported_expr_exists expr_short_builtin_root e) /\
  (!es. ~supported_exprs_exists create_or_short_builtin_root es ==>
        ~supported_exprs_exists expr_create_root es /\
        ~supported_exprs_exists expr_short_builtin_root es) /\
  (!ss. ~supported_stmts_expr_exists create_or_short_builtin_root ss ==>
        ~supported_stmts_expr_exists expr_create_root ss /\
        ~supported_stmts_expr_exists expr_short_builtin_root ss)
Proof
  metis_tac[supported_expr_exists_mono, supported_stmt_expr_exists_mono,
            create_or_short_builtin_root_def]
QED

Theorem compile_runtime_stmts_no_create:
  EVERY (\nd. ~supported_exprs_exists create_or_short_builtin_root (SND nd))
    ce.ce_func_defaults /\
  ~supported_stmts_expr_exists create_or_short_builtin_root ss /\
  EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_stmts ce lc ty ss st)))
Proof
  strip_tac >>
  `EVERY (\nd. ~supported_exprs_exists expr_create_root (SND nd) /\
               ~supported_exprs_exists expr_short_builtin_root (SND nd))
     ce.ce_func_defaults` by
    (fs[EVERY_MEM] >> metis_tac[avoids_create_and_short_builtin]) >>
  `~supported_stmts_expr_exists expr_create_root ss /\
   ~supported_stmts_expr_exists expr_short_builtin_root ss` by
    metis_tac[avoids_create_and_short_builtin] >>
  irule (SIMP_RULE (srw_ss()) [] (Q.INST
    [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`,
     `R` |-> `expr_create_root`, `extra_root` |-> `expr_short_builtin_root`]
    compile_stmts_opcode_every_from_expr)) >>
  simp[] >> rpt strip_tac >>
  mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`,
                  `R` |-> `expr_create_root`] compile_expr_opcode_every) >>
  simp[] >> metis_tac[]
QED

Theorem compile_runtime_expr_no_create[local]:
  package_body_avoids create_or_short_builtin_root ce [] /\
  ~supported_expr_exists create_or_short_builtin_root e ==>
  EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_expr ce ty e st)))
Proof
  rw[package_body_avoids_def, supported_stmt_expr_exists_def] >>
  `EVERY (\nd. ~supported_exprs_exists expr_create_root (SND nd) /\
               ~supported_exprs_exists expr_short_builtin_root (SND nd))
     ce.ce_func_defaults` by
     (fs[EVERY_MEM] >> metis_tac[avoids_create_and_short_builtin]) >>
  `~supported_expr_exists expr_create_root e /\
   ~supported_expr_exists expr_short_builtin_root e` by
     metis_tac[avoids_create_and_short_builtin] >>
  mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`,
                  `R` |-> `expr_create_root`] compile_expr_opcode_every) >>
  simp[] >> metis_tac[]
QED

Theorem run_lowering_no_create:
  run_lowering sels exts ints fb rp buckets metadata dense info entry = SOME unit ==>
  EVERY (external_package_avoids create_or_short_builtin_root) exts /\
  EVERY (internal_package_avoids create_or_short_builtin_root) ints /\
  fallback_package_avoids create_or_short_builtin_root fb ==>
  EVERY (\fn. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (fn_insts fn)) unit.cu_context.ctx_functions
Proof
  ntac 2 strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def, AllCaseEqs()] >> rpt strip_tac >>
  `rp.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >> gvs[] >>
  `!st. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_generate_runtime sels exts ints fb Linear
        buckets metadata dense info st)))` by
    (mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`,
                     `root` |-> `create_or_short_builtin_root`]
      opcode_every_generate_runtime_linear) >>
     simp[compile_runtime_stmts_no_create]) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  drule extract_context_with_internals_every >> disch_then irule >>
  metis_tac[every_state_insts_initial, SND]
QED

Theorem run_grouped_lowering_no_create[local]:
  run_grouped_lowering groups ints fb rp entry = SOME unit ==>
  EVERY (external_group_avoids create_or_short_builtin_root) groups /\
  EVERY (internal_package_avoids create_or_short_builtin_root) ints /\
  fallback_package_avoids create_or_short_builtin_root fb ==>
  EVERY (\fn. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (fn_insts fn)) unit.cu_context.ctx_functions
Proof
  ntac 2 strip_tac >>
  `!st. EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_generate_grouped_runtime groups ints fb st)))` by
    (mp_tac (Q.INST [`P` |-> `\opc. opc <> CREATE /\ opc <> CREATE2`,
                     `root` |-> `create_or_short_builtin_root`]
       opcode_every_generate_grouped_runtime) >>
     simp[package_body_avoids_def, compile_runtime_expr_no_create,
          compile_runtime_stmts_no_create]) >>
  qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` mp_tac >>
  simp[run_grouped_lowering_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `extract_context_with_internals entry ints st1` >- fs[] >>
  rename1 `extract_context_with_internals _ _ _ = SOME p` >>
  PairCases_on `p` >> gvs[AllCaseEqs()] >>
  drule extract_context_with_internals_every >> disch_then irule >>
  metis_tac[every_state_insts_initial, SND]
QED

Theorem lower_vyper_runtime_unit_no_create:
  !tops rp unit. runtime_bodies_avoid_create tops /\
    lower_vyper_runtime_unit tops rp = SOME unit ==>
    !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
      inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts, ints, fb, ctor)` >>
  `!x. MEM x exts ==> external_package_avoids create_or_short_builtin_root
    (set_external_package_target rp.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot) x))` by
    (rpt strip_tac >> irule package_external_avoids_create >> gvs[]) >>
  `!x. MEM x exts ==> external_group_avoids create_or_short_builtin_root
    (package_external_group tops rp.rpol_target T (K global_nonreentrant_slot) x)` by
    (rpt strip_tac >> irule package_external_group_avoids_create >> gvs[]) >>
  `!x. MEM x (order_internals (runtime_internal_order tops ints) ints) ==>
    internal_package_avoids create_or_short_builtin_root
      (set_internal_package_target rp.rpol_target
        (package_internal_fn tops T (K global_nonreentrant_slot) F 0 x))` by
    (rpt strip_tac >> irule package_internal_avoids_create >> fs[] >>
     metis_tac[]) >>
  `fallback_package_avoids create_or_short_builtin_root
     (set_fallback_package_target rp.rpol_target
       (package_fallback_fn tops T (K global_nonreentrant_slot) fb))` by
    (`fb = FST (SND (SND (classify_functions tops)))` by fs[] >>
     pop_assum SUBST1_TAC >> irule package_fallback_avoids_create >> simp[]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, AllCaseEqs()] >> strip_tac
  >- (drule run_grouped_lowering_no_create >>
      simp[EVERY_MAP, EVERY_MEM] >> metis_tac[]) >>
  drule run_lowering_no_create >>
  simp[EVERY_MAP, EVERY_MEM] >> metis_tac[]
QED
