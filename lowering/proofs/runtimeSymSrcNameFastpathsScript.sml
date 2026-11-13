Theory runtimeSymSrcNameFastpaths
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcGeneratorContracts exprLowering
  compileEnv context list loweringShapeDefs

Theorem runtime_sym_addmod_names:
  runtime_sym_context_clauses /\ runtime_sym_math_clauses ==>
  !ce rt aty a bty b mty m s v s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_addmod_names ce rt aty a bty b mty m s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >>
  qpat_x_assum `runtime_sym_context_clauses`
    (assume_tac o cj 1 o SRULE [runtime_sym_context_clauses_def]) >>
  qpat_x_assum `runtime_sym_math_clauses`
    (assume_tac o cj 1 o SRULE [runtime_sym_math_clauses_def]) >>
  rpt gen_tac >> simp[compile_addmod_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  ntac 3
    (drule_all runtime_sym_compile_name >> strip_tac >>
     qpat_assum `!ce v s op s'. _ /\ _ /\ _ /\ unwrap_value _ _ _ = _ ==> _` drule_all >> strip_tac) >>
  qpat_x_assum `!ce v s op s'. _ /\ _ /\ _ /\ unwrap_value _ _ _ = _ ==> _` kall_tac >>
  Cases_on `compile_addmod va vb vm st6` >>
  gvs[as_stack_val_def] >>
  qpat_assum `!a b m s op s'. _`
    (drule_at (Pat `compile_addmod _ _ _ _ = _`)) >>
  simp[runtime_sym_value_def]
QED

Theorem runtime_sym_mulmod_names:
  runtime_sym_context_clauses /\ runtime_sym_math_clauses ==>
  !ce rt aty a bty b mty m s v s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_mulmod_names ce rt aty a bty b mty m s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >>
  qpat_x_assum `runtime_sym_context_clauses`
    (assume_tac o cj 1 o SRULE [runtime_sym_context_clauses_def]) >>
  qpat_x_assum `runtime_sym_math_clauses`
    (assume_tac o cj 2 o SRULE [runtime_sym_math_clauses_def]) >>
  rpt gen_tac >> simp[compile_mulmod_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  ntac 3
    (drule_all runtime_sym_compile_name >> strip_tac >>
     qpat_assum `!ce v s op s'. _ /\ _ /\ _ /\ unwrap_value _ _ _ = _ ==> _`
       drule_all >> strip_tac) >>
  qpat_x_assum `!ce v s op s'. _ /\ _ /\ _ /\ unwrap_value _ _ _ = _ ==> _`
    kall_tac >>
  Cases_on `compile_mulmod va vb vm st6` >>
  gvs[as_stack_val_def] >>
  qpat_assum `!a b m s op s'. _`
    (drule_at (Pat `compile_mulmod _ _ _ _ = _`)) >>
  simp[runtime_sym_value_def]
QED

Theorem runtime_sym_powmod256_names:
  runtime_sym_context_clauses /\ runtime_sym_math_clauses ==>
  !ce rt aty a bty b s v s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_powmod256_names ce rt aty a bty b s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >>
  qpat_x_assum `runtime_sym_context_clauses`
    (assume_tac o cj 1 o SRULE [runtime_sym_context_clauses_def]) >>
  qpat_x_assum `runtime_sym_math_clauses`
    (assume_tac o cj 3 o SRULE [runtime_sym_math_clauses_def]) >>
  rpt gen_tac >> simp[compile_powmod256_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  ntac 2
    (drule_all runtime_sym_compile_name >> strip_tac >>
     qpat_assum `!ce v s op s'. _ /\ _ /\ _ /\ unwrap_value _ _ _ = _ ==> _`
       drule_all >> strip_tac) >>
  qpat_x_assum `!ce v s op s'. _ /\ _ /\ _ /\ unwrap_value _ _ _ = _ ==> _`
    kall_tac >>
  Cases_on `compile_pow_mod256 va vb st4` >>
  gvs[as_stack_val_def] >>
  qpat_assum `!a b s op s'. _`
    (drule_at (Pat `compile_pow_mod256 _ _ _ = _`)) >>
  simp[runtime_sym_value_def]
QED

Theorem runtime_sym_name_fastpaths:
  runtime_sym_context_clauses /\ runtime_sym_math_clauses ==>
  runtime_sym_name_fastpath_clauses
Proof
  strip_tac >> rewrite_tac[runtime_sym_name_fastpath_clauses_def] >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
                drule_all runtime_sym_addmod_names >> simp[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
                drule_all runtime_sym_mulmod_names >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all runtime_sym_powmod256_names >> simp[]
QED
