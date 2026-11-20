Theory ctorDeployMemoryRunPtrPrefixEntryBase
Ancestors
  fnPlanPlaceRevertPostamble
  loweringStateRelDefs
 ctorDeployDefs ctorDeployLoweringDefs entryLocals deployEntryLayout
 e2eEntry o1PassContract compileEnv asmDataSuffixProps finite_map

Theorem prefix_entry_immutable_operand:
  !tops rp runtime unit stmts ce nr key ut imm exit sa sb sj se sp sf func.
  deploy_ctor_code tops rp runtime unit
    (stmts,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) ==>
  ce.ce_imm_alloca = if imm_len tops > 0 then SOME imm else NONE
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> rpt strip_tac >>
  drule compile_register_constructor_args_fields >> simp[]
QED

Theorem prefix_entry_immutable_base:
  !tops runtime rp unit prog prog' plan0 vs es actual stmts ce nr key ut
    imm exit sa sb sj se sp sf func.
  IS_SOME (FLOOKUP (lo_reloc prog prog') "runtime_begin") /\
  gas_variant vs (opt_deploy_entry_state_own prog prog' plan0 tops es with vs_outcomes := vs.vs_outcomes) /\
  actual.vs_labels = vs.vs_labels /\ eval_operand imm actual = SOME 0w /\
  deploy_ctor_code tops rp runtime unit
    (stmts,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) ==>
  immutable_base_zero ce actual
Proof
  rpt gen_tac >> strip_tac >>
  drule prefix_entry_immutable_operand >> disch_tac >>
  drule_all deploy_entry_runtime_label_own >> strip_tac >>
  simp[immutable_base_zero_def] >>
  Cases_on `imm_len tops > 0` >> simp[]
QED
