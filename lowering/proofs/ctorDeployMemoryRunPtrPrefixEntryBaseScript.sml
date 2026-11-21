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
  raw_variant vs.vs_initial_fmp vs
    (opt_deploy_entry_state_own prog prog' plan0 tops es with vs_outcomes := vs.vs_outcomes) /\
  actual.vs_labels = vs.vs_labels /\ eval_operand imm actual = SOME 0w /\
  deploy_ctor_code tops rp runtime unit
    (stmts,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) ==>
  immutable_base_zero ce actual
Proof
  rpt gen_tac >> strip_tac >>
  drule prefix_entry_immutable_operand >> disch_tac >>
  `IS_SOME (FLOOKUP vs.vs_labels "runtime_begin")` by
    (qpat_assum `raw_variant _ _ _`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
     simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def] >>
     disch_then (fn th => rewrite_tac [GSYM th]) >>
     Cases_on `FLOOKUP (lo_reloc prog prog') "runtime_begin"` >>
     fs[FLOOKUP_o_f]) >>
  simp[immutable_base_zero_def] >>
  Cases_on `imm_len tops > 0` >> simp[]
QED
