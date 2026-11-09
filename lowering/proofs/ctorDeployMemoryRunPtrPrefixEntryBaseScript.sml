Theory ctorDeployMemoryRunPtrPrefixEntryBase
Ancestors
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

Theorem prefix_entry_runtime_label:
  !policy tops bc runtime rp unit dout prog plan0 vs es actual.
  deploy_phases policy tops (bc,runtime) (rp,unit,dout,prog,plan0) /\
  gas_variant vs (deploy_entry_state prog plan0 tops es) /\
  actual.vs_labels = vs.vs_labels ==>
  IS_SOME (FLOOKUP actual.vs_labels "runtime_begin")
Proof
  rpt gen_tac >> strip_tac >>
  `vs.vs_labels = (entry_venom_state prog plan0 es).vs_labels` by
    (qpat_x_assum `gas_variant _ _` mp_tac >>
     simp[gas_variant_def, deploy_entry_state_def] >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >> simp[]) >>
  fs[deploy_phases_def] >>
  drule_all lower_vyper_deploy_unit_entry_runtime_label >>
  disch_then (qspecl_then [`[]`,`plan0`,`es`] mp_tac) >>
  simp[entry_venom_state_frame_fields, data_suffix_label_offsets] >>
  Cases_on `FLOOKUP (SND (compute_label_offsets prog)) "runtime_begin"` >> simp[]
QED

Theorem prefix_entry_immutable_base:
  !policy tops bc runtime rp unit dout prog plan0 vs es actual stmts ce nr key ut
    imm exit sa sb sj se sp sf func.
  deploy_phases policy tops (bc,runtime) (rp,unit,dout,prog,plan0) /\
  gas_variant vs (deploy_entry_state prog plan0 tops es) /\
  actual.vs_labels = vs.vs_labels /\ eval_operand imm actual = SOME 0w /\
  deploy_ctor_code tops rp runtime unit
    (stmts,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) ==>
  immutable_base_zero ce actual
Proof
  rpt gen_tac >> strip_tac >>
  drule prefix_entry_immutable_operand >> disch_tac >>
  drule_all prefix_entry_runtime_label >> disch_tac >>
  simp[immutable_base_zero_def] >>
  Cases_on `imm_len tops > 0` >> simp[]
QED
