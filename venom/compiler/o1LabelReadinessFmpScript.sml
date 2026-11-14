Theory o1LabelReadinessFmp
Ancestors
  o1PassContract fmpStepRewrite fmpStepRetpcShape fmpLowerDefs
  fmpAnalysisProps venomInst unitLabelMapIdentity list rich_list
  fmpStepPredicateTransport fmpStepRestrictionClosure venomPassDispatcher

Theorem fmp_inst_all_label_origin[local]:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM j out /\ MEM (Label l) j.inst_operands ==>
  MEM (Label l) inst.inst_operands
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def, MEM_APPEND]
  >- metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM, NULL_EQ]
  >- metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM, NULL_EQ] >>
  drule fmp_resolve_invoke_some >> strip_tac >>
  drule lookup_function_name >> strip_tac >> gvs[MEM_APPEND] >>
  qpat_x_assum `MEM _ (if _ then _ else _)` mp_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem fmp_function_no_label[local]:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  (!i. MEM i (fn_insts fn) ==> ~MEM (Label l) i.inst_operands) ==>
  !i. MEM i (fn_insts fn') ==> ~MEM (Label l) i.inst_operands
Proof
  strip_tac >> drule fmp_lower_function_every >>
  disch_then (qspec_then `\j. ~MEM (Label l) j.inst_operands` mp_tac) >>
  simp[EVERY_MEM] >>
  (impl_tac >- (rpt conj_tac
    >- (rpt strip_tac >> metis_tac[fmp_inst_all_label_origin])
    >- (rpt strip_tac >> drule fmp_emit_restores_restrictions >>
        rewrite_tac[EVERY_MEM] >> strip_tac >> metis_tac[]) >>
    rpt strip_tac >> drule fmp_make_root_layout_restrictions >>
    rewrite_tac[EVERY_MEM, MEM_APPEND] >> strip_tac >> metis_tac[])) >> simp[]
QED

Theorem fmp_pass_no_runtime_begin:
 !rpolicy observed s fn out.
 fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed s fn out /\
 o1_fn_shape observed.cu_context fn /\
 (!i. MEM i (fn_insts fn) ==> ~MEM (Label "runtime_begin") i.inst_operands) ==>
 !i. MEM i (fn_insts out.fpo_function) ==> ~MEM (Label "runtime_begin") i.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_def, AllCaseEqs()] >>
  metis_tac[fmp_function_no_label]
QED
