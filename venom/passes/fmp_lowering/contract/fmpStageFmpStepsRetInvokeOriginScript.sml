Theory fmpStageFmpStepsRetInvokeOrigin
Ancestors
  fmpStepRestrictionClosure venomInstIdsProps fmpLowerDefs venomInst
  fmpAnalysisDefs fmpStepPredicateTransport list

Theorem fmp_return_inst_origin:
  fmp_lower_inst infos ctx runner s i = SOME (out,s') /\
  MEM j out /\ j.inst_opcode = INVOKE /\
  (!name args callee sig.
    i.inst_opcode = INVOKE /\ i.inst_operands = Label name::args /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig ==> ~sig.fms_publishes) ==>
  i.inst_opcode = INVOKE /\ i.inst_id = j.inst_id /\
  i.inst_outputs = j.inst_outputs
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def] >>
  drule fmp_resolve_invoke_some >> strip_tac >>
  gvs[fmp_info_of_signature_def] >> metis_tac[]
QED

Theorem fmp_return_function_origin:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  (!i name args callee sig.
    MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
    i.inst_operands = Label name::args /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig ==> ~sig.fms_publishes) ==>
  !j. MEM j (fn_insts fn') /\ j.inst_opcode = INVOKE ==>
    ?i. MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
        i.inst_id = j.inst_id /\ i.inst_outputs = j.inst_outputs
Proof
  strip_tac >>
  qsuff_tac `EVERY (\j. j.inst_opcode = INVOKE ==>
    ?i. MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
        i.inst_id = j.inst_id /\ i.inst_outputs = j.inst_outputs)
    (fn_insts fn')`
  >- simp[EVERY_MEM] >>
  irule fmp_lower_function_every >>
  conj_tac
  >- (rpt strip_tac >> drule fmp_emit_restores_restrictions >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  qexistsl_tac [`ctx`,`fn`,`s`,`s'`] >>
  conj_tac
  >- (rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
      `i.inst_opcode = INVOKE /\ i.inst_id = j.inst_id /\
       i.inst_outputs = j.inst_outputs` by
        (irule fmp_return_inst_origin >> metis_tac[]) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> drule fmp_make_root_layout_restrictions >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

