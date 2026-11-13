(* A piece of deploy_ctor_entry_reaches_body (ctorDeployLoweringEntry).
   fmp_room holds vacuously at every state of the constructor function: a
   supported program's raw deployment unit has no DALLOCA. *)
Theory ctorDeployLoweringEntryFmp
Ancestors
  ctorDeployLoweringDefs exprLoweringProps ctorDeployShape o1PipelineCorrect
  ptrDiscipline

Theorem deploy_ctor_entry_fmp_room:
  !tops rpolicy runtime_bc dunit
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final
   func s.
    supported_program tops /\ supported_program_deploy tops /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) ==>
    fmp_room dunit.cu_context func s
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  drule_all lower_vyper_deploy_unit_source_unit_ok >> strip_tac >>
  drule o1_source_unit_ok_no_dalloca >>
  simp[fmp_room_def, ctx_has_dalloca_def, listTheory.EXISTS_MEM] >>
  metis_tac[]
QED
