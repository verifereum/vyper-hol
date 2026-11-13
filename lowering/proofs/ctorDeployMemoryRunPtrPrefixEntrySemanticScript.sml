Theory ctorDeployMemoryRunPtrPrefixEntrySemantic
Ancestors
  loweringStateRelDefs
  ctorDeployLoweringFrame ctorDeployMemoryRunPtrPrefixEntryImmutable
  ctorDeployDefs e2eDeployDefs e2eDefs e2eEntry compileEnv compileVyper
  ctorDeployMemoryRunMemEntryLanding ctorDeployLoweringEntryImmutableMemory ctorDeployLoweringNoCtor
  immutableLocationProps immutableRelation entryStateRel entryLocals
  vyperTypeContract vyperTypeContractStaticMaps supportedProgram supportedDecls
  finite_map list alist vyperContext vyperInterpreter

Theorem deploy_ptr_ctor_environment:
  !tops rp runtime unit body ce nr key ut imm exit sa sb sj se sp sf func.
  deploy_ctor_code tops rp runtime unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) ==>
  immutable_section_layout ce tops /\ ce.ce_module = NONE /\ ce.ce_is_ctor
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_module_locations >> strip_tac >>
  drule deploy_ctor_return_metadata >> strip_tac >> simp[] >>
  qspecl_then [`tops`, `Deploy`, `Pure`, `"__init__"`, `[]`, `NoneT`, `[]`, `F`]
    mp_tac immutable_build_compile_env_layout >>
  simp[immutable_section_layout_def, build_compile_env_module_vars]
QED
