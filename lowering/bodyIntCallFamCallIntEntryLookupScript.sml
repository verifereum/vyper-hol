(* Selected internal compilation witnesses, for both lowering modes. *)
Theory bodyIntCallFamCallIntEntryLookup
Ancestors
  moduleLowering compileEnv vyperCompiler intCallLookup ctorDeployShape ctorDeployLoweringCode intCallCallee
  bodyIntCallFamCallIntEntryPackage bodyIntCallFamCallIntEntrySelectedSegment bodyIntCallFamCallIntEntrySegmentCode


Theorem intcall_extracted_internal_lookup:
  !entry packages sf ctx data imm name rb rc.
    extract_context_with_internals entry packages sf = SOME (ctx,data) /\
    lowering_context_ok (install_immutable_reservation imm ctx) /\
    MEM (name,rb,rc) (internal_fn_descriptors packages) ==>
    ?blocks.
      lookup_function name
        (install_immutable_reservation imm ctx).ctx_functions =
        SOME (mk_internal_function name blocks rb rc) /\
      blocks <> [] /\ (HD blocks).bb_label = name
Proof
  rpt gen_tac >>
  simp[vyperCompilerTheory.extract_context_with_internals_def,
       vyperCompilerTheory.install_immutable_reservation_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs(), vyperCompilerTheory.lowering_context_ok_def,
      venomInstTheory.ctx_fn_names_def, venomInstTheory.mk_venom_context_def] >>
  drule package_internal_blocks_metadata >> strip_tac >>
  drule descriptor_names_fn_names >> strip_tac >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors packages))` by gvs[] >>
  drule_all package_internal_blocks_mem >> strip_tac >>
  qexists_tac `fbs` >> simp[] >>
  metis_tac[lookup_function_distinct_mem, mk_internal_function_metadata,
            listTheory.MEM, listTheory.MAP, listTheory.ALL_DISTINCT]
QED

Theorem intcall_deploy_internal_lookup:
  !has_ctor policy runtime imm args size packages ce body pay nr key tr
   entry unit name rb nret.
    run_deploy_lowering has_ctor policy runtime imm args size packages
      ce body pay nr key tr entry = SOME unit /\
    MEM (name,rb,nret) (internal_fn_descriptors packages) ==>
    ?blocks.
      lookup_function name unit.cu_context.ctx_functions =
        SOME (mk_internal_function name blocks rb nret) /\
      blocks <> [] /\ (HD blocks).bb_label = name
Proof
  rpt gen_tac >> simp[run_deploy_lowering_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs()] >>
  drule_all intcall_extracted_internal_lookup >> simp[]
QED

Theorem intcall_deploy_source_lookup:
  !tops policy runtime unit exts ints fb cf src.
    lower_vyper_deploy_unit tops policy runtime = SOME unit /\
    classify_functions tops = (exts,ints,fb,SOME cf) /\ MEM src ints ==>
    ?blocks.
      lookup_function (FST (source_internal_fn_descriptor tops T src))
        unit.cu_context.ctx_functions =
      SOME (mk_internal_function
        (FST (source_internal_fn_descriptor tops T src)) blocks
        (FST (SND (source_internal_fn_descriptor tops T src)))
        (SND (SND (source_internal_fn_descriptor tops T src)))) /\
      blocks <> [] /\
      (HD blocks).bb_label = FST (source_internal_fn_descriptor tops T src)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_lowering_trace >> strip_tac >>
  `MEM (source_internal_fn_descriptor tops T src)
    (internal_fn_descriptors
      (MAP (set_internal_package_target policy.rpol_target o
        package_internal_fn tops F (assign_nkeys tops 0) T (imm_len tops)) ints))`
    by (simp[GSYM listTheory.MAP_MAP_o,
          compileVyperTheory.internal_fn_descriptors_set_internal_package_target,
          compileVyperTheory.internal_fn_descriptors_MAP_package_internal_fn,
          listTheory.MEM_MAP] >>
        qexists_tac `src` >> simp[]) >>
  Cases_on `source_internal_fn_descriptor tops T src` >>
  rename1 `_ = (lbl,metadata)` >> PairCases_on `metadata` >> gvs[] >>
  drule_all intcall_extracted_internal_lookup >> simp[]
QED
