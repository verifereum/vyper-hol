(* Linear and grouped lowering use the same window for all function
   bodies. Grouped lowering also compiles omitted defaults. *)
Theory linkedRuntimeDallocaWindows
Ancestors
  runtimePeakMemoryStmtAll runtimePeakMemoryExprAll runtimePeakMemoryExpr
  runtimePeakMemoryPackage runtimePeakMemoryRuntime runtimePeakMemoryCode
  compileUnit compileVyper moduleLowering vyperCompiler stmtLowering
  compileEnv venomInst list pair option

Theorem lower_vyper_runtime_unit_dalloca_windows_mods:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) /\
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit ==>
  !fn bb. MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
    dalloca_windows window bb.bb_instructions
Proof
  strip_tac >>
  `!ce lc ty ss. preserves_dalloca_windows window (compile_stmts ce lc ty ss)` by
    (mp_tac dalloca_windows_compile_stmts_all >> simp[]) >>
  `!ce ty e. preserves_dalloca_windows window (compile_expr ce ty e)` by
    (rw[dalloca_windows_result_state] >>
     mp_tac dalloca_windows_compile_expr_all_mutual >>
     (impl_tac >- simp[]) >> strip_tac >> first_assum irule >> simp[]) >>
  `!ce args nr key tr vw fbody rt.
     preserves_dalloca_windows window
       (compile_external_function_body ce args nr key tr vw fbody rt)` by
    (rpt gen_tac >> irule dalloca_windows_external_function_body >> simp[]) >>
  `!ints. EVERY (\(lbl:string,ce,ps,buf,nr,key,tr,vw,ctor,im,fbody,rt).
     preserves_dalloca_windows window
       (compile_internal_function ce ps buf nr key tr vw ctor im fbody rt)) ints` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     irule dalloca_windows_internal_function >> simp[]) >>
  `!fb. case fb of NONE => T
      | SOME (ce,pay,nr,key,tr,vw,fbody,rt) =>
          preserves_dalloca_windows window
            (compile_fallback_body ce pay nr key tr vw fbody rt)` by
    (simp[optionTheory.FORALL_OPTION, pairTheory.FORALL_PROD] >>
     rpt (gen_tac ORELSE conj_tac) >> irule dalloca_windows_fallback_body >> simp[]) >>
  `!sels exts ints fb strategy info.
     preserves_dalloca_windows window
       (compile_generate_runtime sels exts ints fb strategy 0 0 [] info)` by
    (rpt gen_tac >> irule dalloca_windows_generate_runtime >>
     simp[] >> simp[EVERY_MEM, pairTheory.FORALL_PROD]) >>
  `!groups ints fb. preserves_dalloca_windows window
     (compile_generate_grouped_runtime groups ints fb)` by
    (rpt gen_tac >> irule dalloca_windows_generate_grouped_runtime >> simp[] >>
     simp[EVERY_MEM] >> qx_gen_tac `group` >> disch_tac >> Cases_on `group` >>
     simp[runtime_external_group_windows_def] >>
     rename1 `runtime_external_package_windows _ pkg` >> PairCases_on `pkg` >>
     simp[runtime_external_package_windows_def]) >>
  qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_mods_def] >> pairarg_tac >>
  simp[bool_case_eq] >> strip_tac >> gvs[]
  >- (drule (REWRITE_RULE [GSYM AND_IMP_INTRO] run_grouped_lowering_dalloca_windows) >>
      disch_then (qspec_then `window` mp_tac) >> simp[]) >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] run_lowering_dalloca_windows) >>
  disch_then (qspec_then `window` mp_tac) >> simp[]
QED
