Theory entryRuntimeContextCode
Ancestors
  entryCodePredicate entryRuntimeBodyCode entryPackagedRuntimeCode
  entryExtractionCodePredicate entryDallocaCoverage compileVyper vyperCompiler
  moduleLowering list

Theorem entry_code_run_lowering[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_generate_runtime sels exts ints fb pol.rpol_frontend_dispatch
      nb bytes buckets info) /\
  run_lowering sels exts ints fb pol nb bytes buckets info label = SOME unit ==>
  !f. MEM f unit.cu_context.ctx_functions ==>
    EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)
Proof
  strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  `entry_code_pred (\i. i.inst_opcode <> DALLOCA) st1` by
    (metis_tac[entry_preserves_code_apply, entry_code_initial]) >>
  metis_tac[entry_code_extracted_context]
QED

Theorem entry_runtime_context_no_dalloca:
  supported_program tops /\ lower_vyper_runtime_unit tops pol = SOME unit ==>
  !f. MEM f unit.cu_context.ctx_functions ==>
    ~EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f)
Proof
  strip_tac >>
  `EVERY (\(lbl,ce,args,cds,pay,nr,key,tr,vw,fb,rt).
      entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
        (compile_external_function_body ce args nr key tr vw fb rt))
    (MAP (set_external_package_target pol.rpol_target o
          package_external_fn tops F (assign_nkeys tops 0))
      (FST (classify_functions tops)))` by
    (simp[GSYM MAP_COMPOSE, entry_code_packaged_externals]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule entry_code_packaged_internals >>
  disch_then (qspec_then `pol.rpol_target` mp_tac) >>
  drule entry_code_packaged_fallback >>
  disch_then (qspec_then `pol.rpol_target` mp_tac) >>
  simp[GSYM MAP_COMPOSE] >> rpt strip_tac >>
  drule_at (Pos (el 2)) entry_code_run_lowering >>
  disch_then (qspec_then `f` mp_tac) >>
  (impl_tac >- (simp[] >> irule entry_code_generate_runtime >>
               gvs[MAP_COMPOSE])) >>
  simp[combinTheory.o_DEF]
QED

Theorem entry_runtime_context_fmp_room:
  supported_program tops /\ lower_vyper_runtime_unit tops pol = SOME unit /\
  MEM func unit.cu_context.ctx_functions ==>
  fmp_room unit.cu_context func s
Proof
  strip_tac >> irule context_without_dalloca_fmp_room >> simp[] >>
  qpat_x_assum `MEM func _` kall_tac >>
  gen_tac >> strip_tac >> drule_all entry_runtime_context_no_dalloca >> simp[]
QED
