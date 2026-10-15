(* Focused structural clients, not stage-correctness/bytecode certificates.
 * Uses actual compile_vyper_o1 and the compiler's literal O1 hook, and checks
 * the context-plan/data/header assembly plus identity-finalizer projection.
 * Singleton checks cover the source lookup and a nonempty declaration list.
 *)
Theory e2eProducerChecks
Ancestors
  e2eProducers compileVyper codegen o1PipelineCorrect
  vyperContext finite_map

Theorem compile_vyper_o1_runtime_shape:
  compile_vyper_o1 (K SOME) tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy unit out prog cp.
    resolve_o1_policy (o1_policy all_capabilities) = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    run_venom_pipeline (K T) (K T) (K T)
      rpolicy o1_pipeline_spec unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    finalize_codegen (K SOME) rpolicy out.po_unit = SOME runtime_bc /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    assembly_target_safe rpolicy.rpol_target prog /\
    prog = execute_plan cp.cp_initial_fmp (context_plan_ops cp) ++
           data_segment_asm out.po_unit.cu_data_segment ++
           [AsmDataHeader "code_end"] /\
    runtime_bc = assemble
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp) ++
       data_segment_asm out.po_unit.cu_data_segment ++
       [AsmDataHeader "code_end"])
Proof
  REWRITE_TAC[compile_vyper_o1_def] >> strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `lower_vyper_runtime_unit tops rpolicy = SOME unit` >>
  rename1 `o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out` >>
  rename1 `codegen_assembly rpolicy out.po_unit = SOME prog` >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qexistsl_tac [`rpolicy`, `unit`, `out`, `prog`, `cplan`] >>
  gvs[o1PipelineCorrectTheory.o1_pipeline_def, finalize_codegen_identity]
QED

Theorem singleton_source_lookup_tenv:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE, tops)] ==>
  get_tenv cx = type_env tops
Proof
  simp[get_tenv_def, type_env_all_modules_single]
QED

Theorem singleton_flag_env:
  type_env_all_modules [(NONE, [FlagDecl "Color" ["red"; "blue"]])] =
    FEMPTY |+ (type_key (NONE, "Color"), FlagArgs 2)
Proof
  simp[type_env_all_modules_single, type_env_def, type_env_for_module_def]
QED
