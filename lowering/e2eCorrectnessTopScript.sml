(* Presentation layer for iterating on the call theorem without changing
 * the shared boundary definitions or rebuilding their consumers. *)
Theory e2eCorrectnessTop
Ancestors
  e2eCorrectness e2eDefs vyperTypeContract vyperTypeContractSoundness
  vyperTypeInitialState vyperTypeContractStaticMaps vyperContext
  vyperState vyperInterpreter vyperCall finite_map
  compileVyper supportedProgram vfmExecution callTrace

(* TOP-LEVEL: declared bare globals have cells with matching type tags. *)
Definition global_cells_typed_top_def:
  global_cells_typed_top tops globals imms <=>
    !src id ty.
      FLOOKUP globals (src, id) = SOME ty ==>
      ?tv v.
        FLOOKUP (get_source_immutables src imms) id = SOME (tv, v) /\
        evaluate_type (type_env tops) ty = SOME tv
End

(* TOP-LEVEL: typing requirements not already supplied by deployment. *)
Definition source_typing_ok_top_def:
  source_typing_ok_top tops am tx <=>
    ?art cenv.
      check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
      global_cells_typed_top tops art.cta_bare_globals (account_immutables am tx.target) /\
      constants_fold_module [(NONE, tops)] (account_immutables am tx.target) NONE tops FEMPTY = SOME cenv /\
      cenv SUBMAP get_source_immutables NONE (account_immutables am tx.target) /\
      machine_well_typed am /\ call_tx_well_typed tx
End

Theorem source_typing_ok_top_imp:
  source_typing_ok_top tops am tx /\ source_deployment_rel tops am tx ==>
  source_typing_ok tops am tx
Proof
  rw[source_typing_ok_top_def, global_cells_typed_top_def, source_deployment_rel_def,
     source_typing_ok_def] >>
  qexists_tac `art` >>
  simp[checked_contract_runtime_ready_def] >>
  conj_tac >- metis_tac[check_contract_single_module_exports_ok] >>
  mp_tac (Q.INST
    [`layouts` |-> `am.layouts`, `addr` |-> `tx.target`,
     `mods` |-> `[(NONE, tops)]`, `art` |-> `art`,
     `sources` |-> `am.sources`, `tx` |-> `tx`]
    check_contract_toplevel_vtypes_consistent_initial) >>
  simp[] >> strip_tac >>
  mp_tac (Q.INST
    [`layouts` |-> `am.layouts`, `addr` |-> `tx.target`,
     `mods` |-> `[(NONE, tops)]`, `art` |-> `art`,
     `sources` |-> `am.sources`, `tx` |-> `tx`]
    check_contract_bare_globals_consistent_initial) >>
  simp[] >> strip_tac >>
  fs[account_immutables_def, empty_immutables_def,
     get_module_code_def, initial_evaluation_context_def] >>
  simp[immutables_ready_def, initial_evaluation_context_def,
       get_tenv_def, get_module_code_def, type_env_all_modules_def,
       GSYM type_env_def] >>
  conj_tac >- metis_tac[optionTheory.IS_SOME_EXISTS] >>
  conj_tac >-
   (rpt strip_tac >>
    qpat_x_assum `!src id ty. _ ==> ?tv v. _` drule >>
    strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP art.cta_toplevel_vtypes (NONE,id) = SOME (Type ty)` >>
  Cases_on `FLOOKUP art.cta_bare_globals (NONE,id)`
  >- (qpat_x_assum `!src id ty. _ /\ FLOOKUP art.cta_bare_globals (src,id) = NONE ==> _`
        (qspecl_then [`NONE`,`id`,`ty`] mp_tac) >>
      simp[] >> strip_tac >> gvs[]) >>
  rename1 `FLOOKUP art.cta_bare_globals (NONE,id) = SOME bare_ty` >>
  qpat_x_assum `!src id ty. _ ==> ?ts. _ /\ FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ _`
    (qspecl_then [`NONE`,`id`,`bare_ty`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `!src id ty. _ ==> ?tv v. _` drule >>
  strip_tac >> gvs[]
QED

Theorem vyper_call_correct_top:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok_top tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    call_outcomes_storage_ok am tx (MAP SND (call_trace es))
    ==>
    ?result es'.
      run_call es = SOME (result, es') /\
      (frame_resource_starved es result es' \/
       call_result_rel tops ret am tx es result es')
Proof
  rpt strip_tac >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  `source_typing_ok tops am tx` by metis_tac[source_typing_ok_top_imp] >>
  metis_tac[vyper_call_correct]
QED
