(* What a successful load_contract leaves for the deploy dead-transport:
 * its sources and layouts.  A supported constructor never halts, so the
 * success always installs the source.
 *)
Theory ctorDeployDeadLoad
Ancestors
  ctorDeployDefs vyperState vyperContext vyperInterpreter vyperTypeContractSoundness
  vyperTypeExternalDefaults vyperTypeContractStaticMaps
  vyperTypeDeploymentMachine typedCopyProducer supportedDecls
  supportedProgram bodyStorageCases evalNoHalt list

(* A supported program's constructor (declared, or the synthetic empty one)
   never halts: it has no defaults, its body cannot halt, and the value
   transfer and the lock only raise errors. *)
Theorem call_external_function_deploy_no_halt:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  lookup_function src name Deploy tops = SOME (mut,nr,args,dflts,ret,fbody) /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals fbody ret =
    (INR HaltException, am', rqs) ==> F
Proof
  strip_tac >>
  `dflts = [] /\ !st st'. eval_stmts cx fbody st <> (INR HaltException, st')` by
    (drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[]
     >- simp[Once evaluate_def, return_def] >>
     drule_all supported_program_declaration >>
     simp[supported_declaration_header_def, supported_declaration_body_def,
          supported_function_body_def, NULL_EQ] >> strip_tac >>
     drule (cj 2 supported_stmts_storage_syntax) >> strip_tac >>
     rpt gen_tac >> irule (cj 4 eval_no_halt) >> metis_tac[]) >>
  qpat_x_assum `dflts = []` SUBST_ALL_TAC >>
  drule call_external_function_halt_cases >> strip_tac >>
  qpat_x_assum `_ = (INR HaltException, st_body)` mp_tac >>
  simp[bind_def, ignore_bind_def, AllCaseEqs(), raise_def, return_def,
       set_scopes_def] >>
  rpt strip_tac >> gvs[]
  >- (qpat_x_assum `option_CASE _ _ _ _ = _` mp_tac >>
      Cases_on `bind_arguments (type_env_all_modules mods) args vals` >>
      simp[raise_def, bind_def, set_scopes_def] >>
      Cases_on `nr` >> simp[return_def] >>
      Cases_on `cx.nonreentrant_slot` >> simp[raise_def, bind_def] >>
      simp[acquire_nonreentrant_lock_def, bind_def, get_transient_storage_def,
           LET_THM] >>
      rw[raise_def, return_def, update_transient_def] >>
      Cases_on `cx.txn.is_static` >> simp[]) >>
  drule send_call_value_error >> simp[]
QED

Theorem load_contract_sources_layouts:
  !orc gobs am tx tops exps am' rqs.
    load_contract orc gobs am tx [(NONE,tops)] exps = INL (am', rqs) /\
    supported_program tops ==>
    am'.sources = (tx.target, [(NONE,tops)]) :: am.sources /\
    am'.layouts = am.layouts
Proof
  rpt strip_tac >>
  `!srcs lay t. (initial_evaluation_context srcs lay t NONE).txn = t` by
    simp[initial_evaluation_context_def] >>
  `am'.sources <> am.sources` by
    (drule load_contract_success_cases >> strip_tac >> gvs[]
     >~ [`_ = (INR HaltException,am_ctor,rqs)`]
     >- (`get_module_code
            (initial_evaluation_context ((tx.target,[(NONE,tops)])::am.sources)
               am.layouts (tx with created_in_tx := T) NONE with in_deploy := T)
            NONE = SOME tops` by
           simp[get_module_code_def, initial_evaluation_context_def] >>
         drule_all call_external_function_deploy_no_halt >> simp[]) >>
     imp_res_tac call_external_function_preserves_sources >>
     gvs[finalize_pending_deletions_def, CONS_ACYCLIC]) >>
  drule_all load_contract_success_constructor_constants_context >> strip_tac >>
  `am_ctor.sources = am_c.sources` by
    (drule_at (Pos (el 2)) call_external_function_deploy_success_cases >>
     simp[] >> disch_then (qspec_then `am_c` mp_tac) >>
     impl_tac >- fs[] >> strip_tac >>
     simp[abstract_machine_from_state_def]) >>
  drule evaluate_all_constants_preserves_machine_static_components >>
  simp[]
QED

Theorem deploy_source_ok_struct_args_unique:
  !tops am tx. deploy_source_ok tops am tx ==> struct_args_unique tops
Proof
  rw[deploy_source_ok_def, e2eDeployDefsTheory.deploy_typing_ok_def] >>
  metis_tac[checked_contract_struct_args_unique]
QED
