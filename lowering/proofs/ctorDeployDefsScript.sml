(* Definitions for the deployment composition (e2e_deploy_correctness).
 * TOP-LEVEL: deploy_phases, deploy_entry_state, deploy_source_ok, deploy_dead,
 * deploy_source_exempt, deploy_venom_result_rel.
 * Helper: deploy_venom_result_rel_terminates.  imm_len, mem_dead_bytes
 * and imm_section_dead are immSectionDead's.
 * deploy_venom_result_rel is the Venom-level counterpart of deploy_result_rel:
 * it relates load_contract's result to a run of the deployment unit, and the
 * creation-frame piece turns it into deploy_result_rel.
 *)
Theory ctorDeployDefs
Ancestors
  immSectionDead e2eDeployDefs e2eProducers ptrDiscipline passSimulationDefs
  venomExecSemantics venomState e2eEntry compileVyper compileEnv valueEncoding
  immutableSectionRel vyperValue vyperContext

(* Every artifact a successful compile_vyper (K SOME) produces for the
   deployment unit, as compile_vyper_runtime_phases does for the runtime unit. *)
Definition deploy_phases_def:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) <=>
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
    dout.po_final_assembly = rpolicy.rpol_final_assembly /\
    codegen_assembly rpolicy dout.po_unit = SOME prog /\
    generate_context_plan dout.po_unit.cu_context = SOME cplan /\
    assembly_target_safe rpolicy.rpol_target prog /\
    prog = execute_plan cplan.cp_initial_fmp (context_plan_ops cplan) ++
           data_segment_asm dout.po_unit.cu_data_segment ++
           [AsmDataHeader "code_end"] /\
    deploy_bc = assemble prog
End

(* The deployment unit's entry state: entry_venom_state with the alloca
   frontier past the immutables fixed region, which the constructor addresses
   by literal offsets rather than through an ALLOCA. *)
Definition deploy_entry_state_def:
  deploy_entry_state prog cplan tops es =
    entry_venom_state prog cplan es with vs_alloca_next := imm_len tops
End

(* The source-side hypotheses of e2e_deploy_correctness. *)
Definition deploy_source_ok_def:
  deploy_source_ok tops am tx <=>
    supported_program tops /\ constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx
End

(* The deployment's dead bytes, fixed before the run (so independent of its
   gas readings): the target's dead storage and transient storage bytes in
   the context load_contract runs the constructor in, as external_call_dead,
   and the dead bytes of the immutables section the run returns after the
   runtime code.  vs_immutables are not observed, so all of them are dead. *)
Definition deploy_dead_def:
  deploy_dead tops runtime_bc am tx =
    let cx = initial_evaluation_context ((tx.target, [(NONE, tops)]) :: am.sources)
               am.layouts tx NONE in
    <| d_stor := (\a st. if a = tx.target
                         then {(k,b) | storage_dead cx F st (w2n k) b}
                         else {});
       d_trans := (\a st. if a = tx.target
                          then {(k,b) | storage_dead cx T st (w2n k) b}
                          else {});
       d_imm := K UNIV;
       d_ret := (\r. {i | LENGTH runtime_bc <= i /\
                         imm_section_dead tops (DROP (LENGTH runtime_bc) r)
                           (i - LENGTH runtime_bc)}) |>
End

Definition deploy_source_exempt_def:
  deploy_source_exempt tops
    (src : (abstract_machine # call_request list) + exception) <=>
    case src of
      INR (Error e) => unspecified_behaviour_exempt tops e
    | _ => F
End

(* A successful constructor halts returning the runtime code followed by its
   immutables section, with the source's accounts (the target modulo code,
   its storage modulo storage_dead), transient storage (modulo storage_dead)
   and logs. Failures abort; a source Error may also halt
   only when it is exempt. *)
Definition deploy_venom_result_rel_def:
  deploy_venom_result_rel tops runtime_bc tx
    (src : (abstract_machine # call_request list) + exception) vres <=>
    case (src, vres) of
      (INL (am', rqs), Halt ss) =>
        let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
        ?section.
          ss.vs_returndata = runtime_bc ++ section /\
          immutables_section_rel tops (account_immutables am' tx.target) section /\
          (!a. a <> tx.target ==>
               lookup_account a ss.vs_accounts = lookup_account a am'.accounts) /\
          (lookup_account tx.target ss.vs_accounts) with code := [] =
          (lookup_account tx.target am'.accounts) with
            <| code := [];
               storage := (lookup_account tx.target ss.vs_accounts).storage |> /\
          storage_agree
            (storage_dead cx F (lookup_account tx.target am'.accounts).storage)
            (lookup_account tx.target am'.accounts).storage
            (lookup_account tx.target ss.vs_accounts).storage /\
          transient_agree cx am'.tStorage ss.vs_transient /\
          logs_correspond (compiled_event_info tops) (type_env tops)
            tx.target am'.logs ss.vs_logs
    | (INR (AssertException s), Abort Revert_abort _) => T
    | (INR (AssertException s), Abort ExHalt_abort _) => (s = "UNREACHABLE")
    | (INR (Error e), Abort _ _) => T
    | (INR (Error e), Halt _) => unspecified_behaviour_exempt tops e
    | _ => F
End

Theorem deploy_venom_result_rel_terminates:
  deploy_venom_result_rel tops runtime_bc tx src res ==> terminates res
Proof
  Cases_on `res` >> simp[terminates_def] >>
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >> simp[deploy_venom_result_rel_def])
  >> rename1 `INR exc` >> Cases_on `exc` >> simp[deploy_venom_result_rel_def]
QED
