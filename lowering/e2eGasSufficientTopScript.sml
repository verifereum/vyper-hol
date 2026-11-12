(* The sufficient-gas companions over the accepted finalizers: each joins
 * its identity case from e2eGasSufficient with its assembly-optimizer case,
 * as vyper_call_correct and e2e_deploy_correctness do.
 *
 * TOP-LEVEL:
 *   vyper_call_gas_sufficient -- the companion of vyper_call_correct
 *   e2e_deploy_gas_sufficient -- the companion of e2e_deploy_correctness
 *)
Theory e2eGasSufficientTop
Ancestors
  e2eGasSufficient e2eComposition asmOptimizer

(* ===== The assembly optimizer's cases ===== *)

(* The final assembly optimizer's case, under the same hypotheses plus the
   temporary exclusion of programs that read their own code, as for
   vyper_call_correct_asm_opt.  PLANNED ADMISSION. *)
Theorem vyper_call_gas_sufficient_asm_opt:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
    ==>
    ?g. !g'.
      g <= g' /\
      call_outcomes_storage_ok am tx (MAP SND (call_trace (add_frame_gas g' es))) /\
      (!obs. ~gas_source_exempt tops
         (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
            obs am tx))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((?op. frame_inst_raises (add_frame_gas g' es) OutOfGas op) ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  cheat
QED

(* The final assembly optimizer's case, under the same hypotheses plus the
   temporary exclusion of programs that read their own code, as for
   e2e_deploy_correctness_asm_opt.  PLANNED ADMISSION. *)
Theorem e2e_deploy_gas_sufficient_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' /\
      call_outcomes_storage_ok am tx (MAP SND (call_trace (add_frame_gas g' es))) /\
      EVERY (\co. contract_storage_well_formed (deploy_evaluation_context tops am tx)
                    (initial_state (am with <|accounts := co.co_accounts;
                                              tStorage := co.co_tStorage|>) []))
        (MAP SND (call_trace (add_frame_gas g' es))) /\
      (!obs. ~deploy_gas_source_exempt tops
         (load_contract NONE obs am tx [(NONE, tops)] []))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops)
Proof
  cheat
QED

(* ===== The companions ===== *)

(* TOP-LEVEL: one theorem over the accepted finalizers, with
   vyper_call_correct's finalizer premises. *)
Theorem vyper_call_gas_sufficient:
  !fin policy tops deploy_bc runtime_bc am tx ret es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (call_outcomes_storage_ok am tx
           (MAP SND (call_trace (add_frame_gas g' es))) /\
         (!obs. ~gas_source_exempt tops
            (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
               obs am tx)) /\
         (?op. frame_inst_raises (add_frame_gas g' es) OutOfGas op) ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  `?g. !g'.
     g <= g' /\
     call_outcomes_storage_ok am tx
       (MAP SND (call_trace (add_frame_gas g' es))) /\
     (!obs. ~gas_source_exempt tops
        (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
           obs am tx))
     ==>
     ?r es'.
       run_call (add_frame_gas g' es) = SOME (r, es') /\
       ((?op. frame_inst_raises (add_frame_gas g' es) OutOfGas op) ==>
        ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
     >- (drule_all vyper_call_gas_sufficient_identity >> simp[])
     >> `~program_reads_self_code tops` by fs[] >>
     drule_all vyper_call_gas_sufficient_asm_opt >> simp[]) >>
  (* run_call is total, so the run exists whatever the conditions *)
  qexists_tac `g` >> rpt strip_tac >>
  qspec_then `add_frame_gas g' es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!g'. g <= g' /\ _ ==> _` (qspec_then `g'` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> metis_tac[]
QED

(* TOP-LEVEL: one theorem over the accepted finalizers, with
   e2e_deploy_correctness's finalizer premises.  The RETURNDATACOPY escape is
   for constructors that call out; with today's call-free constructors only
   the code-size escape is taken. *)
Theorem e2e_deploy_gas_sufficient:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (call_outcomes_storage_ok am tx
           (MAP SND (call_trace (add_frame_gas g' es))) /\
         EVERY (\co. contract_storage_well_formed
                       (deploy_evaluation_context tops am tx)
                       (initial_state (am with <|accounts := co.co_accounts;
                                                 tStorage := co.co_tStorage|>) []))
           (MAP SND (call_trace (add_frame_gas g' es))) /\
         (!obs. ~deploy_gas_source_exempt tops
            (load_contract NONE obs am tx [(NONE, tops)] [])) /\
         r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops \/
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  `?g. !g'.
     g <= g' /\
     call_outcomes_storage_ok am tx
       (MAP SND (call_trace (add_frame_gas g' es))) /\
     EVERY (\co. contract_storage_well_formed
                   (deploy_evaluation_context tops am tx)
                   (initial_state (am with <|accounts := co.co_accounts;
                                             tStorage := co.co_tStorage|>) []))
       (MAP SND (call_trace (add_frame_gas g' es))) /\
     (!obs. ~deploy_gas_source_exempt tops
        (load_contract NONE obs am tx [(NONE, tops)] []))
     ==>
     ?r es'.
       run_call (add_frame_gas g' es) = SOME (r, es') /\
       (r = INR (SOME OutOfGas) ==>
        max_code_size < LENGTH runtime_bc + imm_len tops)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
     >- (drule_all e2e_deploy_gas_sufficient_identity >> simp[])
     >> `~program_reads_self_code tops` by fs[] >>
     drule_all e2e_deploy_gas_sufficient_asm_opt >> simp[]) >>
  (* run_call is total, so the run exists whatever the conditions *)
  qexists_tac `g` >> rpt strip_tac >>
  qspec_then `add_frame_gas g' es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!g'. g <= g' /\ _ ==> _` (qspec_then `g'` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[]
QED
