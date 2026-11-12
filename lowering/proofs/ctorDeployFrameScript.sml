(* Creation-frame boundary: a run of the root-shadowed frame related to the
 * deployment unit's result gives the real creation frame's result
 * (shadow_root_run_halt/_exception and deploy_frame_complete).
 * TOP-LEVEL: deploy_venom_frame (a piece of e2e_deploy_correctness; admitted until proved),
 * deploy_frame_gas_sufficient (S7g-d, a piece of e2e_deploy_gas_sufficient; a planned admission).
 *)
Theory ctorDeployFrame
Ancestors
  ctorDeployDefs deployFrameReplay codegenCorrectness e2eDeployFrame
  frameOutcome vfmRunCall vfmState passSimulationDefs e2eDeployDefs
  frameGas venomRunBounded

(* Single-frame outcomes depend on the start state only through its one
   context's logs and the transaction parameters. *)
Theorem frame_outcome_single_transfer_none[local]:
  es.contexts = [(c0,rb0)] /\ mid.contexts = [(c1,rb1)] /\
  mid.txParams = es.txParams /\ c1.logs = c0.logs ++ lgs /\
  frame_outcome mid r es' NONE out [] ==>
  frame_outcome es r es' NONE out lgs
Proof
  rw[frame_outcome_def] >> gvs[]
QED

Theorem frame_resource_starved_single_transfer[local]:
  es.contexts = [(c0,rb0)] /\ mid.contexts = [(c1,rb1)] /\
  mid.txParams = es.txParams /\ frame_resource_starved mid r es' ==>
  frame_resource_starved es r es'
Proof
  rpt strip_tac >> gvs[frame_resource_starved_def, frame_outcome_def] >>
  metis_tac[]
QED

Theorem shadow_root_frame_outcome_exc[local]:
  es.contexts = [(c0,rb0)] /\
  frame_outcome (shadow_root es) r (shadow_root es') (SOME exc) out lgs ==>
  frame_outcome es r es' (SOME exc) out lgs'
Proof
  rpt strip_tac >>
  gvs[frame_outcome_def, shadow_root_def, shadow_root_contexts_def] >>
  Cases_on `es'.contexts` >> gvs[shadow_root_contexts_def] >>
  PairCases_on `h` >> Cases_on `t` >>
  gvs[shadow_root_contexts_def, shadow_root_contexts_nil]
QED

(* An exceptional shadow run is the real run, outcome included. *)
Theorem deploy_frame_exception[local]:
  es.contexts = [(c0,rb0)] /\
  run_call (shadow_root es) = SOME (r,g) /\
  frame_outcome (shadow_root es) r g (SOME exc) out lgs ==>
  ?es'. run_call es = SOME (r,es') /\
        !lgs'. frame_outcome es r es' (SOME exc) out lgs'
Proof
  strip_tac >>
  `LENGTH (shadow_root es).contexts = 1`
    by simp[shadow_root_def, shadow_root_contexts_def] >>
  `run (shadow_root es) = SOME (r,g)`
    by metis_tac[run_call_eq_run_single_context] >>
  `r = INR (SOME exc)`
    by gvs[frame_outcome_def, shadow_root_def, shadow_root_contexts_def] >>
  gvs[] >> drule shadow_root_run_exception >> strip_tac >>
  qexists_tac `es'` >> simp[run_call_eq_run_single_context] >>
  gen_tac >> irule shadow_root_frame_outcome_exc >> metis_tac[]
QED

(* A halting shadow run is the real run up to the root's halt handler. *)
Theorem deploy_frame_halt_mid[local]:
  es.contexts = [(c0,rb0)] /\
  run_call (shadow_root es) = SOME (r,g) /\
  frame_outcome (shadow_root es) r g NONE out lgs ==>
  ?mid ctxt rb.
    mid.contexts = [(ctxt,rb)] /\ mid.rollback = g.rollback /\
    ctxt.msgParams.outputTo = c0.msgParams.outputTo /\
    ctxt.returnData = out /\ ctxt.logs = c0.logs ++ lgs /\
    mid.txParams = es.txParams /\
    run_call es = SOME (handle_step NONE mid)
Proof
  strip_tac >>
  `LENGTH (shadow_root es).contexts = 1`
    by simp[shadow_root_def, shadow_root_contexts_def] >>
  `run (shadow_root es) = SOME (r,g)`
    by metis_tac[run_call_eq_run_single_context] >>
  `r = INR NONE`
    by gvs[frame_outcome_def, shadow_root_def, shadow_root_contexts_def] >>
  gvs[] >>
  `es.contexts <> []` by simp[] >>
  drule_all shadow_root_run_halt >> strip_tac >>
  qexistsl [`mid`,`ctxt`,`rb`] >>
  gvs[root_output_to_def, run_call_eq_run_single_context] >>
  gvs[frame_outcome_def, shadow_root_def, shadow_root_contexts_def]
QED

(* A pending deletion erases any earlier update of the deleted account. *)
Theorem process_deletions_update_mem[local]:
  !dels accs a x.
    MEM a dels ==>
    process_deletions dels (update_account a x accs) =
    process_deletions dels accs
Proof
  Induct >> fs[vfmExecutionTheory.process_deletions_def, update_account_def] >>
  rpt gen_tac >> Cases_on `h = a` >> fs[combinTheory.UPDATE_EQ] >>
  strip_tac >>
  `(h =+ empty_account_state) ((a =+ x) accs) =
   (a =+ x) ((h =+ empty_account_state) accs)` by
    (irule combinTheory.UPDATE_COMMUTES >> simp[]) >>
  simp[]
QED

(* The unit's logs correspond to the EVM's exactly when they are equal. *)
Theorem logs_correspond_eq[local]:
  logs_correspond info tenv addr l1 l2 <=> l1 = l2
Proof
  `log_entry_corresponds info tenv addr = $=` by
    simp[FUN_EQ_THM, e2eDefsTheory.log_entry_corresponds_concrete_event] >>
  simp[e2eDefsTheory.logs_correspond_def, listTheory.LIST_REL_eq]
QED

(* The shadow run records the real frame's call requests. *)
Theorem shadow_root_call_requests[local]:
  es.contexts <> [] ==> call_requests (shadow_root es) = call_requests es
Proof
  simp[callTraceTheory.call_requests_def, callTraceTheory.call_trace_def, shadow_root_frame_obs]
QED

Theorem deploy_venom_frame:
  !H tops runtime_bc deploy_bc am tx es src res.
    deploy_state_rel tops deploy_bc am tx es /\
    runtime_bc <> [] /\ ~(?t. runtime_bc = 0xEFw :: t) /\
    deploy_venom_result_rel H tops runtime_bc tx src res /\
    (?r g. run_call (shadow_root es) = SOME (r, g) /\
           (frame_resource_starved (shadow_root es) r g \/
            venom_frame_rel (shadow_root es) r g res))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       deploy_result_rel H tops runtime_bc tx es r es' src)
Proof
  rpt strip_tac >>
  `?c0 rb0. es.contexts = [(c0,rb0)] /\
            c0.msgParams.outputTo = Code tx.target`
    by gvs[deploy_state_rel_def] >>
  qpat_x_assum `deploy_state_rel _ _ _ _ _` kall_tac
  >- (gvs[frame_resource_starved_def] >>
      drule_all deploy_frame_exception >> strip_tac >>
      first_assum (irule_at (Pos hd)) >>
      simp[frame_resource_starved_def] >> metis_tac[]) >>
  Cases_on `res` >> gvs[venom_frame_rel_def]
  >~ [`Halt ss`]
  >- (drule_all deploy_frame_halt_mid >> strip_tac >>
      `call_requests (shadow_root es) = call_requests es` by
        (irule shadow_root_call_requests >> simp[]) >>
      Cases_on `src`
      >- (PairCases_on `x` >>
          Cases_on `ALOOKUP x0.sources tx.target = NONE`
          >- (gvs[deploy_venom_result_rel_def, logs_correspond_eq] >>
              qspecl_then [`mid`,`ctxt`,`rb`,`tx.target`] mp_tac
                deploy_frame_complete >>
              impl_tac >- simp[] >>
              strip_tac >> gvs[]
              >- (disj1_tac >> irule frame_resource_starved_single_transfer >>
                  metis_tac[]) >>
              disj2_tac >> simp[deploy_result_rel_def] >>
              simp[lookup_account_def, update_account_def,
                   combinTheory.APPLY_UPDATE_THM] >>
              conj_tac
              >- (irule frame_outcome_single_transfer_none >> metis_tac[]) >>
              `process_deletions ss.vs_pending_deletions
                 (update_account tx.target
                    (lookup_account tx.target ss.vs_accounts with code := [])
                    ss.vs_accounts) =
               process_deletions ss.vs_pending_deletions ss.vs_accounts` by
                (irule process_deletions_update_mem >> simp[]) >>
              fs[update_account_def, lookup_account_def]) >>
          gvs[deploy_venom_result_rel_def, logs_correspond_eq] >>
          qspecl_then [`mid`,`ctxt`,`rb`,`tx.target`] mp_tac
            deploy_frame_complete >>
          impl_tac >- (Cases_on `runtime_bc` >> gvs[]) >>
          strip_tac >> gvs[]
          >- (disj1_tac >> irule frame_resource_starved_single_transfer >>
              metis_tac[]) >>
          disj2_tac >> simp[deploy_result_rel_def] >>
          qexists `section` >>
          gvs[lookup_account_def, update_account_def,
              combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_EQ] >>
          irule frame_outcome_single_transfer_none >> metis_tac[]) >>
      Cases_on `y` >>
      gvs[deploy_venom_result_rel_def, deploy_result_rel_def] >>
      Cases_on `handle_step NONE mid` >> gvs[])
  >~ [`Abort ab vs'`]
  >- (Cases_on `src`
      >- (PairCases_on `x` >> Cases_on `ab` >>
          gvs[deploy_venom_result_rel_def]) >>
      Cases_on `ab` >> gvs[] >>
      drule_all deploy_frame_exception >> strip_tac >>
      first_assum (irule_at (Pos hd)) >>
      Cases_on `y` >>
      gvs[deploy_venom_result_rel_def, deploy_result_rel_def] >>
      metis_tac[]) >>
  drule deploy_venom_result_rel_terminates >> simp[terminates_def]
QED

(* PLANNED ADMISSION S7g-d, sufficient gas for deployment: the deploy-side
   counterpart of codegen_gas_sufficient together with deploy_venom_frame.
   Given the constructor unit's resource bound, some gas g, independent of
   the creation frame, is enough: with g' >= g more gas, the creation frame
   ends in OutOfGas only when the code it deposits, runtime_bc and the
   immutables section, is longer than max_code_size, which handle_create
   rejects with OutOfGas at any gas.  No RETURNDATACOPY exemption: the
   constructor makes no calls.  The last premise says what the constructor
   returns, so the deposit's length is LENGTH runtime_bc + imm_len tops.
   Proof idea: S7g's per-instruction argument on the root-shadowed frame
   codegen runs (shadow_root), with no RETURNDATACOPY run, plus the
   deposit, which costs at most code_deposit_cost * max_code_size. *)
Theorem deploy_frame_gas_sufficient:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan fuel M.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    unit_shape_ok dout.po_unit /\
    constructor_call_free tops
    ==>
    ?g. !g' am tx es Inv.
      g <= g' /\
      deploy_state_rel tops deploy_bc am tx (add_frame_gas g' es) /\
      LENGTH (FST (HD (add_frame_gas g' es).contexts)).msgParams.code
        <= dimword(:256) DIV 2 /\
      codegen_context_obligations Inv dout.po_unit.cu_context cplan /\
      codegen_reachability_package Inv dout.po_unit.cu_context
        (deploy_entry_state prog cplan tops (add_frame_gas g' es)) /\
      venom_run_bounded fuel M dout.po_unit.cu_context
        (deploy_entry_state prog cplan tops (add_frame_gas g' es)) /\
      (?src vfuel.
         ~deploy_source_exempt tops src /\
         deploy_venom_result_rel tops runtime_bc tx src
           (run_context vfuel dout.po_unit.cu_context
              (deploy_entry_state prog cplan tops (add_frame_gas g' es))))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops)
Proof
  cheat
QED
