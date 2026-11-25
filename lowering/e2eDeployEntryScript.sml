(* The shared entry and storage hypotheses of the deployment headlines. *)
Theory e2eDeployEntry
Ancestors
  e2eDefs e2eDeployDefs e2eCorrectness e2eLifecycle
  callTrace vyperStorageFootprint frameGas vfmState vfmExecutionProp
  vfmCalldataBound vfmReturndataBound

(* The target has no source installation and starts with empty persistent and
   transient storage.  The creation account fact itself is part of
   frame_tx_rel, through tx.created_in_tx. *)
Definition deploy_target_fresh_rel_def:
  deploy_target_fresh_rel am tx <=>
    ALOOKUP am.sources tx.target = NONE /\
    (lookup_account tx.target am.accounts).storage = empty_storage /\
    am.tStorage tx.target = empty_storage
End

(* The grouped entry relation used by the deployment headline. *)
Definition deploy_entry_rel_def:
  deploy_entry_rel tops deploy_bc am tx es <=>
    ?ctxt rb args_bytes.
      es.contexts = [(ctxt, rb)] /\
      evm_state_ok es /\
      (?d. es.msdomain = Collect d) /\
      frame_fresh ctxt /\ ctxt.msgParams.outputTo = Code tx.target /\
      frame_tx_rel tx es ctxt /\ world_rel am tx es /\
      ctxt.msgParams.code = deploy_bc ++ args_bytes /\
      constructor_args_encode tops tx args_bytes /\ tx.calldata = [] /\
      tx.function_name = "__init__" /\ ~tx.is_static /\ tx.created_in_tx /\
      layouts_agree tops am tx /\ deploy_target_fresh_rel am tx
End

(* The lower proof takes the original entry relation. The headline also
   requires bounded calldata and returndata and empty target storage. *)
Theorem deploy_entry_rel_state:
  deploy_entry_rel tops deploy_bc am tx es <=>
    deploy_state_rel tops deploy_bc am tx es /\ evm_state_ok es /\
    (lookup_account tx.target am.accounts).storage = empty_storage /\
    am.tStorage tx.target = empty_storage
Proof
  rw[deploy_entry_rel_def, deploy_target_fresh_rel_def,
     deploy_state_rel_def, evm_state_ok_def, frame_fresh_def,
     frame_tx_rel_def, world_rel_def] >>
  eq_tac >> strip_tac
  >- (`ctxt.msgParams.parsed = parse_code 0 FEMPTY (deploy_bc ++ args_bytes)`
        by (qpat_assum `wf_state es` (mp_tac o cj 3 o REWRITE_RULE [wf_state_def]) >>
            qpat_assum `es.contexts = [(ctxt,rb)]` (fn contexts =>
              qpat_assum `ctxt.msgParams.code = deploy_bc ++ args_bytes` (fn code =>
                simp[NoAsms, wf_context_def, contexts, code]))) >>
      conj_tac
      >- (qexistsl_tac [`ctxt`, `rb`, `args_bytes`] >>
          metis_tac[])
      >> simp[]) >>
  qexistsl_tac [`ctxt`, `rb`, `args_bytes`] >>
  metis_tac[]
QED

Theorem deploy_state_rel_evm_state_ok:
  deploy_state_rel tops deploy_bc am tx es ==>
  (evm_state_ok es <=> (FST (HD es.contexts)).msgParams.gasLimit < 2 ** 64)
Proof
  rw[deploy_state_rel_def, evm_state_ok_def] >>
  eq_tac >> strip_tac
  >- gvs[vfmCalldataBoundTheory.calldata_bounded_def]
  >- (gvs[vfmReturndataBoundTheory.returndata_bounded_def,
         vfmCalldataBoundTheory.calldata_bounded_def,
         vfmCalldataBoundTheory.memory_paid_def,
         vfmCalldataBoundTheory.frames_paid_def,
         vfmCalldataBoundTheory.outputs_fit_def,
         vfmBufferTheory.LENGTH_buffer_to_list] >>
      conj_tac
      >- (qpat_x_assum `buffer_to_list ctxt.msgParams.data = []`
            (mp_tac o Q.AP_TERM `LENGTH`) >>
          simp[vfmBufferTheory.LENGTH_buffer_to_list])
      >- (qpat_x_assum `buffer_to_list ctxt.memory = []`
            (mp_tac o Q.AP_TERM `LENGTH`) >>
          simp[vfmBufferTheory.LENGTH_buffer_to_list]))
QED

(* Every gas filling of the constructor stays inside one fixed storage
   horizon.  The starting storage is supplied separately by the headline. *)
Definition deploy_within_def:
  deploy_within H tops am tx es <=>
    let cx = deploy_evaluation_context tops am tx in
    !gs. storage_observations_ok cx H
      (deploy_storage_trace (SOME (MAP SND (call_trace es))) gs am tx tops)
End

Theorem deploy_storage_ok_from_within:
  horizon_ok H /\
  (lookup_account tx.target am.accounts).storage = empty_storage /\
  am.tStorage tx.target = empty_storage /\
  deploy_within H tops am tx es ==>
  !gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs
Proof
  simp[horizon_ok_def] >> strip_tac >> qx_gen_tac `gs` >>
  rw[deploy_storage_ok_def] >>
  simp[deploy_within_def, storage_trace_horizon_def, LET_THM] >>
  conj_tac
  >- (qpat_x_assum `deploy_within _ _ _ _ _` mp_tac >>
      simp[deploy_within_def, storage_observations_ok_def, storage_trace_horizon_def,
           storage_trace_regions_def, storage_trace_locks_def, listTheory.EVERY_MEM] >>
      metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `deploy_within _ _ _ _ _` mp_tac >>
      simp[deploy_within_def, storage_observations_ok_def, storage_trace_horizon_def,
           storage_trace_regions_def, storage_trace_locks_def, listTheory.EVERY_MEM] >>
      metis_tac[regions_consistent_def]) >>
  conj_tac
  >- (qpat_x_assum `deploy_within _ _ _ _ _` mp_tac >>
      simp[deploy_within_def, storage_observations_ok_def, storage_trace_horizon_def,
           storage_trace_regions_def, storage_trace_locks_def, listTheory.EVERY_MEM] >>
      metis_tac[storage_locks_separated_def]) >>
  conj_tac
  >- (irule deploy_empty_storage_well_formed_on >> simp[]) >>
  qpat_x_assum `deploy_within _ _ _ _ _` mp_tac >>
  simp[deploy_within_def, storage_observations_ok_def,
       storage_trace_backends_well_formed_def, storage_well_formed_on_def,
       storage_trace_regions_def, listTheory.EVERY_MEM,
       storage_trace_horizon_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  strip_tac >> gen_tac >> strip_tac >>
  Cases_on `observation` >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!gs. _` (qspecl_then [`gs`] mp_tac) >> strip_tac >>
  Cases_on `observation` >> gvs[]
  >- (rename1 `StorageRoot b n t` >>
      rename1 `StorageBackend f f0` >>
      qpat_x_assum `!region. _` (qspecl_then [`(b,n2w n,t)`] mp_tac) >>
      impl_tac >- (qexists_tac `[(b,n2w n,t)]` >> conj_tac
                   >- (qexists_tac `StorageRoot b n t` >> simp[])
                   >> simp[]) >>
      simp[] >>
      qpat_x_assum `!observation. _`
        (qspecl_then [`StorageBackend f f0`] mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `!b slot tv. _`
        (qspecl_then [`b`,`n2w n`,`t`] mp_tac) >> simp[])
  >> metis_tac[]
QED
