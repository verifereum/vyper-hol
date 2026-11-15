(*
 * The O1 stage contracts' companion on external-call requests at an abort.
 *
 * ctx_sim relates the two runs' requests only at a halt (dead_result_rel);
 * at an abort it says nothing of the states.  ctx_abort_rq adds that the
 * output run's requests are a prefix of the input run's, request by request
 * up to the dead bytes D.  A prefix, not the whole list: DFT may run an
 * ASSERT before a CALL that does not feed it, so its output can abort one
 * request earlier.  A request the output does make was made by the input
 * at the same index, which is what the callee-outcome producer reads.
 *
 * o1_stage_rq_contract_gas is o1_stage_contract_gas with ctx_abort_rq
 * added under the same chosen input oracle, so that DFT's choice serves
 * both; o1PipelineRequests composes these into S4's companion.
 *)
Theory o1RequestContract
Ancestors
  o1PassContract o1PassLift ptrDiscipline venomPassSchedule stateFrame
  unitTransformDefs passSimulationDefs venomExecSemantics venomState
  list rich_list

(* ===== Request lists ===== *)

Theorem request_agree_except_refl:
  request_agree_except D r r
Proof
  simp[request_agree_except_def, accounts_agree_except_def,
       transient_agree_except_def, storage_agree_except_def,
       word_agree_except_def,
       extCallOracleTheory.call_request_component_equality]
QED

(* The second list is a prefix of the first, element by element up to the
   dead bytes of the first. *)
Definition request_prefix_rel_def:
  request_prefix_rel D rqs rqs' <=>
    LENGTH rqs' <= LENGTH rqs /\
    LIST_REL (request_agree_except D) (TAKE (LENGTH rqs') rqs) rqs'
End

Theorem request_prefix_rel_EL:
  request_prefix_rel D rqs rqs' <=>
    LENGTH rqs' <= LENGTH rqs /\
    !i. i < LENGTH rqs' ==> request_agree_except D (EL i rqs) (EL i rqs')
Proof
  simp[request_prefix_rel_def, LIST_REL_EL_EQN, LENGTH_TAKE_EQ] >>
  eq_tac >> rw[] >> gvs[EL_TAKE]
QED

Theorem LIST_REL_imp_request_prefix_rel:
  LIST_REL (request_agree_except D) rqs rqs' ==> request_prefix_rel D rqs rqs'
Proof
  rw[request_prefix_rel_EL] >> gvs[LIST_REL_EL_EQN]
QED

Theorem isPREFIX_imp_request_prefix_rel:
  rqs' <<= rqs ==> request_prefix_rel D rqs rqs'
Proof
  rw[IS_PREFIX_APPEND] >>
  simp[request_prefix_rel_EL, EL_APPEND1, request_agree_except_refl]
QED

Theorem request_prefix_rel_refl:
  request_prefix_rel D rqs rqs
Proof
  simp[request_prefix_rel_EL, request_agree_except_refl]
QED

Theorem request_prefix_rel_trans:
  dead_wf D /\ request_prefix_rel D r1 r2 /\ request_prefix_rel D r2 r3 ==>
  request_prefix_rel D r1 r3
Proof
  rw[request_prefix_rel_EL] >> irule request_agree_except_trans >>
  simp[] >> qexists_tac `EL i r2` >> simp[]
QED

(* The form the callee-outcome producer reads: the first i requests agree,
   for any i up to the output run's count. *)
Theorem request_prefix_rel_take:
  request_prefix_rel D rqs rqs' /\ i <= LENGTH rqs' ==>
  LIST_REL (request_agree_except D) (TAKE i rqs) (TAKE i rqs')
Proof
  rw[request_prefix_rel_EL, LIST_REL_EL_EQN, LENGTH_TAKE_EQ, EL_TAKE]
QED

(* ===== Runs ===== *)

(* An aborting run of ctx from s is matched by an aborting run of ctx' from
   s' whose requests are a prefix of its own. *)
Definition ctx_abort_rq_def:
  ctx_abort_rq D ctx ctx' s s' <=>
    !fuel a t. run_context fuel ctx s = Abort a t ==>
      ?fuel' a' t'. run_context fuel' ctx' s' = Abort a' t' /\
        request_prefix_rel D t.vs_requests t'.vs_requests
End

Theorem ctx_abort_rq_refl:
  ctx_abort_rq D C C s s
Proof
  rw[ctx_abort_rq_def] >> metis_tac[request_prefix_rel_refl]
QED

Theorem ctx_abort_rq_trans:
  dead_wf D /\ ctx_abort_rq D C1 C2 s1 s2 /\ ctx_abort_rq D C2 C3 s2 s3 ==>
  ctx_abort_rq D C1 C3 s1 s3
Proof
  rw[ctx_abort_rq_def] >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[request_prefix_rel_trans]
QED

Theorem ctx_abort_rq_run_context_eq:
  ctx_abort_rq D C1 C2 s s /\
  (!fuel. run_context fuel C2 s = run_context fuel C3 s)
  ==> ctx_abort_rq D C1 C3 s s
Proof
  simp[ctx_abort_rq_def] >> metis_tac[]
QED

Theorem execution_frame_requests[local]:
  execution_frame s' = execution_frame s ==> s'.vs_requests = s.vs_requests
Proof
  strip_tac >>
  `(execution_frame s').vs_requests = (execution_frame s).vs_requests` by
    simp[] >>
  gvs[execution_frame_def]
QED

(* Bisimilar contexts abort with the same frame, requests included: the
   route of ctx_bisim_ctx_sim, keeping the abort's state. *)
Theorem ctx_bisim_ctx_abort_rq:
  ctx_bisim C C' /\ C'.ctx_entry = C.ctx_entry /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  ctx_abort_rq D C C' vs vs
Proof
  strip_tac >> rw[ctx_abort_rq_def] >>
  Cases_on `C.ctx_entry` >> gvs[run_context_def] >>
  Cases_on `lookup_function x C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function x C.ctx_functions = SOME fn` >>
  fs[ctx_bisim_def] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `fn_entry_label fn` >> gvs[run_function_def] >>
  `fn_entry_state fn
     (vs with <|vs_prev_bb := NONE; vs_current_bb := x'; vs_inst_idx := 0|>)` by
    (irule context_fn_entry_state >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!fuel. terminates (run_blocks fuel C fn _) ==> _`
    (qspec_then `fuel` mp_tac) >> simp[terminates_def] >>
  strip_tac >> qexists_tac `fuel'` >>
  Cases_on `run_blocks fuel' C' fn' (vs with
     <|vs_prev_bb := NONE; vs_current_bb := x'; vs_inst_idx := 0|>)` >>
  gvs[frame_result_rel_def] >>
  metis_tac[execution_frame_requests, request_prefix_rel_refl]
QED

(* ===== Stage contracts ===== *)

(* o1_stage_contract_gas with the abort companion under the same choice of
   input oracle. *)
Definition o1_stage_rq_contract_gas_def:
  o1_stage_rq_contract_gas rpolicy D pass view pre I I' <=>
    !C C' vs'.
      ctx_pass_stage rpolicy pass view C C' /\ pre C C' /\ dead_wf D /\
      o1_ctx_shape C /\ o1_run_state_ok vs' ==>
      ?vs. gas_variant vs vs' /\
           (I C vs ==> ctx_sim D C C' vs vs' /\ ctx_abort_rq D C C' vs vs' /\
                       I' C' vs')
End

(* The companion of the k-th run of the walk. *)
Definition o1_run_rq_contract_gas_def:
  o1_run_rq_contract_gas rpolicy D k <=>
    o1_stage_rq_contract_gas rpolicy D (EL k o1_fn_passes)
      (o1_walk_view rpolicy k) (o1_pre k) (o1_inv D k) (o1_inv D (SUC k))
End

(* A pass whose stage contract runs from the same initial state lifts with
   its abort fact at that state. *)
Theorem o1_stage_contract_rq_lift:
  o1_stage_contract rpolicy D pass view pre Inv Inv' /\
  (!C C' vs.
     ctx_pass_stage rpolicy pass view C C' /\ pre C C' /\ dead_wf D /\
     o1_ctx_shape C /\ o1_run_state_ok vs /\ Inv C vs ==>
     ctx_abort_rq D C C' vs vs) ==>
  o1_stage_rq_contract_gas rpolicy D pass view pre Inv Inv'
Proof
  rw[o1_stage_contract_def, o1_stage_rq_contract_gas_def] >>
  qexists_tac `vs'` >> simp[gas_variant_refl] >> metis_tac[ctx_sim_fuel_imp_ctx_sim]
QED
