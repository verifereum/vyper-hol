Theory bodyFullExtCallSuccessSource
Ancestors
  bodyFullExtCallFrames vyperCallOutcomeProps rawCallOutcomeLengthPtr
  vyperFiniteStoragePreservation exprSimExtCallCase vyperCallOutcome
  rawCallMemoryFramePtr vyperStorageFootprint vyperStorageTrace

Theorem extcall_success_source_boundary:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  oc.co_success /\ ee' = SND (adopt_call_outcome rq oc consumed) /\
  eval_ext_call_effects cx target calldata value_opt gas ee.accounts ee =
    (INL oc.co_returnData,ee') ==>
  ee'.gas_obs = [] /\ accounts_runtime_well_typed ee'.accounts /\
  MAP FDOM es.scopes = MAP FDOM ee'.scopes /\
  LENGTH oc.co_returnData < dimword (:256) /\
  (!H. valid_horizon cx st0 H ee'.storage_trace ==>
       storage_well_formed_on cx ee' (FST H))
Proof
  strip_tac >>
  `adopt_call_outcome rq oc consumed = (INL (),ee')` by
    (gvs[adopt_call_outcome_equation]) >>
  `ee'.scopes = ee.scopes` by
    (drule oracle_take_adoption_locals >> metis_tac[]) >>
  `consumed.gas_obs = ee.gas_obs` by
    (drule take_call_outcome_frame >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `ee'.gas_obs = ee.gas_obs` by
    (gvs[adopt_call_outcome_equation] >>
     Cases_on `rq.cr_static` >> gvs[]) >>
  `accounts_runtime_well_typed ee'.accounts` by
    (irule take_adopt_call_outcome_typed >>
     metis_tac[extcall_request_ready_def]) >>
  `LENGTH oc.co_returnData < dimword (:256)` by
    (irule take_call_outcome_returnData_length >>
     metis_tac[extcall_request_ready_def]) >>
  fs[extcall_request_ready_def] >>
  rpt strip_tac >>
  `valid_horizon cx st0 H consumed.storage_trace` by
    (qpat_assum `adopt_call_outcome _ _ _ = _`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_adopt]) >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `take_call_outcome _ _ _ _ = _`
       (mp_then Any mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_take_call]) >>
  irule eval_ext_call_effects_preserves_storage_well_formed_on >>
  metis_tac[valid_horizon_def]
QED
