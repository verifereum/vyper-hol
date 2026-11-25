(* Final source gas observations do not change the linked row posts. *)
Theory createCtorPayloadGasObsMods
Ancestors
  createExprSizeExitDefsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  loweringStateRelDefs bodyPtrDefs exprSimExtract32Post exprSimSubscriptArrayCompose
  vyperState exprLoweringProps exprSimMemDefs

Theorem ctor_payload_scalar_final_obs_mods:
  expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s,op,G0,tn0) H res (ee with gas_obs := gs) G tn t <=>
  expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s,op,G0,tn0) H res ee G tn t
Proof
  simp[expr_sim_full_post_mods_def, expr_post_mods_def, extract32_expr_post_end_gas_obs,
       immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def,
       immutables_rel_def, immutable_alloca_sep_def, ghost_inv_at_mods_def]
QED

Theorem ctor_payload_vv_final_obs_mods:
  (vv_store_bound cx ty lt (ee with gas_obs := gs) raw vv t <=>
   vv_store_bound cx ty lt ee raw vv t) /\
  (ptr_vv_ok cx ty raw vv (ee with gas_obs := gs) G tn t <=>
   ptr_vv_ok cx ty raw vv ee G tn t) /\
  (ghost_inv_at_mods D lo d ce cx (ee with gas_obs := gs) G tn t <=>
   ghost_inv_at_mods D lo d ce cx ee G tn t)
Proof
  Cases_on `vv` >>
  simp[vv_store_bound_def, ptr_vv_ok_def, read_result_success_gas_iff,
       ghost_inv_at_mods_def]
QED
