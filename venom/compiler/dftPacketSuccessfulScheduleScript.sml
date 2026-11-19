Theory dftPacketSuccessfulSchedule
Ancestors
  dftGasInvFixedTrace dftGasInvReturnReflect dftGasInvResidualTrace
  dftRunRel dftGasOracleDefs venomInst venomState list

Theorem successful_trace_unpull[local]:
  !pre s t.
    EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y) pre /\
    inv_ev_trace orc p d fuel D (y::pre ++ post) s t ==>
    inv_ev_trace orc p d fuel D (pre ++ y::post) s t
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `inv_ev_trace orc p d fuel D (h::y::(pre ++ post)) s t` by
    (irule inv_ev_trace_exchange >> gvs[]) >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ (y::_) _ _` kall_tac >>
  gvs[Once inv_ev_trace_def] >>
  simp[Once inv_ev_trace_def] >>
  (gvs[dftGasInvResidualTraceTheory.inv_ev_trace_def])
QED

Theorem successful_trace_schedule[local]:
  !xs ys.
    dft_head_bubbles
      (\x y. dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y) xs ys ==>
    !s t. inv_ev_trace orc p d fuel D ys s t ==>
      inv_ev_trace orc p d fuel D xs s t
Proof
  ho_match_mp_tac dft_head_bubbles_ind >>
  conj_tac >- simp[inv_ev_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule successful_trace_unpull >> simp[] >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ (y::_) _ _` mp_tac >>
  simp[Once inv_ev_trace_def] >> strip_tac >>
  simp[Once inv_ev_trace_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem successful_trace_context[local]:
  !xs s t.
    LIST_REL dft_fn_rel C.ctx_functions D.ctx_functions /\
    inv_ev_trace orc p d fuel D xs s t ==>
    inv_ev_trace orc p d fuel C xs s t
Proof
  Induct >> simp[inv_ev_trace_def] >> rpt strip_tac >>
  `ev_step orc p d fuel C h s = OK u` by
    (irule inv_ev_step_success_reflect >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem dft_packet_successful_schedule_reflect:
  !xs ys s t.
    LIST_REL dft_fn_rel C.ctx_functions D.ctx_functions /\
    dft_head_bubbles
      (\x y. dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y) xs ys /\
    inv_ev_trace orc p d fuel D ys s t ==>
    inv_ev_trace orc p d fuel C xs s t
Proof
  rpt strip_tac >> irule successful_trace_context >>
  goal_assum (drule_at Any) >> irule successful_trace_schedule >>
  goal_assum (drule_at Any) >> simp[]
QED
