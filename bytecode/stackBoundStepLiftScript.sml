(* Lift raw opcode contracts through the full-step exception handler. *)
Theory stackBoundStepLift
Ancestors
  stackBoundInterface stackBoundFrames vfmExecution vfmExecutionProp
  vfmStepLength vfmSameFrame vfmContext vfmState list pair finite_map

Theorem sb_decoded_step_inner:
  s.contexts <> [] /\ sb_decoded (FST (HD s.contexts)) op ==>
  step_inner s = sb_inner op s
Proof
  simp[sb_decoded_def] >> strip_tac >>
  Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc` >>
  gvs[step_inner_def, sb_inner_def, bind_def, ignore_bind_def,
      get_current_context_def, return_def, fail_def] >>
  Cases_on `LENGTH (FST (HD s.contexts)).msgParams.code <=
    (FST (HD s.contexts)).pc` >>
  gvs[step_inst_def, bind_def, fail_def, finish_def,
      get_current_context_def, return_def, ignore_bind_def,
      set_return_data_def, set_current_context_def]
QED

Theorem sb_opcode_contracts_step_simulates:
  (!op. sb_opcode_contract op) ==> sb_step_simulates
Proof
  strip_tac >> rw[sb_step_simulates_def] >>
  `?op. sb_decoded (FST (HD s.contexts)) op` by
    (Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
       (FST (HD s.contexts)).pc` >> simp[sb_decoded_def]) >>
  qpat_x_assum `!op. sb_opcode_contract op`
    (qspec_then `op` mp_tac) >>
  simp[sb_opcode_contract_def] >>
  disch_then (qspecl_then [`s`,`a`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all sb_step_decode >> strip_tac >>
  Cases_on `sb_inner op s` >> rename1 `sb_inner op s = (result,mid)` >>
  qpat_x_assum `step s = _` mp_tac >> simp[handle_def] >>
  Cases_on `result` >> simp[] >> strip_tac >>
  `LENGTH s.contexts <= LENGTH mid.contexts` by
    (drule_all sb_decoded_step_inner >> strip_tac >>
     metis_tac[same_frame_or_grow_step_inner_named,
               same_frame_or_grow_length, arithmeticTheory.GREATER_EQ]) >>
  `mid.contexts <> []` by (Cases_on `mid.contexts` >> gvs[]) >>
  `handle_step y mid = (INL (),t)` by metis_tac[] >>
  drule_all sb_handle_no_same_depth_success >> strip_tac >>
  `LENGTH s.contexts < LENGTH mid.contexts` by decide_tac >>
  qpat_x_assum `!r t. _`
    (qspecl_then [`INR y`,`mid`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `q` >> simp[] >>
  irule sb_handle_resume >> metis_tac[]
QED
