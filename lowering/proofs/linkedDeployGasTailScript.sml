(* Shape-independent replay of a constructor's final gas charge. *)
Theory linkedDeployGasTail
Ancestors
  deployFrameReplay e2eDeployFrame frameRunRaises frameGas frameStep
  vfmRunCall vfmExecution vfmState vfmContext arithmetic list

Theorem deploy_frame_gas_tail_bounded_output:
  es.contexts = [(ctxt, rb)] /\ ctxt.msgParams.outputTo = Code target /\
  wf_state es /\
  (!s op r s'. frame_inst_at (shadow_root es) s op /\ step_inst op s = (r, s') /\
     LENGTH s'.contexts = LENGTH s.contexts ==>
     r <> INR (SOME OutOfGas) /\
     code_deposit_cost * max_code_size <= frame_gas_left s') /\
  run_call (shadow_root es) = SOME (INR ret, ghost) /\
  (!c rb'. ret = NONE /\ ghost.contexts = [(c, rb')] ==>
     LENGTH c.returnData <= max_len) ==>
  ?r es'. run_call es = SOME (r, es') /\
    (r = INR (SOME OutOfGas) ==> max_code_size < max_len)
Proof
  strip_tac >>
  qabbrev_tac `sh = shadow_root es` >>
  `wf_state sh /\ sh.contexts = [(ctxt with msgParams updated_by
     (\p. p with outputTo := Memory <|offset := 0; size := 0|>), rb)]` by
    simp[Abbr `sh`, shadow_root_wf_state, shadow_root_def, shadow_root_contexts_def] >>
  qspecl_then [`sh`, `ctxt with msgParams updated_by
     (\p. p with outputTo := Memory <|offset := 0; size := 0|>)`,
     `rb`, `INR ret`, `ghost`] mp_tac run_call_root_ends_at_inst >>
  impl_tac >- simp[] >>
  strip_tac >>
  `run_call sh = run sh /\ run_call es = run es` by
    (conj_tac >> irule run_call_eq_run_single_context >> simp[]) >>
  `run sh = SOME (INR ret, ghost)` by fs[] >>
  Cases_on `ret`
  >- (gvs[] >>
      Cases_on `ghost.contexts` >> fs[] >> PairCases_on `h` >> gvs[] >>
      `LENGTH s.contexts = 1` by
        (qpat_assum `frame_inst_at sh s op` mp_tac >>
         qpat_assum `sh.contexts = _` mp_tac >>
         simp[NoAsms, frame_inst_at_step] >> rpt strip_tac >> gvs[]) >>
      `code_deposit_cost * max_code_size <= frame_gas_left ghost` by
        (qpat_assum `!s op r s'. frame_inst_at sh _ _ /\ _ ==> _`
           (qspecl_then [`s`, `op`, `INR NONE`, `ghost`] mp_tac) >>
         simp[]) >>
      `es.contexts <> []` by simp[] >>
      qunabbrev_tac `sh` >>
      drule_all shadow_root_run_halt >> strip_tac >>
      gvs[root_output_to_def, shadow_root_def, shadow_root_contexts_def, frame_gas_left_def] >>
      rename1 `mid.contexts = [(halt_ctxt,halt_rb)]` >>
      Cases_on `handle_step NONE mid` >> simp[] >> strip_tac >>
      qspecl_then [`mid`, `halt_ctxt`, `halt_rb`, `target`] mp_tac
        deploy_handle_step_out_of_gas >>
      simp[] >>
      `0 < code_deposit_cost * max_code_size` by EVAL_TAC >>
      simp[] >> decide_tac) >>
  `x <> OutOfGas` by
    (strip_tac >> gvs[frame_inst_raises_def] >>
     qpat_assum `!s op r s'. frame_inst_at sh _ _ /\ _ ==> _` drule >>
     disch_then drule >> fs[frame_inst_at_step]) >>
  qunabbrev_tac `sh` >>
  drule shadow_root_run_exception >> strip_tac >> fs[]
QED
