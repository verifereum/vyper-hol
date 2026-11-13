(* Residual internal calls return into the existing caller-owned cells. *)
Theory functionInlinerResidualReturn
Ancestors
  functionInlinerLiveInvariant functionInlinerOperationalCuts
  functionInlinerFmp functionInlinerFrontier functionInlinerSimulation functionInlinerFrame
  functionInlinerParameterSavedReads functionInlinerParameterAncestry
  functionInlinerReturnTransport venomExecProofs venomExecSemantics venomInstProofs1
  venomState stateFrame list rich_list pred_set

Theorem inline_live_residual_return:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_frontier_stack ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  EVERY (\x. MEM x (cfgTransform$fn_all_vars a.ia_function) /\
    ~retpc_var a.ia_function x) outs /\
  INJ route.ir_rename (set outs UNION snap.ils_defined) UNIV /\
  inline_shared_frame sv = inline_shared_frame tv /\
  inline_caller_residual sv = inline_caller_residual snap.ils_state /\
  inline_fmp_result snap.ils_state.vs_fmp (IntRet ir sv) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state snap.ils_state sv)) = SOME su ==>
  ?tu. bind_outputs (MAP route.ir_rename outs) ir.iret_values
        (adopt_return_fmp ir (merge_callee_state frame.ipf_state tv)) = SOME tu /\
    inline_live_stack C cert root
      ((p,a,route,snap with <|ils_state := su;
        ils_defined := set outs UNION snap.ils_defined|>)::rest)
      (frame with ipf_state := tu) /\
    inline_frontier_stack
      ((p,a,route,snap with <|ils_state := su;
        ils_defined := set outs UNION snap.ils_defined|>)::rest)
      (frame with ipf_state := tu) /\
    su.vs_current_bb = snap.ils_state.vs_current_bb /\
    su.vs_inst_idx = snap.ils_state.vs_inst_idx /\
    su.vs_halted = snap.ils_state.vs_halted /\
    tu.vs_current_bb = frame.ipf_state.vs_current_bb /\
    tu.vs_inst_idx = frame.ipf_state.vs_inst_idx /\
    tu.vs_halted = frame.ipf_state.vs_halted
Proof
  rpt strip_tac >>
  `LENGTH outs = LENGTH ir.iret_values` by
    (gvs[bind_outputs_def, AllCaseEqs()]) >>
  qabbrev_tac `sbase = FOLDL (\s (x,w). update_var x w s)
    snap.ils_state (ZIP (outs,ir.iret_values))` >>
  qabbrev_tac `tbase = FOLDL (\s (x,w). update_var (route.ir_rename x) w s)
    frame.ipf_state (ZIP (outs,ir.iret_values))` >>
  `bind_outputs outs ir.iret_values snap.ils_state = SOME sbase` by
    simp[bind_outputs_def, Abbr `sbase`] >>
  `bind_outputs (MAP route.ir_rename outs) ir.iret_values frame.ipf_state = SOME tbase` by
    (simp[bind_outputs_def, Abbr `tbase`, ZIP_MAP, FOLDL_MAP, combinTheory.o_DEF,
          pairTheory.LAMBDA_PROD]) >>
  `su = adopt_return_fmp ir (merge_callee_state sbase sv)` by
    metis_tac[inline_return_bind_merge, optionTheory.SOME_11] >>
  qexists `adopt_return_fmp ir (merge_callee_state tbase tv)` >>
  conj_tac >- metis_tac[inline_return_bind_merge] >>
  `inline_owner_storage cert
      ((p,a,route,snap with <|ils_state := sbase;
        ils_defined := set outs UNION snap.ils_defined|>)::rest)
      (frame with ipf_state := tbase)` by
    (drule inline_live_stack_storage >> strip_tac >>
     mp_tac (inline_owner_storage_writes |> Q.INST [`writes` |-> `ZIP (outs,ir.iret_values)`]) >>
     simp[MAP_ZIP, Abbr `sbase`, Abbr `tbase`] >>
     disch_then irule >> simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> imp_res_tac MEM_ZIP >>
     gvs[EVERY_MEM] >> metis_tac[MEM_EL]) >>
  suspend "finish"
QED

Resume inline_live_residual_return[finish]:
  `inline_owner_storage cert
    ((p,a,route,snap with <|ils_state := su;
      ils_defined := set outs UNION snap.ils_defined|>)::rest)
    (frame with ipf_state := adopt_return_fmp ir (merge_callee_state tbase tv))` by
    (drule inline_owner_storage_projections >>
     disch_then (qspecl_then [`adopt_return_fmp ir (merge_callee_state tbase tv)`, `su`] mp_tac) >>
     Cases_on `ir.iret_adopt_fmp` >> simp[merge_callee_state_def, adopt_return_fmp_def]) >>
  `!vars. (sbase with vs_vars := vars) = (snap.ils_state with vs_vars := vars) /\
    (tbase with vs_vars := vars) = (frame.ipf_state with vs_vars := vars)` by
    (gen_tac >>
     mp_tac (bind_outputs_preserves |> Q.ISPEC `\u:venom_state. u with vs_vars := vars`) >>
     simp[update_var_def] >> disch_then imp_res_tac >> simp[]) >>
  qpat_x_assum `!vars. _` (mp_tac o Q.SPEC `FEMPTY`) >>
  simp[venom_state_component_equality] >> strip_tac >>
  `su.vs_fmp = snap.ils_state.vs_fmp /\
   inline_caller_residual su = inline_caller_residual snap.ils_state` by
    (Cases_on `ir.iret_adopt_fmp` >>
     fs[inline_fmp_result_def] >>
     simp[adopt_return_fmp_def, merge_callee_state_def,
         inline_caller_residual_def, inline_shared_frame_def, execution_frame_def,
         venom_state_component_equality]) >>
  `inline_shared_frame su =
     inline_shared_frame (adopt_return_fmp ir (merge_callee_state tbase tv))` by
    (drule inline_live_stack_head_shared >>
     qpat_x_assum `inline_shared_frame sv = inline_shared_frame tv` mp_tac >>
     Cases_on `ir.iret_adopt_fmp` >>
     simp[inline_shared_frame_def, execution_frame_def, merge_callee_state_def,
          adopt_return_fmp_def, venom_state_component_equality]) >>
  conj_tac
  >- (`inline_parameter_saved_reads
        ((p,a,route,snap with <|ils_state := su;
          ils_defined := set outs UNION snap.ils_defined|>)::rest)` by
        metis_tac[inline_live_stack_lifecycle, inline_parameter_saved_reads_head_replace] >>
      `inline_caller_residual (adopt_return_fmp ir (merge_callee_state tbase tv)) =
         inline_caller_residual su` by metis_tac[inline_caller_residual_shared] >>
      `(adopt_return_fmp ir (merge_callee_state tbase tv)).vs_fmp = su.vs_fmp` by
        (qpat_x_assum `inline_shared_frame su = _`
          (mp_tac o Q.AP_TERM `\s. s.vs_fmp`) >>
         simp[NoAsms, inline_shared_frame_def, execution_frame_def] >> metis_tac[]) >>
      fs[inline_live_stack_def] >>
      gvs[EVERY_MEM, pairTheory.FORALL_PROD]) >>
  Cases_on `ir.iret_adopt_fmp` >>
  simp[inline_frontier_stack_def, merge_callee_state_def, adopt_return_fmp_def] >>
  fs[inline_frontier_stack_def]
QED

Finalise inline_live_residual_return
