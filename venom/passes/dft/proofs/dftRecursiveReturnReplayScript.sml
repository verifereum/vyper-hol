Theory dftRecursiveReturnReplay
Ancestors
  dftRecursiveActivePhase dftRecursiveCallProvenance dftMixedCrossing
  dftOccurrenceReturn dftOccurrenceResidual instIdxIndep
  venomExecSemantics venomState list option

Theorem dft_pending_index:
  !us s. dft_pending_apply us (s with vs_inst_idx := n) =
    (dft_pending_apply us s) with vs_inst_idx := n
Proof
  Induct >- simp[dft_pending_apply_def] >> rpt gen_tac >>
  pure_rewrite_tac[dft_pending_apply_def, FOLDL] >>
  pure_rewrite_tac[GSYM dft_pending_apply_def] >>
  `update_var (FST h) (SND h) (s with vs_inst_idx := n) =
   (update_var (FST h) (SND h) s) with vs_inst_idx := n` by
    simp[update_var_def] >> simp[]
QED

Theorem dft_restore_index:
  dft_restore outs ret cs (s with vs_inst_idx := n) =
  OPTION_MAP (\t. t with vs_inst_idx := n) (dft_restore outs ret cs s)
Proof
  `!u. FOLDL (\s' (out,value). update_var out value s') u
      (ZIP (outs,ret.iret_values)) =
    dft_pending_apply (ZIP (outs,ret.iret_values)) u` by
    simp[dft_pending_apply_def, pairTheory.LAMBDA_PROD] >>
  simp[dft_restore_def, bind_outputs_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[merge_callee_state_def, adopt_return_fmp_def] >>
  once_rewrite_tac[GSYM dft_pending_index] >> simp[]
QED

Theorem dft_schedule_call_outputs_disjoint:
  dft_original_schedule f b q /\
  q.bb_instructions = pre ++ done ++ x::call::post /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE ==>
  !v. MEM v x.inst_outputs ==> ~MEM v call.inst_outputs
Proof
  strip_tac >>
  `ssa_form f /\ MEM b f.fn_blocks` by
    fs[dftProtectedRuntimeTheory.dft_original_schedule_def, venomWfTheory.wf_ssa_def] >>
  `MEM x b.bb_instructions /\ MEM call b.bb_instructions` by
    (drule dft_original_schedule_perm >>
     disch_then (mp_tac o MATCH_MP sortingTheory.PERM_MEM_EQ) >> simp[] >> metis_tac[]) >>
  `MEM x (fn_insts f) /\ MEM call (fn_insts f)` by
    (simp[venomInstTheory.fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     conj_tac >> qexists `b` >> simp[]) >>
  `x <> call` by
    (strip_tac >> gvs[] >> drule_all dftOccurrenceFrameTheory.dft_invoke_inversion_disjoint >>
     simp[venomEffectsTheory.read_effects_def, venomEffectsTheory.empty_effects_def,
          venomEffectsTheory.all_effects_def]) >>
  drule_all dftCorrectnessTheory.ssa_disjoint_defs >>
  simp[venomInstTheory.inst_defs_def, pred_setTheory.DISJOINT_DEF,
       pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_legal_return_replay_equal:
  dft_original_cut f b q s /\
  q.bb_instructions = pp ++ done ++ x::call::todo /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) /\
  (!l. MEM (Label l) x.inst_operands ==> l IN FDOM s.vs_labels) /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  step_inst_base x s = OK t /\
  dft_restore call.inst_outputs ret cs
    (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME a /\
  dft_restore call.inst_outputs ret cs s = SOME b' ==>
  ?u. step_inst_base x (b' with vs_inst_idx := SUC s.vs_inst_idx) = OK u /\
      (u with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
      (a with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >>
  drule_all dft_legal_invoke_partner_return_replay >> strip_tac >>
  `t = dft_pending_apply us s` by gvs[] >>
  `!v. MEM v x.inst_outputs ==> ~MEM v call.inst_outputs` by
    (`dft_original_schedule f b q` by
       fs[dftProtectedRuntimeTheory.dft_original_cut_def] >>
     drule dft_schedule_call_outputs_disjoint >>
     disch_then assume_tac >> metis_tac[]) >>
  `EVERY (\p. ~MEM (FST p) call.inst_outputs) us` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `dft_restore call.inst_outputs ret cs t =
    SOME (dft_pending_apply us b')` by
    simp[dft_restore_pending] >>
  `a = (dft_pending_apply us b') with vs_inst_idx := SUC s.vs_inst_idx` by
    metis_tac[dft_restore_index, optionTheory.OPTION_MAP_DEF,
              optionTheory.SOME_11] >>
  qexists `(dft_pending_apply us b') with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem dft_certificate_return_replay_equal:
  dft_crossing_evidence z /\
  dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME b ==>
  ?u. step_inst_base z.dft_cert_partner
        (b with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = OK u /\
      (u with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx)) =
      (a with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))
Proof
  strip_tac >>
  qpat_x_assum `dft_crossing_evidence z` mp_tac >>
  pure_rewrite_tac[dft_crossing_evidence_def] >> strip_tac >>
  drule_all dft_legal_return_replay_equal >> simp[]
QED

(* Select the owed instruction's caller by the certificate orientation. *)
Theorem dft_provenanced_return_replay_equal:
  dft_provenanced_frame fm bm (SOME z)
    (DftCaller fL fuelL bbL call sL) (DftCaller fR fuelR bbR call sR) /\
  dft_restore call.inst_outputs ret cs sL = SOME afterL /\
  dft_restore call.inst_outputs ret cs sR = SOME afterR ==>
  ?u. step_inst_base z.dft_cert_partner
        ((if z.dft_cert_forward then afterR else afterL)
           with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = OK u /\
      (u with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx)) =
      ((if z.dft_cert_forward then afterL else afterR)
           with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))
Proof
  strip_tac >>
  qpat_x_assum `dft_provenanced_frame _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_provenanced_frame_def, dft_certificate_saved_def, LET_THM] >>
  Cases_on `z.dft_cert_forward` >> simp[] >> strip_tac >> gvs[] >>
  drule_all dft_certificate_return_replay_equal >> simp[]
QED

Theorem dft_provenanced_return_pair_failure:
  dft_provenanced_frame fm bm (SOME z)
    (DftCaller fL fuelL bbL call sL) (DftCaller fR fuelR bbR call sR) ==>
  (dft_restore call.inst_outputs ret cs sL = NONE <=>
   dft_restore call.inst_outputs ret cs sR = NONE)
Proof
  simp[dft_restore_pair_failure]
QED
