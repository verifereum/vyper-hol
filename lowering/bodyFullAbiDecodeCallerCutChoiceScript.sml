Theory bodyFullAbiDecodeCallerCutChoice
Ancestors
  bodyFullAbiDecodeCallerFull bodyFullAbiDecodeCallerSetupCut
  bodyFullAbiDecodeGuardedCut bodyFullAbiDecodeCutPath exprSimAbiDecodeOblivious
  abiBuiltinDecodeCorrect externalEntryShape exprSimAbiGasBridge pair

local
  val normalized = CONV_RULE (REPEATC (REWR_CONV boolTheory.LET_THM THENC BETA_CONV))
    bodyFullAbiDecodeCallerFullTheory.abi_decode_caller_full_conditional
  val (premises, _) = boolSyntax.dest_imp (concl normalized)
  val (_, rest) = boolSyntax.dest_conj premises
  val (_, rest) = boolSyntax.dest_conj rest
  val (selector, _) = boolSyntax.dest_conj rest
  val _ = if null (free_vars selector) then ()
          else raise Fail "ABI decoder selector hypothesis must be closed"
in
  val decode_cut_selector = selector
end

Theorem setup_suffix_extends[local]:
  lower_abi_decode data info mn mx cap start = (out,final) /\
  abi_builtin_decode_setup data mn mx cap start = (ops,ready) ==>
  cs_extends ready final
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  fs[] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[GSYM PULL_EXISTS] >> metis_tac[cj 1 compile_abi_decode_labels, SND]
QED

Theorem guarded_handoff_first[local]:
  (layout /\ blocks /\ entry /\ contained /\ origin /\ cursor ==> result) ==>
  (entry /\ contained /\ origin) ==> (layout /\ blocks /\ cursor) ==> result
Proof
  metis_tac[]
QED

Theorem abi_decode_caller_cut_choice:
  ^decode_cut_selector
Proof
  rpt gen_tac >> simp_tac pure_ss [LET_THM, BETA_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp_tac pure_ss [GSYM CONJ_ASSOC] >>
  drule lower_abi_decode_frag_facts >> strip_tac >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  drule_all setup_suffix_extends >> strip_tac >>
  drule_at (Pat `abi_builtin_decode_setup _ _ _ _ _ = _`)
    (SIMP_RULE pure_ss [LET_THM, BETA_THM, GSYM CONJ_ASSOC]
       abi_decode_caller_setup_cut) >>
  disch_then (drule_at (Pat `fn_has_code (start_relabel _ _ _) _ _`)) >>
  disch_then (mp_tac o BETA_RULE o
    Q.INST [`V` |-> `\H. valid_horizon cx st0 H es1.storage_trace`,
            `s''` |-> `s`, `input_bytes` |-> `bs`, `origin` |-> `sa`,
            `ce'` |-> `ce`, `es` |-> `es1`, `es0` |-> `es`] o SPEC_ALL) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r0` (qx_choose_then `Gs` (qx_choose_then `ts`
    (map_every assume_tac o CONJUNCTS)))) >>
  qpat_assum `(?a. r0 = Abort Revert_abort a) \/ _`
    (DISJ_CASES_THEN2 (qx_choose_then `a` assume_tac)
      (qx_choose_then `ready_state` (CONJUNCTS_THEN2 assume_tac assume_tac)))
  >- (qexistsl [`r0`, `Gs`, `ts`, `r0`, `Gs`, `ts`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (disj1_tac >> qexists `a` >> simp[]) >>
      qexistsl [`L`, `ids`, `id`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >> disj2_tac >>
      qpat_x_assum `(?t u. r0 = OK t /\ _) \/ _` mp_tac >>
      qpat_assum `r0 = Abort Revert_abort a` (fn th =>
        simp_tac bool_ss [th, venomExecSemanticsTheory.exec_result_distinct])) >>
  qpat_assum `!t Gs ts. _ ==> _` (qspecl_then [`ready_state`, `Gs`, `ts`] mp_tac) >>
  (impl_tac >- (simp_tac pure_ss [GSYM CONJ_ASSOC] >>
    qpat_assum `(?output input. ~ready_state.vs_halted /\ _) /\ _` ACCEPT_TAC)) >>
  disch_then (mk_asm "guarded_entry") >>
  qpat_x_assum `(?t u. r0 = OK t /\ _) \/ _` mp_tac >>
  qpat_assum `r0 = OK ready_state` (fn th =>
    simp_tac bool_ss [th, venomExecSemanticsTheory.exec_result_distinct,
                     venomExecSemanticsTheory.exec_result_11]) >>
  disch_then (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
  drule abiBuiltinDecodeSetupTheory.abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends start ready` by
    (irule abiEncoderChildContextTheory.abi_encoder_straight_extends >> simp[]) >>
  asm "guarded_entry" (fn th =>
    let
      val producer = Q.INST [`V` |-> `\H. valid_horizon cx st0 H es1.storage_trace`]
        (INST_TYPE [alpha |-> ``:256``]
          (SPEC_ALL abi_decode_guarded_to_buf_cut_selected))
      val reordered = MATCH_MP guarded_handoff_first
        (CONV_RULE (REDEPTH_CONV BETA_CONV) producer)
      val by_entry = CONV_RULE (LAND_CONV (PURE_REWRITE_CONV [GSYM CONJ_ASSOC])) reordered
    in
      mp_tac (Q.INST [`cut_start` |-> `start`]
        (MATCH_MP by_entry (PURE_REWRITE_RULE [GSYM CONJ_ASSOC] th)))
    end) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS) (mk_asm "terminal"))))) >>
  qexistsl [`r0`, `Gs`, `ts`, `r`, `Gf`, `tnf`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (disj2_tac >> qexists `ready_state` >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM CONJ_ASSOC])) >>
  qexistsl [`L`, `ids`, `id`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  asm_x "terminal" (DISJ_CASES_THEN2
    (qx_choose_then `v` (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)))
    (qx_choose_then `v` (qx_choose_then `w` (qx_choose_then `fuel`
      (map_every assume_tac o CONJUNCTS)))))
  >- (disj1_tac >> qexistsl [`v`, `w`] >>
      `run_from 0 ctx (frag_relabel_observer start final L ids func id) w =
       Halt (stop_view w)` by
        (irule abiEncoderObserverTheory.run_from_stop_view >>
         qexistsl [`<|bb_label := final.cs_current_bb;
           bb_instructions := final.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
         qpat_assum `(w.vs_current_bb,w.vs_inst_idx) = frag_observer_cut final` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[frag_observer_cut_def] >> strip_tac >>
         simp[frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
      `?k. run_from k ctx (frag_relabel_observer start final L ids func id) u =
           Halt (stop_view w)` by
        (qpat_assum `local_prefix _ _ (frag_observer_cut final) u w` mp_tac >>
         qpat_assum `run_from 0 _ _ w = Halt _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         metis_tac[abi_decode_cut_prefix_run, venomExecSemanticsTheory.exec_result_distinct]) >>
      `(?k. run_from k ctx (frag_relabel_observer start final L ids func id)
         (s with vs_current_bb := L) = Halt (stop_view w))` suffices_by
        (disch_then (qx_choose_then `fuel_all` assume_tac) >>
         qexists `fuel_all` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `local_prefix _ _ (L,LENGTH ready.cs_current_insts) _ u` mp_tac >>
      qpat_assum `run_from _ _ _ u = Halt (stop_view w)` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      metis_tac[abi_decode_cut_prefix_run, venomExecSemanticsTheory.exec_result_distinct]) >>
  disj2_tac >> qexistsl [`v`, `w`] >>
  `(?k. run_from k ctx (frag_relabel_observer start final L ids func id)
     (s with vs_current_bb := L) = Abort Revert_abort w)` suffices_by
    (disch_then (qx_choose_then `fuel_all` assume_tac) >>
     qexists `fuel_all` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `local_prefix _ _ (L,LENGTH ready.cs_current_insts) _ u` mp_tac >>
  qpat_assum `run_from fuel _ _ u = Abort Revert_abort w` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[abi_decode_cut_prefix_run, venomExecSemanticsTheory.exec_result_distinct]
QED
