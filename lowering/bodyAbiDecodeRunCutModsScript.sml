(* Select one physical ABI decoder run before interpreting its linked post. *)
Theory bodyAbiDecodeRunCutMods
Ancestors
  bodyFullAbiDecodeCallerFull bodyFullAbiDecodeCallerSetupCut
  bodyFullAbiDecodeGuardedCut bodyFullAbiDecodeCutPath exprSimAbiDecodeOblivious
  abiBuiltinDecodeCorrect externalEntryShape exprSimAbiGasBridge pair
  bodyFullAbiDecodeCallerSetupOrigin bodyFullAbiDecodeRecursive
  abiBuiltinDecodeSetup abiEncoderChildContext abiDecoderAppend abiEncoderObserver
  venomExecSemantics fragExec
Libs
  markerLib

(* Share the physical entry and endpoint formulae used by the checked
   caller. Neither the singleton context nor its selector proof is reused. *)
local
  val normalized = CONV_RULE (REPEATC (REWR_CONV LET_THM THENC BETA_CONV))
    abi_decode_caller_full_conditional
  val (suppliers, _) = dest_imp (concl normalized)
  val (_, after_setup) = dest_conj suppliers
  val (guarded_producer, after_guarded) = dest_conj after_setup
  val (selector, _) = dest_conj after_guarded
  val unfold_lets = REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM, BETA_CONV])
  val (premise, result) = dest_imp (#2 (strip_forall
    (rhs (concl (unfold_lets selector)))))
  val ((_, entry), collision) = (dest_conj ## I) (dest_conj premise)
  val (results, (joint, cut)) = (I ## dest_conj) (strip_exists result)
  val physical = ``lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    start = (out,final) /\ fn_has_code start final func``
  fun close tm = list_mk_forall (free_vars tm, tm)
in
  val regular_guarded_statement = guarded_producer
  val collision_run_statement = close ``(^physical /\ ^entry) /\ ^collision ==> ^result``
  val run_statement = close ``(^physical /\ ^entry) ==>
    ^(list_mk_exists (results, ``^joint /\ (^collision ==> ^cut)``))``
end

Theorem decode_setup_suffix_extends[local]:
  lower_abi_decode data info mn mx cap start = (out,final) /\
  abi_builtin_decode_setup data mn mx cap start = (ops,ready) ==>
  cs_extends ready final
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> simp[pairTheory.PAIR_EQ] >>
  strip_tac >> drule abiDecoderAppendTheory.cs_extends_abi_decode >> simp[]
QED

Theorem decode_guarded_handoff_first[local]:
  (layout /\ blocks /\ entry /\ contained /\ origin /\ cursor ==> result) ==>
  (entry /\ contained /\ origin) ==> (layout /\ blocks /\ cursor) ==> result
Proof
  metis_tac[]
QED

Theorem abi_decode_collision_run_mods[local]:
  ^collision_run_statement
Proof
  rpt gen_tac >> simp_tac pure_ss [LET_THM, BETA_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp_tac pure_ss [GSYM CONJ_ASSOC] >>
  drule lower_abi_decode_frag_facts >> strip_tac >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  drule_all decode_setup_suffix_extends >> strip_tac >>
  qpat_assum `abi_builtin_decode_setup _ _ _ _ _ = _` (fn setup =>
    qpat_assum `fn_has_code (start_relabel _ _ _) _ _` (fn code =>
      let
        val rule = CONV_RULE
          (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM, BETA_CONV]) THENC
           PURE_REWRITE_CONV [GSYM CONJ_ASSOC]) abi_decode_caller_setup_cut
        val with_setup = PART_MATCH (lhand o lhand) rule (concl setup)
        val relabelled_code = find_term
          (can (match_term ``fn_has_code (start_relabel _ _ _) _ _``)) o lhand
        val with_code = PART_MATCH relabelled_code with_setup (concl code)
      in
        mp_tac (BETA_RULE (Q.INST
          [`V` |-> `\H. valid_horizon cx st0 H es1.storage_trace`,
           `s` |-> `s`, `input_bytes` |-> `bs`, `origin` |-> `sa`,
           `ce'` |-> `ce`, `es` |-> `es1`, `es0` |-> `es`]
          (SPEC_ALL with_code)))
      end)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r0` (qx_choose_then `Gs` (qx_choose_then `ts`
    (map_every assume_tac o CONJUNCTS)))) >>
  qpat_assum `(?a. r0 = Abort Revert_abort a) \/ _`
    (DISJ_CASES_THEN2 (qx_choose_then `a` assume_tac)
      (qx_choose_then `ready_state` (CONJUNCTS_THEN2 assume_tac assume_tac)))
  >- suspend "setup_reject" >>
  suspend "guarded"
QED

Resume abi_decode_collision_run_mods[setup_reject]:
  qexistsl [`r0`, `Gs`, `ts`, `r0`, `Gs`, `ts`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (disj1_tac >> qexists `a` >>
    conj_tac >- first_assum ACCEPT_TAC >> simp_tac bool_ss []) >>
  qexistsl [`L`, `ids`, `id`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> disj2_tac >>
  qpat_x_assum `(?t u. r0 = OK t /\ _) \/ _` mp_tac >>
  qpat_assum `r0 = Abort Revert_abort a` (fn th =>
    simp_tac bool_ss [th, exec_result_distinct])
QED

Resume abi_decode_collision_run_mods[guarded]:
  qpat_assum `!t Gs ts. _ ==> _` (qspecl_then [`ready_state`, `Gs`, `ts`] mp_tac) >>
  (impl_tac >- (simp_tac pure_ss [GSYM CONJ_ASSOC] >>
    qpat_assum `(?output input. ~ready_state.vs_halted /\ _) /\ _` ACCEPT_TAC)) >>
  disch_then (mk_asm "guarded_entry") >>
  qpat_x_assum `(?t u. r0 = OK t /\ _) \/ _` mp_tac >>
  qpat_assum `r0 = OK ready_state` (fn th =>
    simp_tac bool_ss [th, exec_result_distinct, exec_result_11]) >>
  disch_then (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends start ready` by
    (irule abi_encoder_straight_extends >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm "guarded_entry" (fn th =>
    let
      val producer = Q.INST [`V` |-> `\H. valid_horizon cx st0 H es1.storage_trace`]
        (INST_TYPE [alpha |-> ``:256``]
          (SPEC_ALL abi_decode_guarded_to_buf_cut_selected))
      val reordered = MATCH_MP decode_guarded_handoff_first
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
  >- suspend "stop_at_cut" >>
  suspend "revert_before_cut"
QED

Resume abi_decode_collision_run_mods[stop_at_cut]:
  disj1_tac >> qexistsl [`v`, `w`] >>
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
     metis_tac[abi_decode_cut_prefix_run, exec_result_distinct]) >>
  `(?k. run_from k ctx (frag_relabel_observer start final L ids func id)
     (s with vs_current_bb := L) = Halt (stop_view w))` suffices_by
    (disch_then (qx_choose_then `fuel_all` assume_tac) >>
     qexists `fuel_all` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `local_prefix _ _ (L,LENGTH ready.cs_current_insts) _ u` mp_tac >>
  qpat_assum `run_from _ _ _ u = Halt (stop_view w)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[abi_decode_cut_prefix_run, exec_result_distinct]
QED

Resume abi_decode_collision_run_mods[revert_before_cut]:
  disj2_tac >> qexistsl [`v`, `w`] >>
  `(?k. run_from k ctx (frag_relabel_observer start final L ids func id)
     (s with vs_current_bb := L) = Abort Revert_abort w)` suffices_by
    (disch_then (qx_choose_then `fuel_all` assume_tac) >>
     qexists `fuel_all` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `local_prefix _ _ (L,LENGTH ready.cs_current_insts) _ u` mp_tac >>
  qpat_assum `run_from fuel _ _ u = Abort Revert_abort w` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[abi_decode_cut_prefix_run, exec_result_distinct]
QED

Finalise abi_decode_collision_run_mods[local]

Theorem decode_regular_guarded[local]:
  ^regular_guarded_statement
Proof
  rpt gen_tac >>
  mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] abi_decode_guarded_to_buf_joint)) >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  pure_rewrite_tac [GSYM CONJ_ASSOC] >> disch_then ACCEPT_TAC
QED

Theorem abi_decode_run_cut_mods:
  ^run_statement
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (mk_asm "physical") (mk_asm "entry")) >>
  Cases_on `start.cs_blocks <> final.cs_blocks /\
            start.cs_current_bb = final.cs_current_bb`
  >- (mp_tac (SPEC_ALL abi_decode_collision_run_mods) >>
      (impl_tac >- (conj_tac >- (conj_tac >- asm "physical" ACCEPT_TAC >>
        asm "entry" ACCEPT_TAC) >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choose_then `r0` $ qx_choose_then `Gs` $ qx_choose_then `ts` $
        qx_choose_then `r` $ qx_choose_then `Gf` $ qx_choose_then `tnf` $
        CONJUNCTS_THEN2 (mk_asm "joint") (mk_asm "cut")) >>
      qexistsl [`r0`,`Gs`,`ts`,`r`,`Gf`,`tnf`] >>
      conj_tac >- asm "joint" ACCEPT_TAC >>
      disch_tac >> asm "cut" ACCEPT_TAC) >>
  qpat_x_assum `~(_ /\ _)` (SUBST1_TAC o EQF_INTRO) >>
  pure_rewrite_tac [IMP_CLAUSES, AND_CLAUSES] >>
  asm_x "entry" (CONJUNCTS_THEN2 (mk_asm "setup_pre") $
    CONJUNCTS_THEN2 (mk_asm "handoff") kall_tac) >>
  asm "setup_pre" (mp_tac o MATCH_MP (BETA_RULE
    (Q.INST [`V` |-> `\H. valid_horizon cx st0 H es1.storage_trace`]
      (SPEC_ALL abi_decode_caller_setup_origin_observed)))) >>
  disch_then (qx_choose_then `r0` $ qx_choose_then `Gs` $ qx_choose_then `ts` $
    (fn post => mk_asm "setup_post" post >>
      (CONJUNCTS_THEN2 kall_tac $ CONJUNCTS_THEN2 kall_tac $
       DISJ_CASES_THEN2 (qx_choose_then `a` assume_tac)
         (qx_choose_then `u` $ CONJUNCTS_THEN2
           (CONJUNCTS_THEN2 (mk_asm "setup_normal") (mk_asm "setup_ok"))
           (mk_asm "setup_origin"))) post))
  >- (qexistsl [`r0`,`Gs`,`ts`,`r0`,`Gs`,`ts`] >> conj_tac
      >- (pure_rewrite_tac [GSYM CONJ_ASSOC] >>
      asm "setup_post" (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM CONJ_ASSOC])) >>
      disj1_tac >> qexists `a` >> simp[]) >>
  asm "handoff" (qspecl_then [`u`,`Gs`,`ts`] mp_tac) >>
  (impl_tac >- (conj_tac >- asm "setup_ok" ACCEPT_TAC >> asm "setup_origin" ACCEPT_TAC)) >>
  disch_then (mp_tac o MATCH_MP (BETA_RULE
    (Q.INST [`V` |-> `\H. valid_horizon cx st0 H es1.storage_trace`]
      (SPEC_ALL decode_regular_guarded)))) >>
  disch_then (qx_choose_then `r` $ qx_choose_then `Gf` $ qx_choose_then `tnf` $
    mk_asm "guarded_post") >>
  qexistsl [`r0`,`Gs`,`ts`,`r`,`Gf`,`tnf`] >>
  conj_tac >- (pure_rewrite_tac [GSYM CONJ_ASSOC] >>
      asm "setup_post" (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM CONJ_ASSOC])) >>
  disj2_tac >> qexists `u` >>
  conj_tac >- asm "setup_normal" ACCEPT_TAC >>
  asm "guarded_post" ACCEPT_TAC
QED
