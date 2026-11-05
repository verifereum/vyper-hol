(* Proof-only lifting with independent Abort observations. *)
Theory acFunctionSimProofs
Ancestors
  passSimulationDefs execEquivParamBase venomExecProofs
  venomExecSemantics venomState venomInst execEquivParamDefs stateEquiv list

Theorem ac_lookup_block_map[local]:
  !lbl bbs bt.
    (!bb. (bt bb).bb_label = bb.bb_label) ==>
    lookup_block lbl (MAP bt bbs) =
      OPTION_MAP bt (lookup_block lbl bbs)
Proof
  gen_tac >> Induct >>
  simp[lookup_block_def, listTheory.FIND_thm] >>
  rw[] >> res_tac >> gvs[lookup_block_def] >> metis_tac[]
QED

Theorem ac_block_sim_function_inv_cross:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (R_abort : venom_state -> venom_state -> bool) bt fn
   (Inv : venom_state -> bool).
    valid_state_rel R_ok R_term /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s s'.
       MEM bb fn.fn_blocks /\ Inv s /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (!bb fuel ctx s s'.
       MEM bb (function_map_transform bt fn).fn_blocks /\ Inv s /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (!bb fuel ctx s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 /\ Inv s1 /\ Inv s2 ==>
       lift_result R_ok R_term R_abort (run_block fuel ctx bb s1)
         (run_block fuel ctx (bt bb) s2)) ==>
    !fuel ctx s.
      Inv s /\ s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term R_abort (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (function_map_transform bt fn) s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `fn' = function_map_transform bt fn` >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> drule_all vsr_R_ok_fields >> simp[]) >>
  qsuff_tac
    `!fuel ctx s1 s2.
       R_ok s1 s2 /\ Inv s1 /\ Inv s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term R_abort (run_blocks fuel ctx fn s1)
         (run_blocks fuel ctx fn' s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      simp[] >> disch_then irule >>
      irule vsr_R_ok_refl >> metis_tac[]) >>
  Induct_on `fuel` >> rw[]
  >- simp[run_blocks_def, lift_result_def] >>
  qpat_assum `!s1 s2. R_ok s1 s2 ==> (_ /\ _ /\ _)`
    (drule_then strip_assume_tac) >>
  once_rewrite_tac[run_blocks_unfold] >>
  simp[Abbr `fn'`, function_map_transform_def, ac_lookup_block_map] >>
  qabbrev_tac `fn' = function_map_transform bt fn` >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def] >>
  gvs[] >> rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM (bt bb) fn'.fn_blocks` by
    (simp[Abbr `fn'`, function_map_transform_def, MEM_MAP] >> metis_tac[]) >>
  `lift_result R_ok R_term R_abort (run_block fuel ctx bb s1)
     (run_block fuel ctx (bt bb) s2)` by metis_tac[] >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def] >>
  rename1 `R_ok t1 t2` >>
  `t1.vs_halted = t2.vs_halted` by metis_tac[] >>
  Cases_on `t1.vs_halted`
  >- (`t2.vs_halted` by metis_tac[] >>
      simp[lift_result_def] >> metis_tac[]) >>
  `~t2.vs_halted` by metis_tac[] >>
  `Inv t1 /\ Inv t2` by metis_tac[] >>
  `t1.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
  simp[] >>
  qpat_x_assum `!ctx s1 s2. R_ok s1 s2 /\ Inv s1 /\ Inv s2 /\
      s1.vs_inst_idx = 0 ==> _` (drule_all_then mp_tac) >>
  simp[Abbr `fn'`, function_map_transform_def]
QED
