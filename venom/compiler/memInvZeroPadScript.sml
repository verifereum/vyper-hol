(*
 * Zero padding of the GAS readings keeps the memory invariants.
 *
 * GAS reads 0w from an exhausted reading list (exec_gas), so the run from
 * readings l ++ REPLICATE j 0w visits the states of the run from l, each
 * with zeros appended to its remaining readings.  A memory fact that does
 * not look at the readings therefore carries over.
 *
 * TOP-LEVEL:
 *   mem_inv_zero_pad        - mem_inv M survives zero padding when M
 *                             ignores the readings
 *   o1_lowered_inv_zero_pad - o1_lowered_inv survives zero padding
 *)
Theory memInvZeroPad
Ancestors
  gasOracleReplay contextRawReachable contextCodegenRel unitMemInv
  o1PassContract dftContractGas stateEquiv venomExecSemantics venomState
  list rich_list arithmetic

(* ===== Replays read the same prefix from padded readings ===== *)



(* KEY LEMMA: a replayable function that ends OK from zero-padded readings
   ends OK from the unpadded ones, in the same state up to padding. *)

(* ===== Steps, block entries and reachability ===== *)


Theorem enters_block_readings_cong[local]:
  enters_block fn (s with vs_gas_readings := gs) s1 ==>
  ?s0. enters_block fn s s0 /\ s0.vs_gas_readings = s.vs_gas_readings /\
       s1 = s0 with vs_gas_readings := gs
Proof
  rw[enters_block_def] >>
  qspecl_then [`bb.bb_instructions`, `s`] mp_tac gas_eval_phis >>
  simp[gas_replay_at_def] >> disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[lift_result_def] >>
  strip_tac >> rename1 `eval_phis s _ = OK a` >>
  qexists_tac `a with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  simp[venom_state_component_equality]
QED

Theorem raw_reachable_zero_pad[local]:
  !v ctx fn inst t. raw_reachable v ctx fn inst t ==>
  !vs j. v = vs with vs_gas_readings := vs.vs_gas_readings ++ REPLICATE j 0w ==>
  ?s j'. raw_reachable vs ctx fn inst s /\
         t = s with vs_gas_readings := s.vs_gas_readings ++ REPLICATE j' 0w
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> rpt strip_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `enters_block fn ent s1` >>
      qspecl_then [`fn`,
        `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>`,
        `vs.vs_gas_readings ++ REPLICATE j 0w`, `s1`] mp_tac
        (Q.GENL [`fn`, `s`, `gs`, `s1`] enters_block_readings_cong) >>
      impl_tac >- simp[Abbr `ent`] >> strip_tac >>
      qexistsl_tac [`s0`, `j`] >> gvs[dftGasToListReplayTheory.active_inst_gas_update] >>
      irule (cj 1 raw_reachable_rules) >> simp[] >> metis_tac[])
  >- (strip_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[dftGasToListReplayTheory.active_inst_gas_update] >>
      drule gasOracleReplayTheory.step_inst_zero_pad >>
      disch_then (qx_choosel_then [`next`, `pad`] strip_assume_tac) >> gvs[] >>
      qexistsl_tac [`next with vs_inst_idx := SUC s.vs_inst_idx`, `pad`] >>
      simp[] >> irule (cj 2 raw_reachable_rules) >>
      fs[active_inst_def] >> metis_tac[])
  >- (strip_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[dftGasToListReplayTheory.active_inst_gas_update] >>
      drule gasOracleReplayTheory.step_inst_zero_pad >>
      disch_then (qx_choosel_then [`next`, `pad`] strip_assume_tac) >> gvs[] >>
      drule enters_block_readings_cong >> strip_tac >> gvs[] >>
      qexistsl_tac [`s0`, `pad`] >> gvs[dftGasToListReplayTheory.active_inst_gas_update] >>
      irule (cj 3 raw_reachable_rules) >> fs[active_inst_def] >> metis_tac[]) >>
  strip_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[dftGasToListReplayTheory.active_inst_gas_update, gas_setup_callee] >>
  rename1 `setup_callee callee args s0 = SOME cs0` >>
  `cs0.vs_gas_readings = s0.vs_gas_readings` by
    metis_tac[gas_setup_callee_readings] >>
  drule enters_block_readings_cong >> strip_tac >> gvs[] >>
  qexistsl_tac [`s0'`, `j'`] >> gvs[dftGasToListReplayTheory.active_inst_gas_update] >>
  irule (cj 4 raw_reachable_rules) >> simp[] >> metis_tac[]
QED

(* ===== Memory invariants ===== *)

(* TOP-LEVEL: a memory fact that ignores the readings holds of every state
   reachable from zero-padded readings once it holds of those from vs. *)
Theorem mem_inv_zero_pad:
  (!fn inst s rs. M ctx fn inst (s with vs_gas_readings := rs) <=>
                  M ctx fn inst s) /\
  mem_inv M ctx vs ==>
  mem_inv M ctx
    (vs with vs_gas_readings := vs.vs_gas_readings ++ REPLICATE k 0w)
Proof
  rw[mem_inv_raw_reachable] >>
  drule raw_reachable_zero_pad >>
  disch_then (qspecl_then [`vs`, `k`] mp_tac) >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >> simp[]
QED

(* TOP-LEVEL: O1's lowered memory invariant survives zero padding. *)
Theorem o1_lowered_inv_zero_pad:
  o1_lowered_inv C vs ==>
  o1_lowered_inv C
    (vs with vs_gas_readings := vs.vs_gas_readings ++ REPLICATE k 0w)
Proof
  rw[o1_lowered_inv_def] >> qexists_tac `eom` >> simp[] >>
  irule mem_inv_zero_pad >> simp[]
QED
