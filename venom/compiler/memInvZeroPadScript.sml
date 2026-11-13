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

Theorem gas_prefix_take_pad[local]:
  !n l N. n <= LENGTH l + N ==>
    gas_prefix n l = TAKE n (l ++ REPLICATE N 0w)
Proof
  rw[gas_prefix_def, LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_APPEND,
     LENGTH_REPLICATE] >>
  rw[EL_TAKE, EL_APPEND_EQN, EL_REPLICATE, LENGTH_REPLICATE]
QED

Theorem gas_replay_at_zero_pad[local]:
  !n f s N.
    gas_replay_at n f s /\ n <= LENGTH s.vs_gas_readings + N ==>
    lift_result
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = a with vs_gas_readings :=
                   DROP n (s.vs_gas_readings ++ REPLICATE N 0w))
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = a with vs_gas_readings :=
                   DROP n (s.vs_gas_readings ++ REPLICATE N 0w))
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = a with vs_gas_readings :=
                   DROP n (s.vs_gas_readings ++ REPLICATE N 0w))
      (f s)
      (f (s with vs_gas_readings := s.vs_gas_readings ++ REPLICATE N 0w))
Proof
  rw[gas_replay_at_def] >>
  first_x_assum (qspec_then
    `DROP n (s.vs_gas_readings ++ REPLICATE N 0w)` mp_tac) >>
  `gas_prefix n s.vs_gas_readings ++
   DROP n (s.vs_gas_readings ++ REPLICATE N 0w) =
   s.vs_gas_readings ++ REPLICATE N 0w` by
    (qspecl_then [`n`, `s.vs_gas_readings`, `N`] mp_tac gas_prefix_take_pad >>
     simp[]) >>
  simp[]
QED

Theorem append_replicate_assoc[local]:
  l ++ REPLICATE a x ++ REPLICATE b x = l ++ REPLICATE (a + b) x
Proof
  rewrite_tac[GSYM APPEND_ASSOC, REPLICATE_APPEND]
QED

(* KEY LEMMA: a replayable function that ends OK from zero-padded readings
   ends OK from the unpadded ones, in the same state up to padding. *)
Theorem zero_pad_replay_ok[local]:
  !n m f s j t'.
    gas_replay_at n f s /\
    gas_replay_at m f
      (s with vs_gas_readings := s.vs_gas_readings ++ REPLICATE j 0w) /\
    f (s with vs_gas_readings := s.vs_gas_readings ++ REPLICATE j 0w) =
      OK t' ==>
    ?s' j'. f s = OK s' /\
      t' = s' with vs_gas_readings := s'.vs_gas_readings ++ REPLICATE j' 0w
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `f`, `s`, `j + (n + m)`] mp_tac gas_replay_at_zero_pad >>
  impl_tac >- simp[] >>
  qspecl_then [`m`, `f`,
    `s with vs_gas_readings := s.vs_gas_readings ++ REPLICATE j 0w`,
    `n + m`] mp_tac gas_replay_at_zero_pad >>
  impl_tac >- simp[] >>
  simp[append_replicate_assoc, AC ADD_ASSOC ADD_COMM] >>
  Cases_on `f (s with vs_gas_readings :=
              s.vs_gas_readings ++ REPLICATE (j + (n + m)) 0w)` >>
  gvs[lift_result_def, AC ADD_ASSOC ADD_COMM] >>
  Cases_on `f s` >> gvs[lift_result_def, AC ADD_ASSOC ADD_COMM] >>
  rpt strip_tac >>
  rename1 `f s = OK a` >>
  `n = m` by
    (qpat_x_assum `t' with vs_gas_readings := _ = a with vs_gas_readings := _`
       (mp_tac o Q.AP_TERM `\z. LENGTH z.vs_gas_readings`) >>
     simp[LENGTH_DROP]) >>
  gvs[] >> qexists_tac `j - (m - LENGTH s.vs_gas_readings)` >>
  gvs[venom_state_component_equality, DROP_APPEND]
QED

(* ===== Steps, block entries and reachability ===== *)

Theorem step_inst_zero_pad[local]:
  step_inst fuel ctx inst
    (s with vs_gas_readings := s.vs_gas_readings ++ REPLICATE j 0w) =
    OK t' ==>
  ?s' j'. step_inst fuel ctx inst s = OK s' /\
    t' = s' with vs_gas_readings := s'.vs_gas_readings ++ REPLICATE j' 0w
Proof
  strip_tac >>
  `gas_replay (step_inst fuel ctx inst) s /\
   gas_replay (step_inst fuel ctx inst)
     (s with vs_gas_readings := s.vs_gas_readings ++ REPLICATE j 0w)` by
    simp[gas_replay_fuel] >>
  fs[gas_replay_def] >>
  qspecl_then [`n`, `n'`, `step_inst fuel ctx inst`, `s`, `j`, `t'`]
    mp_tac zero_pad_replay_ok >>
  simp[]
QED

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

Theorem active_inst_gas_readings[local]:
  active_inst fn inst (s with vs_gas_readings := gs) <=> active_inst fn inst s
Proof
  simp[active_inst_def]
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
      qexistsl_tac [`s0`, `j`] >> gvs[active_inst_gas_readings] >>
      irule (cj 1 raw_reachable_rules) >> simp[] >> metis_tac[])
  >- (strip_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[active_inst_gas_readings] >>
      drule step_inst_zero_pad >>
      disch_then (qx_choosel_then [`next`, `pad`] strip_assume_tac) >> gvs[] >>
      qexistsl_tac [`next with vs_inst_idx := SUC s.vs_inst_idx`, `pad`] >>
      simp[] >> irule (cj 2 raw_reachable_rules) >>
      fs[active_inst_def] >> metis_tac[])
  >- (strip_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[active_inst_gas_readings] >>
      drule step_inst_zero_pad >>
      disch_then (qx_choosel_then [`next`, `pad`] strip_assume_tac) >> gvs[] >>
      drule enters_block_readings_cong >> strip_tac >> gvs[] >>
      qexistsl_tac [`s0`, `pad`] >> gvs[active_inst_gas_readings] >>
      irule (cj 3 raw_reachable_rules) >> fs[active_inst_def] >> metis_tac[]) >>
  strip_tac >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[active_inst_gas_readings, gas_setup_callee] >>
  rename1 `setup_callee callee args s0 = SOME cs0` >>
  `cs0.vs_gas_readings = s0.vs_gas_readings` by
    metis_tac[gas_setup_callee_readings] >>
  drule enters_block_readings_cong >> strip_tac >> gvs[] >>
  qexistsl_tac [`s0'`, `j'`] >> gvs[active_inst_gas_readings] >>
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
