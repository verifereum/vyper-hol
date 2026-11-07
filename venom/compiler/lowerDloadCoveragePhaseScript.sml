Theory lowerDloadCoveragePhase
Ancestors
  lowerDloadPhaseBoundary lowerDloadControlPosition
  venomExecSemantics venomExecProps venomState contextCodegenRel
  venomInst venomInstProps list rich_list arithmetic

Theorem ld_block_slice_fetch[local]:
  gb.bb_instructions = p ++ code ++ tail /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  t.vs_inst_idx = LENGTH p + n /\ n < LENGTH code ==>
  get_instruction gb t.vs_inst_idx = SOME (EL n code) /\
  active_inst gn (EL n code) t
Proof
  strip_tac >>
  `MEM gb gn.fn_blocks /\ gb.bb_label = t.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  conj_tac
  >- simp[get_instruction_def, EL_APPEND2, EL_APPEND1] >>
  simp[active_inst_def] >> qexists_tac `gb` >>
  simp[EL_APPEND2, EL_APPEND1]
QED

Theorem ld_block_slice_trace:
  !T R F J.
  gb.bb_instructions = p ++ code ++ tail /\
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  lookup_block t0.vs_current_bb gn.fn_blocks = SOME gb /\
  t0.vs_inst_idx = LENGTH p /\ T 0 = t0 /\ N <= LENGTH code /\
  (!h. h < N ==>
    (?b. lookup_block (T h).vs_current_bb gn.fn_blocks = SOME b /\
      get_instruction b (T h).vs_inst_idx = SOME (J h)) /\
    step_inst (F h) CT (J h) (T h) = OK (R h) /\
    T (SUC h) = (R h with vs_inst_idx := SUC (T h).vs_inst_idx)) ==>
  (!n. n <= N ==> (T n).vs_current_bb = t0.vs_current_bb /\
    (T n).vs_inst_idx = LENGTH p + n) /\
  (!h. h < N ==> J h = EL h code) /\
  (!n. n <= N /\ n < LENGTH code ==> active_inst gn (EL n code) (T n))
Proof
  rpt gen_tac >> strip_tac >> rename1 `Ts 0 = t0` >>
  `!n. n <= N ==> (Ts n).vs_current_bb = t0.vs_current_bb /\
    (Ts n).vs_inst_idx = LENGTH p + n` by
    (Induct >- gvs[] >> strip_tac >>
     `n < N /\ n <= N /\ n < LENGTH code` by decide_tac >>
     first_x_assum drule >> strip_tac >>
     qpat_assum `!h. h < N ==> _` (qspec_then `n` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `lookup_block (Ts n).vs_current_bb gn.fn_blocks = SOME gb` by metis_tac[] >>
     `get_instruction gb (Ts n).vs_inst_idx = SOME (EL n code)` by
       (drule_all ld_block_slice_fetch >> simp[]) >>
     `J n = EL n code` by metis_tac[optionTheory.SOME_11] >>
     `~is_terminator (J n).inst_opcode` by
       (gvs[EVERY_EL] >> metis_tac[]) >>
     `(R n).vs_current_bb = (Ts n).vs_current_bb` by
       metis_tac[step_preserves_control_flow] >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!h. h < N ==> _` (qspec_then `h` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `h <= N /\ h < LENGTH code` by decide_tac >>
      qpat_assum `!n. n <= N ==> _` (qspec_then `h` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `lookup_block (Ts h).vs_current_bb gn.fn_blocks = SOME gb` by metis_tac[] >>
      drule_all ld_block_slice_fetch >> metis_tac[optionTheory.SOME_11]) >>
  rpt strip_tac >>
  qpat_assum `!n. n <= N ==> _` drule >> strip_tac >>
  irule (cj 2 ld_block_slice_fetch) >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`p`,`tail`] >> simp[]
QED

Theorem ld_block_slice_target_prefix:
  !T Q R F J.
  gb.bb_instructions = p ++ code ++ tail /\
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  lookup_block t0.vs_current_bb gn.fn_blocks = SOME gb /\
  t0.vs_inst_idx = LENGTH p /\ T 0 = t0 /\ Q 0 = u0 /\
  N <= LENGTH code /\
  (!h. h < N ==>
    (?b. lookup_block (T h).vs_current_bb gn.fn_blocks = SOME b /\
       get_instruction b (T h).vs_inst_idx = SOME (J h)) /\
    step_inst (F h) CT (J h) (T h) = OK (R h) /\
    T (SUC h) = (R h with vs_inst_idx := SUC (T h).vs_inst_idx) /\
    Q (SUC h) = step_taint (J h) (T h) (R h) (Q h)) ==>
  (!n. n <= N ==>
    ld_target_prefix CT code t0 u0 n (T n) (Q n) /\
    (T n).vs_current_bb = t0.vs_current_bb /\
    (T n).vs_inst_idx = LENGTH p + n) /\
  (!h. h < N ==> J h = EL h code) /\
  (!n. n <= N /\ n < LENGTH code ==>
    active_inst gn (EL n code) (T n))
Proof
  map_every qx_gen_tac [`Ts`,`Q`,`R`,`Fs`,`J`] >> strip_tac >>
  `(!n. n <= N ==> (Ts n).vs_current_bb = t0.vs_current_bb /\
      (Ts n).vs_inst_idx = LENGTH p + n) /\
   (!h. h < N ==> J h = EL h code) /\
   (!n. n <= N /\ n < LENGTH code ==> active_inst gn (EL n code) (Ts n))` by
    (irule ld_block_slice_trace >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`CT`,`Fs`,`R`] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!n. n <= N ==> ld_target_prefix CT code t0 u0 n (Ts n) (Q n)` by
    (Induct
     >- simp[ld_target_prefix_rules] >>
     strip_tac >> `n < N /\ n <= N /\ n < LENGTH code` by decide_tac >>
     first_x_assum drule >> strip_tac >>
     qpat_assum `!h. h < N ==> _ /\ _` (qspec_then `n` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `J n = EL n code` by metis_tac[] >>
     qpat_x_assum `Ts (SUC n) = _` SUBST1_TAC >>
     qpat_x_assum `Q (SUC n) = _` SUBST1_TAC >>
     qpat_assum `J n = _` SUBST1_TAC >>
     irule (cj 2 ld_target_prefix_rules) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED
