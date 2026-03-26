(*
 * Pass Simulation Framework — Proofs
 *
 * TOP-LEVEL:
 *   lookup_block_map_proof       — label-preserving MAP commutes with lookup
 *   lift_result_refl_proof       — R_ok, R_term reflexive ⟹ lift_result reflexive
 *   lift_result_trans_proof      — R_ok, R_term transitive ⟹ lift_result transitive
 *   lift_result_weaken_proof     — covariant in both R_ok and R_term
 *   block_sim_function_proof     — relational block sim ⟹ function sim (general)
 *   block_sim_function_with_pred_proof — relational block sim with state predicate P
 *   same_state_to_rel_block_sim_proof — same-state → R-related (triangle combiner)
 *   block_sim_function_pointwise_proof — corollary: valid_state_rel + pointwise block sim
 *   block_sim_function_pointwise_reachable_proof — pointwise + reachability guard
 *   lift_result_implies_pass_correct_proof — same-fuel lift_result → pass_correct bridge
 *)

Theory passSimulationProofs
Ancestors
  passSimulationDefs execEquivParamProofs execEquivParamBase execEquivParamDefs
  stateEquivProps execEquivProps stateEquiv venomInst venomExecSemantics
  venomExecProofs
Libs
  listTheory

Theorem lookup_block_MEM[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> simp[lookup_block_def, listTheory.FIND_thm] >>
  rw[] >> disj2_tac >> first_x_assum irule >> fs[lookup_block_def] >>
  metis_tac[]
QED

Theorem lookup_block_map_proof:
  !lbl bbs bt.
    (!bb. (bt bb).bb_label = bb.bb_label) ==>
    lookup_block lbl (MAP bt bbs) =
      OPTION_MAP bt (lookup_block lbl bbs)
Proof
  gen_tac >> Induct >>
  simp[lookup_block_def, listTheory.FIND_thm] >>
  rw[] >> res_tac >> fs[lookup_block_def]
QED

Theorem lift_result_refl_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
    (!s. R_ok s s) /\ (!s. R_term s s) ==>
    !r. lift_result R_ok R_term r r
Proof
  rpt strip_tac >> Cases_on `r` >> simp[lift_result_def]
QED

Theorem lift_result_trans_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) ==>
    !r1 r2 r3. lift_result R_ok R_term r1 r2 /\
               lift_result R_ok R_term r2 r3 ==>
               lift_result R_ok R_term r1 r3
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  fs[lift_result_def] >> metis_tac[]
QED

(* lift_result is covariant in both R_ok and R_term. *)
Theorem lift_result_weaken_proof:
  !(R1 : venom_state -> venom_state -> bool)
   (R2 : venom_state -> venom_state -> bool)
   (R1' : venom_state -> venom_state -> bool)
   (R2' : venom_state -> venom_state -> bool).
    (!s1 s2. R1 s1 s2 ==> R1' s1 s2) /\
    (!s1 s2. R2 s1 s2 ==> R2' s1 s2) ==>
    !r1 r2. lift_result R1 R2 r1 r2 ==>
            lift_result R1' R2' r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >>
  fs[lift_result_def] >> metis_tac[]
QED

(* Relational block sim ⟹ function sim. Most general lifting theorem.
   Per-block sim takes R-related states directly. No triangle composition,
   no valid_state_rel. Minimal R requirements: reflexivity, R_ok ⊆ R_term,
   and control-flow field agreement.
   vs_inst_idx = 0 precondition: 1:N expansion changes block length, so
   simulation is false at arbitrary idx (see counterexampleScript.sml). *)
Theorem block_sim_function_proof:
  !R_ok R_term bt fn.
    (!s. R_ok s s) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_halted = s2.vs_halted) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s1 s2.
        R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s1 = Error e) \/
        lift_result R_ok R_term
          (run_block fuel ctx bb s1)
          (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term
        (run_function fuel ctx fn s)
        (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  qsuff_tac
    `!fuel ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_function fuel ctx fn s1 = Error e) \/
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx (function_map_transform bt fn) s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      simp[])
  >>
  Induct_on `fuel` >> rw[]
  >- (DISJ1_TAC >> simp[run_function_def])
  >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- (DISJ1_TAC >> gvs[])
  >>
  gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  first_x_assum (qspec_then `bb` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s1`, `s2`] mp_tac) >> simp[] >>
  strip_tac
  >- (DISJ1_TAC >> qexists_tac `e` >> simp[])
  >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted` >> fs[] >>
    gvs[lift_result_def, function_map_transform_def] >>
    `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
      metis_tac[run_block_OK_inst_idx_0] >>
    first_x_assum irule >> metis_tac[]
  )
QED

(* Like block_sim_function_proof but R_ok reflexivity is conditional on
   a state predicate P. P must be preserved by block execution when R_ok holds.
   Useful when per-block sim requires a condition (e.g. calldata length bound)
   that is maintained across blocks. *)
Theorem block_sim_function_with_pred_proof:
  !P R_ok R_term bt fn.
    (!s. P s ==> R_ok s s) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_halted = s2.vs_halted) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s1 s2 s1' s2'.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 /\ P s1 /\
       run_block fuel ctx bb s1 = OK s1' /\
       run_block fuel ctx (bt bb) s2 = OK s2' /\
       R_ok s1' s2' ==>
       P s1') /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s1 s2.
        R_ok s1 s2 /\ P s1 /\ s1.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s1 = Error e) \/
        lift_result R_ok R_term
          (run_block fuel ctx bb s1)
          (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      P s /\ s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term
        (run_function fuel ctx fn s)
        (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  qsuff_tac
    `!fuel ctx s1 s2. R_ok s1 s2 /\ P s1 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_function fuel ctx fn s1 = Error e) \/
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx (function_map_transform bt fn) s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      metis_tac[])
  >>
  Induct_on `fuel` >> rw[]
  >- (DISJ1_TAC >> simp[run_function_def])
  >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- (DISJ1_TAC >> gvs[])
  >>
  gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `(?e. run_block fuel ctx bb s1 = Error e) \/
   lift_result R_ok R_term
     (run_block fuel ctx bb s1)
     (run_block fuel ctx (bt bb) s2)` by metis_tac[] >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted` >> fs[] >>
    gvs[lift_result_def, function_map_transform_def] >>
    `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
      metis_tac[run_block_OK_inst_idx_0] >>
    `P v` by (
      qpat_x_assum `!bb fuel ctx s1 s2 s1' s2'. _ ==> P s1'`
        (qspecl_then [`bb`, `fuel`, `ctx`, `s1`, `s2`, `v`, `v'`] mp_tac) >>
      simp[]) >>
    qpat_x_assum `!ctx' s1' s2'. _ ==> _ \/ lift_result _ _ (run_function _ _ fn _) _`
      (qspecl_then [`ctx`, `v`, `v'`] mp_tac) >> simp[]
  )
QED

(* Triangle combiner: same-state per-block sim + valid_state_rel ⟹
   R-related per-block sim. Lets existing passes (which prove same-state
   block sim) use block_sim_function without changing their proofs.
   Composes same-code preservation (run_block_preserves_R) with
   diff-code simulation via lift_result_trans. *)
Theorem same_state_to_rel_block_sim_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn bb bt_bb.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb inst x. MEM bb fn.fn_blocks /\
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    MEM bb fn.fn_blocks /\
    (!fuel ctx s. s.vs_inst_idx = 0 ==>
      (?e. run_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term (run_block fuel ctx bb s)
                               (run_block fuel ctx bt_bb s))
  ==>
    !fuel ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
      (?e. run_block fuel ctx bb s1 = Error e) \/
      lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx bt_bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  `!fuel ctx bb' s1 s2.
     MEM bb' fn.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term (run_block fuel ctx bb' s1)
                              (run_block fuel ctx bb' s2)` by
    (match_mp_tac (cj 1 run_block_preserves_R_proof) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `lift_result R_ok R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx bb s2)` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[vsr_R_ok_fields] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `s2`] mp_tac) >> simp[] >>
  strip_tac
  >- (
    Cases_on `run_block fuel ctx bb s1` >> gvs[lift_result_def] >>
    DISJ1_TAC >> metis_tac[]
  )
  >>
  DISJ2_TAC >>
  irule lift_result_trans_proof >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `run_block fuel ctx bb s2` >> simp[]
QED

(* Pointwise version: per-block sim proved on a single state (not R-related pair).
   Corollary of block_sim_function_proof + same_state_to_rel_block_sim_proof.
   Requires valid_state_rel, R_ok/R_term transitivity, and operand condition
   (the triangle bridges from same-state to R-related block sim internally). *)
Theorem block_sim_function_pointwise_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s = Error e) \/
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac block_sim_function_proof >> rpt conj_tac
  >- (irule vsr_R_ok_refl >> metis_tac[])
  >- (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[])
  >- (rpt strip_tac >> imp_res_tac
        (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields))
  >- first_assum ACCEPT_TAC
  >> rpt strip_tac >>
  irule same_state_to_rel_block_sim_proof >>
  simp[] >> metis_tac[]
QED

(* Helper: lookup_block at HD label finds HD *)
Triviality lookup_block_HD[local]:
  !bbs. bbs <> [] ==>
    lookup_block (HD bbs).bb_label bbs = SOME (HD bbs)
Proof
  Cases >> simp[lookup_block_def, listTheory.FIND_thm]
QED

(* Pointwise + reachability-guarded version of block_sim_function.
   Same-state per-block sim only required when bb = HD fn.fn_blocks (entry)
   or vs_prev_bb <> NONE (reachable non-entry). Uses valid_state_rel triangle
   internally. Guard maintained across iterations via run_block_ok_sets_prev_bb. *)
Theorem block_sim_function_pointwise_reachable_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        (bb = HD fn.fn_blocks \/ s.vs_prev_bb <> NONE) ==>
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      (fn.fn_blocks <> [] /\
       s.vs_current_bb = (HD fn.fn_blocks).bb_label \/
       s.vs_prev_bb <> NONE) ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx /\
     s1.vs_prev_bb = s2.vs_prev_bb` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields)) >>
  `!fuel ctx bb s1 s2.
     MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term (run_block fuel ctx bb s1)
                              (run_block fuel ctx bb s2)` by
    (match_mp_tac (cj 1 run_block_preserves_R_proof) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qsuff_tac
    `!fuel ctx s1 s2.
       R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
       (fn.fn_blocks <> [] /\
        s1.vs_current_bb = (HD fn.fn_blocks).bb_label \/
        s1.vs_prev_bb <> NONE) ==>
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx (function_map_transform bt fn) s2)`
  >- (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
    simp[] >>
    disch_then irule >>
    irule vsr_R_ok_refl >> metis_tac[]
  )
  >>
  Induct_on `fuel`
  >- (rw[] >> simp[run_function_def, function_map_transform_def, lift_result_def])
  >>
  rpt gen_tac >> disch_tac >>
  `R_ok s1 s2` by metis_tac[] >>
  `s1.vs_inst_idx = 0` by metis_tac[] >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks` >>
  gvs[lift_result_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `s2.vs_prev_bb = s1.vs_prev_bb` by metis_tac[] >>
  (* Guard for per-block sim: s2.vs_prev_bb = NONE ==> bb = HD fn.fn_blocks *)
  `s2.vs_prev_bb = NONE ==> bb = HD fn.fn_blocks` by (
    strip_tac >>
    `s1.vs_prev_bb = NONE` by metis_tac[] >>
    `fn.fn_blocks <> [] /\ s2.vs_current_bb = (HD fn.fn_blocks).bb_label`
      by metis_tac[] >>
    `lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks =
     SOME (HD fn.fn_blocks)` by simp[lookup_block_HD] >>
    gvs[]
  ) >>
  (* Triangle: run_block bb s1 ~ run_block bb s2 ~ run_block (bt bb) s2 *)
  `lift_result R_ok R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qexists_tac `run_block fuel ctx bb s2` >>
    conj_tac >- metis_tac[] >>
    first_x_assum (qspec_then `bb` mp_tac) >> simp[] >>
    disch_then irule >> metis_tac[]
  ) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def] >>
  (* Both OK: recurse. Guard maintained via run_block_ok_sets_prev_bb *)
  `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
  Cases_on `v.vs_halted` >> fs[] >>
  gvs[lift_result_def, function_map_transform_def] >>
  `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
    metis_tac[run_block_OK_inst_idx_0] >>
  `v.vs_prev_bb <> NONE` by metis_tac[run_block_ok_sets_prev_bb] >>
  `v'.vs_prev_bb <> NONE` by metis_tac[] >>
  first_x_assum irule >>
  metis_tac[]
QED

(* Bridge: same-fuel lift_result → pass_correct.
   Requires fuel determinism for both executions (when an execution terminates
   at two different fuel values, the results are equal).
   run_function_fuel_mono (in rtaCorrectnessProof) provides this for
   no_invoke_in_function; a general version is future work. *)
Triviality result_equiv_terminates:
  !fresh r1 r2. result_equiv fresh r1 r2 ==>
    (terminates r1 <=> terminates r2)
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[result_equiv_def, terminates_def]
QED

Theorem lift_result_implies_pass_correct_proof:
  !fresh exec1 exec2.
    (!fuel. result_equiv fresh (exec1 fuel) (exec2 fuel)) /\
    (!fuel fuel'. terminates (exec1 fuel) /\ terminates (exec1 fuel') ==>
                  exec1 fuel = exec1 fuel') /\
    (!fuel fuel'. terminates (exec2 fuel) /\ terminates (exec2 fuel') ==>
                  exec2 fuel = exec2 fuel')
  ==>
    pass_correct fresh exec1 exec2
Proof
  rw[pass_correct_def] >> (
    metis_tac[result_equiv_terminates]
  )
QED
