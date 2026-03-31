(*
 * Pass Simulation Framework - Proofs
 *
 * TOP-LEVEL:
 *   lookup_block_map_proof       - label-preserving MAP commutes with lookup
 *   lift_result_refl_proof       - R_ok, R_term reflexive ==> lift_result reflexive
 *   lift_result_trans_proof      - R_ok, R_term transitive ==> lift_result transitive
 *   lift_result_weaken_proof     - covariant in both R_ok and R_term
 *   block_sim_function_proof     - relational block sim ==> function sim (general)
 *   block_sim_function_with_pred_proof - relational block sim with state predicate P
 *   same_state_to_rel_block_sim_proof - same-state to R-related (triangle combiner)
 *   block_sim_function_pointwise_proof - corollary: valid_state_rel + pointwise block sim
 *   block_sim_function_pointwise_reachable_proof - pointwise + reachability guard
 *   block_sim_function_rel_proof - relational block sim ==> function sim (no valid_state_rel)
 *   two_state_block_sim_function_proof - two-state block sim, no operand condition
 *   block_sim_function_unconditional_proof - no error disjunct
 *   lift_result_mono_proof       - monotonicity for lift_result
 *   block_sim_function_inv_proof - invariant-carrying (operand agree on fn and fn')
 *   block_sim_function_inv_rbpr_proof - invariant + direct run_block_preserves_R
 *   block_sim_function_inv_cross_proof - invariant + single cross-state obligation
 *   block_sim_function_error_proof - error disjunct + block_inv stable under R_ok
 *   block_sim_function_error_bb_proof - error + vs_current_bb = bb.bb_label
 *   lift_result_implies_pass_correct_proof - same-fuel lift_result to pass_correct bridge
 *   block_sim_function_dual_ctx_proof - per-block sim with different ctx + callee IH
 *)

Theory passSimulationProofs
Ancestors
  passSimulationDefs execEquivParamProofs execEquivParamBase execEquivParamDefs
  stateEquivProps execEquivProps stateEquiv venomInst venomExecSemantics
  venomExecProofs venomWf
Libs
  listTheory indexedListsTheory

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




(* Backward compatibility: same-state per-block sim + valid_state_rel →
   R-related per-block sim. Packages the triangle composition for one block.
   Lets existing passes (which prove same-state block sim) use
   block_sim_function_rel without changing their per-block proofs. *)

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
  (* Same-code R_ok preservation (universal form) *)
  `!fuel ctx bb' s1 s2.
     MEM bb' fn.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term (run_block fuel ctx bb' s1)
                              (run_block fuel ctx bb' s2)` by
    (match_mp_tac (cj 1 run_block_preserves_R_proof) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  (* Same-code: run_block bb s1 ~ run_block bb s2 *)
  `lift_result R_ok R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx bb s2)` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by
    metis_tac[vsr_R_ok_fields] >>
  (* Per-block sim on s2 *)
  first_x_assum (qspecl_then [`fuel`, `ctx`, `s2`] mp_tac) >> simp[] >>
  strip_tac
  >- (
    (* Error case: run_block bb s2 = Error e *)
    Cases_on `run_block fuel ctx bb s1` >> gvs[lift_result_def] >>
    DISJ1_TAC >> metis_tac[]
  )
  >>
  (* Compose triangle: s1 ~R~ s2 (same-code) then s2 ~R~ bt_bb s2 *)
  DISJ2_TAC >>
  irule lift_result_trans_proof >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `run_block fuel ctx bb s2` >> simp[]
QED

(* Per-fn-block sim → function sim via valid_state_rel triangle.
   Corollary of block_sim_function_rel_proof + same_state_to_rel_block_sim_proof.
   Operand condition: fn's blocks don't read variables that disagree under R_ok.
   vs_inst_idx = 0 precondition: required because 1:N expansion (FLAT) changes
   block length; false at arbitrary idx (see counterexampleScript.sml). *)
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

(* Alias for backward compatibility *)
Theorem block_sim_function_rel_proof =
  block_sim_function_proof

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
  match_mp_tac block_sim_function_rel_proof >> rpt conj_tac
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

(* Two-state block sim → function sim. Unlike block_sim_function, the
   per-block sim takes two RELATED states (R_ok s1 s2) instead of one.
   This eliminates the operand condition and the triangle composition,
   since the per-block hypothesis directly gives the needed cross-state
   cross-code result. Useful when the operand condition doesn't hold
   globally (e.g., remove_unused where NOP'd vars may be operands in
   other blocks). *)
Theorem two_state_block_sim_function_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s1 s2.
        R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s1 = Error e) \/
        lift_result R_ok R_term (run_block fuel ctx bb s1)
                                 (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields)) >>
  (* Strengthen: work with R_ok s1 s2 /\ idx=0 *)
  qsuff_tac
    `!fuel ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_function fuel ctx fn s1 = Error e) \/
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx (function_map_transform bt fn) s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      impl_tac >- (conj_tac >- (irule vsr_R_ok_refl >> metis_tac[]) >> simp[]) >>
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
  (* Two-state per-block hypothesis: directly gives cross-state cross-code *)
  first_x_assum (qspec_then `bb` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s1`, `s2`] mp_tac) >> simp[] >>
  strip_tac
  >- (
    (* Error case *)
    DISJ1_TAC >> qexists_tac `e` >> simp[]
  )
  >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    (* Both OK, not halted: recurse via IH *)
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted` >> fs[] >>
    gvs[lift_result_def, function_map_transform_def] >>
    `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
      metis_tac[run_block_OK_inst_idx_0] >>
    first_x_assum irule >> metis_tac[]
  )
  (* Remaining cases: Halt/Abort/IntRet/Error — closed by gvs *)
QED

(* Unconditional version: when per-block sim gives lift_result (no error
   disjunct), function-level sim also gives unconditional lift_result.
   Direct fuel induction (same structure as block_sim_function_proof). *)
Theorem block_sim_function_unconditional_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  (* Derive useful consequences of valid_state_rel *)
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields)) >>
  (* Same-code R_ok preservation *)
  `!fuel ctx bb s1 s2.
     MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term (run_block fuel ctx bb s1)
                              (run_block fuel ctx bb s2)` by
    (match_mp_tac (cj 1 run_block_preserves_R_proof) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* Strengthen: work with R_ok s1 s2 /\ idx=0 *)
  qsuff_tac
    `!fuel ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx (function_map_transform bt fn) s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      impl_tac >- (conj_tac >- (irule vsr_R_ok_refl >> metis_tac[]) >> simp[]) >>
      simp[])
  >>
  Induct_on `fuel` >> rw[]
  >- simp[run_function_def, lift_result_def]
  >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  (* Same-code: run_block bb s1 ~ run_block bb s2 *)
  `lift_result R_ok R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx bb s2)` by metis_tac[] >>
  (* Per-block: run_block bb s2 ~ run_block (bt bb) s2 (unconditional) *)
  `lift_result R_ok R_term (run_block fuel ctx bb s2)
                            (run_block fuel ctx (bt bb) s2)` by metis_tac[] >>
  (* Triangle: compose via transitivity *)
  sg `lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx (bt bb) s2)`
  >- (irule lift_result_trans_proof >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `run_block fuel ctx bb s2` >>
      simp[]) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    (* Both OK, not halted: recurse via IH *)
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted` >> fs[] >>
    gvs[lift_result_def, function_map_transform_def] >>
    `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
      metis_tac[run_block_OK_inst_idx_0] >>
    first_x_assum irule >> metis_tac[]
  )
  (* Remaining cases: Halt/Abort/IntRet/Error — closed by gvs *)
QED

(* Monotonicity: if R1 <= R2 and T1 <= T2, then lift_result R1 T1 <= lift_result R2 T2 *)
Theorem lift_result_mono_proof:
  !R1 R2 T1 T2 r1 r2.
    (!s1 s2. R1 s1 s2 ==> R2 s1 s2) /\
    (!s1 s2. T1 s1 s2 ==> T2 s1 s2) /\
    lift_result R1 T1 r1 r2 ==>
    lift_result R2 T2 r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[]
QED

(* --------------------------------------------------------------------------
   Invariant-Carrying Block Simulation
   --------------------------------------------------------------------------
   Per-block sim only holds when state invariant Inv is satisfied.
   Three variants:
   - _inv: operand agreement on both fn and fn'
   - _inv_rbpr: takes run_block_preserves_R on fn' directly
   - _inv_cross: single cross-state obligation (most general)
   -------------------------------------------------------------------------- *)

Theorem block_sim_function_inv_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn
   (Inv : venom_state -> bool).
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (* Invariant preserved by original block execution *)
    (!bb fuel ctx s s'.
       MEM bb fn.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (* Per-block sim holds under invariant *)
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        Inv s /\ s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (* Operand agreement on ORIGINAL fn *)
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (* Operand agreement on TRANSFORMED fn *)
    (!bb inst x.
       MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      Inv s /\ s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx fn' s)
Proof
  simp_tac std_ss [LET_THM] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `fn' = function_map_transform bt fn` >>
  (* Derive useful consequences of valid_state_rel *)
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields)) >>
  (* Same-code R_ok preservation on TRANSFORMED fn *)
  `!fuel ctx bb s1 s2.
     MEM bb fn'.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term (run_block fuel ctx bb s1)
                              (run_block fuel ctx bb s2)` by
    (match_mp_tac (cj 1 run_block_preserves_R_proof) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* Strengthen: R_ok s1 s2 /\ Inv s1 /\ idx=0 *)
  qsuff_tac
    `!fuel ctx s1 s2.
       R_ok s1 s2 /\ Inv s1 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx fn' s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      simp[] >> disch_then irule >>
      irule vsr_R_ok_refl >> metis_tac[])
  >>
  Induct_on `fuel` >> rw[]
  >- simp[run_function_def, lift_result_def]
  >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[Abbr `fn'`, function_map_transform_def, lookup_block_map_proof] >>
  qabbrev_tac `fn' = function_map_transform bt fn` >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM (bt bb) fn'.fn_blocks` by
    (simp[Abbr `fn'`, function_map_transform_def, MEM_MAP] >>
     metis_tac[]) >>
  (* Triangle: per-block + same-code *)
  `lift_result R_ok R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx (bt bb) s1)` by metis_tac[] >>
  `lift_result R_ok R_term (run_block fuel ctx (bt bb) s1)
                            (run_block fuel ctx (bt bb) s2)` by metis_tac[] >>
  sg `lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx (bt bb) s2)`
  >- (irule lift_result_trans_proof >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `run_block fuel ctx (bt bb) s1` >>
      simp[]) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    (* Both OK, not halted: recurse via IH *)
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted` >> fs[] >>
    gvs[lift_result_def, function_map_transform_def] >>
    `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
      metis_tac[run_block_OK_inst_idx_0] >>
    first_x_assum irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    metis_tac[]
  )
QED

(* Same as block_sim_function_inv, but takes run_block_preserves_R on the
   transformed function directly instead of deriving it from operand agreement.
   Strictly more general: works when the transform introduces fresh
   variables as operands. *)
Theorem block_sim_function_inv_rbpr_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn
   (Inv : venom_state -> bool).
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (* Invariant preserved by original block execution *)
    (!bb fuel ctx s s'.
       MEM bb fn.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (* Per-block sim holds under invariant *)
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        Inv s /\ s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (* Invariant preserved by transformed block execution *)
    (!bb fuel ctx s s'.
       MEM bb fn'.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (* run_block_preserves_R on TRANSFORMED fn -- caller provides directly *)
    (!fuel ctx bb s1 s2.
       MEM bb fn'.fn_blocks /\ R_ok s1 s2 /\
       Inv s1 /\ Inv s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx bb s2))
  ==>
    !fuel ctx s.
      Inv s /\ s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx fn' s)
Proof
  simp_tac std_ss [LET_THM] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `fn' = function_map_transform bt fn` >>
  (* Derive useful consequences of valid_state_rel *)
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields)) >>
  (* Strengthen: R_ok s1 s2 /\ Inv s1 /\ Inv s2 /\ idx=0 *)
  qsuff_tac
    `!fuel ctx s1 s2.
       R_ok s1 s2 /\ Inv s1 /\ Inv s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx fn' s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      simp[] >> disch_then irule >>
      irule vsr_R_ok_refl >> metis_tac[])
  >>
  Induct_on `fuel` >> rw[]
  >- simp[run_function_def, lift_result_def]
  >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[Abbr `fn'`, function_map_transform_def, lookup_block_map_proof] >>
  qabbrev_tac `fn' = function_map_transform bt fn` >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM (bt bb) fn'.fn_blocks` by
    (simp[Abbr `fn'`, function_map_transform_def, MEM_MAP] >>
     metis_tac[]) >>
  (* Triangle: per-block + same-code *)
  `lift_result R_ok R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx (bt bb) s1)` by metis_tac[] >>
  `lift_result R_ok R_term (run_block fuel ctx (bt bb) s1)
                            (run_block fuel ctx (bt bb) s2)` by metis_tac[] >>
  sg `lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx (bt bb) s2)`
  >- (irule lift_result_trans_proof >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `run_block fuel ctx (bt bb) s1` >>
      simp[]) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    (* Both OK, not halted: recurse via IH *)
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted` >> fs[] >>
    gvs[lift_result_def, function_map_transform_def] >>
    `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
      metis_tac[run_block_OK_inst_idx_0] >>
    first_x_assum irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    metis_tac[]
  )
QED

(* Cross-state variant: single cross-state per-block sim obligation.
   Strictly more general than both inv and rbpr. *)
Theorem block_sim_function_inv_cross_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn
   (Inv : venom_state -> bool).
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (* Invariant preserved by original block execution *)
    (!bb fuel ctx s s'.
       MEM bb fn.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (* Invariant preserved by transformed block execution *)
    (!bb fuel ctx s s'.
       MEM bb fn'.fn_blocks /\ Inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK s' /\ ~s'.vs_halted ==> Inv s') /\
    (* Cross-state per-block sim *)
    (!bb fuel ctx s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 /\
       Inv s1 /\ Inv s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      Inv s /\ s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx fn' s)
Proof
  simp_tac std_ss [LET_THM] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `fn' = function_map_transform bt fn` >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields)) >>
  (* Strengthen to 2-state IH *)
  qsuff_tac
    `!fuel ctx s1 s2.
       R_ok s1 s2 /\ Inv s1 /\ Inv s2 /\ s1.vs_inst_idx = 0 ==>
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx fn' s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      simp[] >> disch_then irule >>
      irule vsr_R_ok_refl >> metis_tac[])
  >>
  Induct_on `fuel` >> rw[]
  >- simp[run_function_def, lift_result_def]
  >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[Abbr `fn'`, function_map_transform_def, lookup_block_map_proof] >>
  qabbrev_tac `fn' = function_map_transform bt fn` >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM (bt bb) fn'.fn_blocks` by
    (simp[Abbr `fn'`, function_map_transform_def, MEM_MAP] >>
     metis_tac[]) >>
  (* Direct cross-state per-block sim -- no triangle needed *)
  `lift_result R_ok R_term (run_block fuel ctx bb s1)
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
    first_x_assum irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    metis_tac[]
  )
QED

(* --------------------------------------------------------------------------
   Error-Disjunct Invariant Block Simulation
   --------------------------------------------------------------------------
   Like inv family above but conclusion has Error disjunct.
   block_inv must be stable under R_ok. Two variants:
   - _error: basic, no vs_current_bb in handlers
   - _error_bb: strengthened, exposes vs_current_bb = bb.bb_label
   -------------------------------------------------------------------------- *)

Triviality lookup_block_label[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >> fs[]
QED

(* Strengthened: exposes s.vs_current_bb = bb.bb_label in handlers *)
Theorem block_sim_function_error_bb_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (block_inv : venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (* Per-block sim: block_inv + current_bb = bb.bb_label *)
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\ block_inv s /\
        s.vs_current_bb = bb.bb_label ==>
        (?e. run_block fuel ctx bb s = Error e) \/
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (* block_inv preserved: gets current_bb = bb.bb_label *)
    (!bb fuel ctx s v.
       MEM bb fn.fn_blocks /\ block_inv s /\ s.vs_inst_idx = 0 /\
       s.vs_current_bb = bb.bb_label /\
       run_block fuel ctx bb s = OK v ==> block_inv v) /\
    (* block_inv stable under R_ok *)
    (!s1 s2. R_ok s1 s2 /\ block_inv s1 ==> block_inv s2) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ block_inv s ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
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
       R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\ block_inv s1 ==>
       (?e. run_function fuel ctx fn s1 = Error e) \/
       lift_result R_ok R_term (run_function fuel ctx fn s1)
         (run_function fuel ctx (function_map_transform bt fn) s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      impl_tac >- (rpt conj_tac
        >- (irule vsr_R_ok_refl >> metis_tac[])
        >> first_assum ACCEPT_TAC) >>
      simp[])
  >>
  Induct_on `fuel` >> rw[]
  >- (DISJ1_TAC >> simp[run_function_def])
  >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  `block_inv s2` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- (DISJ1_TAC >> gvs[])
  >>
  gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] >>
  `lift_result R_ok R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx bb s2)` by metis_tac[] >>
  qpat_x_assum `!bb. MEM bb _ ==> _`
    (qspec_then `bb` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s2`] mp_tac) >> simp[] >>
  strip_tac
  >- (
    Cases_on `run_block fuel ctx bb s1` >> gvs[lift_result_def] >>
    DISJ1_TAC >> qexists_tac `e'` >> simp[]
  )
  >>
  sg `lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx (bt bb) s2)`
  >- (irule lift_result_trans_proof >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `run_block fuel ctx bb s2` >>
      simp[]) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted` >> fs[] >>
    gvs[lift_result_def, function_map_transform_def] >>
    `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
      metis_tac[run_block_OK_inst_idx_0] >>
    first_x_assum irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (* block_inv v: preserved at block boundary *)
    first_x_assum (qspecl_then [`bb`, `fuel`, `ctx`, `s1`, `v`] mp_tac) >>
    simp[]
  )
QED

(* Original version -- derives from bb version by dropping extra hyps *)
Theorem block_sim_function_error_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (block_inv : venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\ block_inv s ==>
        (?e. run_block fuel ctx bb s = Error e) \/
        lift_result R_ok R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb fuel ctx s v.
       MEM bb fn.fn_blocks /\ block_inv s /\ s.vs_inst_idx = 0 /\
       run_block fuel ctx bb s = OK v ==> block_inv v) /\
    (!s1 s2. R_ok s1 s2 /\ block_inv s1 ==> block_inv s2) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ block_inv s ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result R_ok R_term (run_function fuel ctx fn s)
                 (run_function fuel ctx (function_map_transform bt fn) s)
Proof
  rpt strip_tac
  \\ mp_tac block_sim_function_error_bb_proof
  \\ disch_then (qspecl_then [`R_ok`, `R_term`, `block_inv`, `bt`, `fn`] mp_tac)
  \\ `(!bb. MEM bb fn.fn_blocks ==>
        !fuel ctx s. s.vs_inst_idx = 0 /\ block_inv s /\
          s.vs_current_bb = bb.bb_label ==>
          (?e. run_block fuel ctx bb s = Error e) \/
          lift_result R_ok R_term (run_block fuel ctx bb s)
            (run_block fuel ctx (bt bb) s))` by
       metis_tac[]
  \\ `(!bb fuel ctx s v. MEM bb fn.fn_blocks /\ block_inv s /\
        s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
        run_block fuel ctx bb s = OK v ==> block_inv v)` by
       metis_tac[]
  \\ impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC)
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED

(* Bridge: same-fuel lift_result -> pass_correct.
   Requires fuel determinism for both executions (when an execution terminates
   at two different fuel values, the results are equal). *)
Triviality lift_result_terminates:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) r1 r2.
    lift_result R_ok R_term r1 r2 ==>
    (terminates r1 <=> terminates r2)
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def, terminates_def]
QED

Theorem lift_result_implies_pass_correct_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) exec1 exec2.
    (!fuel. lift_result R_ok R_term (exec1 fuel) (exec2 fuel)) /\
    (!fuel fuel'. terminates (exec1 fuel) /\ terminates (exec1 fuel') ==>
                  exec1 fuel = exec1 fuel') /\
    (!fuel fuel'. terminates (exec2 fuel) /\ terminates (exec2 fuel') ==>
                  exec2 fuel = exec2 fuel')
  ==>
    pass_correct R_ok R_term exec1 exec2
Proof
  rw[pass_correct_def] >> (
    metis_tac[lift_result_terminates]
  )
QED


(* ===== Dual-context module simulation ===== *)

(* Module-level simulation with different contexts.
   Proves that ALL function pairs (looked up by name from ctx1/ctx2)
   are related, given per-block simulation with a callee IH.

   The conclusion quantifies over all function pairs, so the fuel
   induction provides the callee IH at each step.

   When ctx1 = ctx2 with matching functions, this degenerates to
   block_sim_function_proof. *)
Theorem module_sim_dual_ctx_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) ctx1 ctx2.
    (!s. R_ok s s) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_halted = s2.vs_halted) /\
    (* Contexts have matching labels for corresponding functions *)
    (!fn_name fn1 fn2.
       lookup_function fn_name ctx1.ctx_functions = SOME fn1 /\
       lookup_function fn_name ctx2.ctx_functions = SOME fn2 ==>
       !lbl. IS_SOME (lookup_block lbl fn1.fn_blocks) <=>
             IS_SOME (lookup_block lbl fn2.fn_blocks)) /\
    (* Per-block sim with callee IH *)
    (!fn_name fn1 fn2 lbl bb1 bb2 fuel s1 s2.
       lookup_function fn_name ctx1.ctx_functions = SOME fn1 /\
       lookup_function fn_name ctx2.ctx_functions = SOME fn2 /\
       lookup_block lbl fn1.fn_blocks = SOME bb1 /\
       lookup_block lbl fn2.fn_blocks = SOME bb2 /\
       R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
       (* Callee IH: all functions in both contexts are related *)
       (!callee_name cfn1 cfn2 cs1 cs2.
          lookup_function callee_name ctx1.ctx_functions = SOME cfn1 /\
          lookup_function callee_name ctx2.ctx_functions = SOME cfn2 /\
          R_ok cs1 cs2 /\ cs1.vs_inst_idx = 0 ==>
          (?e. run_function fuel ctx1 cfn1 cs1 = Error e) \/
          lift_result R_ok R_term
            (run_function fuel ctx1 cfn1 cs1)
            (run_function fuel ctx2 cfn2 cs2))
       ==>
       (?e. run_block fuel ctx1 bb1 s1 = Error e) \/
       lift_result R_ok R_term
         (run_block fuel ctx1 bb1 s1)
         (run_block fuel ctx2 bb2 s2))
  ==>
    !fn_name fn1 fn2 fuel s1 s2.
      lookup_function fn_name ctx1.ctx_functions = SOME fn1 /\
      lookup_function fn_name ctx2.ctx_functions = SOME fn2 /\
      R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx1 fn1 s1 = Error e) \/
      lift_result R_ok R_term
        (run_function fuel ctx1 fn1 s1)
        (run_function fuel ctx2 fn2 s2)
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `fuel` >> rw[]
  >- (DISJ1_TAC >> simp[run_function_def])
  >>
  `s2.vs_current_bb = s1.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  (* Rewrite fn2 side to use s1.vs_current_bb *)
  qpat_x_assum `s2.vs_current_bb = _`
    (fn th => PURE_REWRITE_TAC[th]) >>
  Cases_on `lookup_block s1.vs_current_bb fn1.fn_blocks`
  >- (DISJ1_TAC >> gvs[])
  >>
  rename1 `lookup_block _ fn1.fn_blocks = SOME bb1` >>
  (* Get matching block from fn2 via label correspondence *)
  `IS_SOME (lookup_block s1.vs_current_bb fn2.fn_blocks)` by
    (qpat_assum `!fn_name fn1 fn2. _ ==> !lbl. _`
       (qspecl_then [`fn_name`, `fn1`, `fn2`] mp_tac) >>
     simp[] >>
     disch_then (qspec_then `s1.vs_current_bb` mp_tac) >>
     simp[optionTheory.IS_SOME_DEF]) >>
  fs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_block _ fn2.fn_blocks = SOME bb2` >>
  gvs[] >>
  (* Apply per-block hypothesis *)
  first_x_assum (qspecl_then
    [`fn_name`, `fn1`, `fn2`, `s1.vs_current_bb`,
     `bb1`, `bb2`, `fuel`, `s1`, `s2`] mp_tac) >> simp[] >>
  impl_tac
  >- ((* Discharge callee IH from induction hypothesis *)
      rpt gen_tac >> strip_tac >>
      first_x_assum irule >> metis_tac[])
  >>
  strip_tac
  >- (DISJ1_TAC >> qexists_tac `e` >> simp[])
  >>
  Cases_on `run_block fuel ctx1 bb1 s1` >>
  Cases_on `run_block fuel ctx2 bb2 s2` >>
  gvs[lift_result_def]
  >- (
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted` >> fs[] >>
    gvs[lift_result_def] >>
    `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
      metis_tac[run_block_OK_inst_idx_0] >>
    first_x_assum irule >> metis_tac[]
  )
QED
(* ===== Structural preservation for function_map_transform ===== *)

(* General theorem: function_map_transform preserves wf_function
   given per-block preconditions. *)
Theorem fmt_preserves_wf_function_proof:
  !bt fn.
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. bb_well_formed bb ==> bb_well_formed (bt bb)) /\
    (!bb. bb_well_formed bb ==> bb_succs (bt bb) = bb_succs bb) /\
    fn_inst_ids_distinct (function_map_transform bt fn)
    ==>
    wf_function fn ==> wf_function (function_map_transform bt fn)
Proof
  rw[wf_function_def, function_map_transform_def] >>
  gvs[fn_labels_def, MAP_MAP_o, fn_has_entry_def,
      MEM_MAP, fn_succs_closed_def, combinTheory.o_DEF] >>
  rpt strip_tac >> gvs[] >> res_tac >> metis_tac[]
QED

(* General theorem: function_map_transform preserves ssa_form
   given per-block instruction preservation precondition. *)
Theorem fmt_preserves_ssa_form_proof:
  !bt fn.
    fn_insts (function_map_transform bt fn) = fn_insts fn
    ==>
    ssa_form fn ==> ssa_form (function_map_transform bt fn)
Proof
  simp[ssa_form_def]
QED

(* sublist preserves through FLAT *)
Theorem flat_sublist[local]:
  !(p : 'a list list) (q : 'a list list).
    sublist p q ==> sublist (FLAT p) (FLAT q)
Proof
  Induct >> simp[rich_listTheory.sublist_def] >>
  rpt strip_tac >>
  fs[rich_listTheory.sublist_append_extend] >>
  `sublist (FLAT p) (FLAT y)` by metis_tac[] >>
  `sublist (h ++ FLAT p) (h ++ FLAT y)`
    by (irule rich_listTheory.sublist_append_pair >>
        simp[rich_listTheory.sublist_refl]) >>
  simp[listTheory.FLAT_APPEND] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule rich_listTheory.sublist_append_include >> simp[]
QED

(* If instructions are a sublist, SSA is preserved (sublist means
   order-preserving without duplication). *)
Theorem ssa_form_sublist_proof:
  !fn fn'.
    ssa_form fn /\
    sublist (fn_insts fn') (fn_insts fn)
    ==>
    ssa_form fn'
Proof
  rpt strip_tac >> fs[ssa_form_def] >>
  irule rich_listTheory.sublist_ALL_DISTINCT >>
  qexists_tac `FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))` >>
  simp[] >>
  irule flat_sublist >>
  irule rich_listTheory.MAP_SUBLIST >> simp[]
QED

(* ALL_DISTINCT (MAP f l) means f is injective on l *)
Theorem all_distinct_map_inj[local]:
  !f l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\
             f x = f y ==> x = y
Proof
  rpt strip_tac >> gvs[MEM_EL] >>
  `n < LENGTH (MAP f l) /\ n' < LENGTH (MAP f l)` by simp[] >>
  `EL n (MAP f l) = EL n' (MAP f l)` by gvs[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

(* If FLAT(MAP f l) is ALL_DISTINCT and v appears in both f(x) and f(y)
   for x,y in l, then x = y. *)
Theorem all_distinct_flat_map_mem_unique[local]:
  !l f x y v.
    ALL_DISTINCT (FLAT (MAP f l)) /\ MEM x l /\ MEM y l /\
    MEM v (f x) /\ MEM v (f y) ==> x = y
Proof
  rpt strip_tac >>
  `?l1 l2. l = l1 ++ x::l2` by metis_tac[MEM_SPLIT] >>
  gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  `MEM y l1 \/ y = x \/ MEM y l2` by gvs[MEM_APPEND] >> gvs[] >>
  metis_tac[MEM_FLAT, MEM_MAP]
QED

(* If FLAT(MAP f l) is ALL_DISTINCT and MEM x l, then f(x) is ALL_DISTINCT. *)
Theorem all_distinct_flat_map_segment[local]:
  !l f x.
    ALL_DISTINCT (FLAT (MAP f l)) /\ MEM x l ==> ALL_DISTINCT (f x)
Proof
  rpt strip_tac >>
  `?l1 l2. l = l1 ++ x::l2` by metis_tac[MEM_SPLIT] >>
  gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

Theorem fn_insts_blocks_flat[local]:
  !l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem fn_inst_ids_eq_map[local]:
  !fn. ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) <=>
       fn_inst_ids_distinct fn
Proof
  simp[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
       MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

(* General list lemma: ALL_DISTINCT(FLAT(MAP f l')) when each element
   of l' traces to an element of l with same or empty f-values,
   and g is injective on l'. *)
Theorem all_distinct_flat_map_traced[local]:
  !(l' : 'a list) l (f : 'a -> 'b list) (g : 'a -> 'c).
    ALL_DISTINCT (FLAT (MAP f l)) /\
    ALL_DISTINCT (MAP g l') /\
    (!x. MEM x l' ==> ?y. MEM y l /\ g x = g y /\ (f x = f y \/ f x = []))
    ==>
    ALL_DISTINCT (FLAT (MAP f l'))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  simp[ALL_DISTINCT_APPEND] >> rpt conj_tac
  (* ALL_DISTINCT (f h) *)
  >- (`?orig. MEM orig l /\ (f h = f orig \/ f h = [])` by metis_tac[] >>
      gvs[] >- metis_tac[all_distinct_flat_map_segment] >> simp[])
  (* ALL_DISTINCT (FLAT (MAP f l')) by IH *)
  >- metis_tac[]
  (* Disjointness: MEM e (f h) ==> ~MEM e (FLAT (MAP f l')) *)
  >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `?orig. MEM orig l /\ g h = g orig /\ f h = f orig`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[] >>
        strip_tac >> gvs[] >> metis_tac[]) >>
  `?z. MEM z l' /\ MEM e (f z)`
    by (fs[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `?worig. MEM worig l /\ g z = g worig /\ f z = f worig`
    by (first_x_assum (qspec_then `z` mp_tac) >> simp[] >>
        strip_tac >> gvs[] >> metis_tac[]) >>
  `orig = worig` by metis_tac[all_distinct_flat_map_mem_unique] >>
  metis_tac[MEM_MAP]
QED

(* General SSA preservation for 1:1 transforms that preserve IDs and
   either preserve or clear outputs. Covers MAPi-based transforms
   like load_elim, copy_elision, etc. *)
Theorem ssa_form_preserved_by_output_subset_proof:
  !fn fn'.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    fn_inst_ids_distinct fn' /\
    (!inst. MEM inst (fn_insts fn') ==>
      ?orig. MEM orig (fn_insts fn) /\
             inst.inst_id = orig.inst_id /\
             (inst.inst_outputs = orig.inst_outputs \/
              inst.inst_outputs = []))
    ==>
    ssa_form fn'
Proof
  rpt strip_tac >> fs[ssa_form_def] >>
  irule (INST_TYPE [gamma |-> ``:num``] all_distinct_flat_map_traced) >>
  qexists_tac `\(i:instruction). i.inst_id` >>
  qexists_tac `fn_insts fn` >>
  fs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
     MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

(* General SSA preservation for function_map_transform:
   if each output instruction traces to an original with same id and
   preserved-or-cleared outputs, SSA is preserved. *)
Theorem fmt_preserves_ssa_form_general_proof:
  !bt fn.
    (!bb inst. MEM bb fn.fn_blocks /\
               MEM inst (bt bb).bb_instructions ==>
      ?orig. MEM orig bb.bb_instructions /\
             inst.inst_id = orig.inst_id /\
             (inst.inst_outputs = orig.inst_outputs \/
              inst.inst_outputs = [])) /\
    fn_inst_ids_distinct (function_map_transform bt fn) /\
    fn_inst_ids_distinct fn /\ ssa_form fn
    ==>
    ssa_form (function_map_transform bt fn)
Proof
  rpt strip_tac >>
  irule ssa_form_preserved_by_output_subset_proof >>
  simp[] >> qexists_tac `fn` >> simp[] >>
  fs[fn_insts_def, fn_insts_blocks_flat, function_map_transform_def] >>
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
  first_x_assum (qspecl_then [`y`, `inst`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `orig` >> simp[] >> metis_tac[]
QED

(* MAPi transform: each instruction traces to an original *)
Theorem mapi_transform_fn_insts_trace_proof:
  !h fn inst.
    MEM inst (fn_insts (function_map_transform
      (\bb. bb with bb_instructions :=
        MAPi (\idx i. h bb idx i) bb.bb_instructions) fn)) ==>
    ?bb idx. MEM bb fn.fn_blocks /\
             idx < LENGTH bb.bb_instructions /\
             inst = h bb idx (EL idx bb.bb_instructions)
Proof
  rpt strip_tac >>
  fs[fn_insts_def, fn_insts_blocks_flat, function_map_transform_def,
     MEM_FLAT, MEM_MAP] >>
  gvs[MEM_MAPi] >> metis_tac[]
QED
