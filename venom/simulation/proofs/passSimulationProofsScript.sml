(*
 * Pass Simulation Framework — Proofs
 *
 * TOP-LEVEL (frozen):
 *   lookup_block_map_proof       — label-preserving MAP commutes with lookup
 *   lift_result_refl_proof       — R_ok, R_term reflexive ⟹ lift_result reflexive
 *   lift_result_trans_proof      — R_ok, R_term transitive ⟹ lift_result transitive
 *   block_sim_function_proof     — block sim ⟹ function sim
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

(* Per-fn-block sim → function sim. Needs valid_state_rel + transitivity for the
   triangle composition at inter-block transitions: same-state-diff-code
   composed with same-code-diff-state (run_block_preserves_R) via
   lift_result_trans.
   Operand condition: fn's blocks don't read variables that disagree under R_ok.
   Takes per-fn-block simulation (not block_simulates) since block_simulates is
   universal over all blocks, which is too strong for state_equiv {vars}.
   vs_inst_idx = 0 precondition: required because 1:N expansion (FLAT) changes
   block length; false at arbitrary idx (see counterexampleScript.sml). *)
Theorem block_sim_function_proof:
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
  >- simp[run_function_def, function_map_transform_def, lift_result_def]
  >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks` >>
  gvs[lift_result_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  (* Triangle: run_block bb s1 ~ run_block bb s2 ~ run_block (bt bb) s2 *)
  sg `lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx (bt bb) s2)`
  >- (irule lift_result_trans_proof >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `run_block fuel ctx bb s2` >>
      conj_tac >- metis_tac[] >- metis_tac[]) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def] >>
  (* Both OK: use run_block_OK_inst_idx_0 for IH *)
  `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
  Cases_on `v.vs_halted` >> fs[] >>
  gvs[lift_result_def, function_map_transform_def] >>
  (* v and v' have vs_inst_idx = 0 from run_block_OK_inst_idx_0 *)
  `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
    metis_tac[run_block_OK_inst_idx_0] >>
  first_x_assum irule >> metis_tac[]
QED

(* Helper: lookup_block at HD label finds HD *)
Triviality lookup_block_HD[local]:
  !bbs. bbs <> [] ==>
    lookup_block (HD bbs).bb_label bbs = SOME (HD bbs)
Proof
  Cases >> simp[lookup_block_def, listTheory.FIND_thm]
QED

(* Reachability-guarded version of block_sim_function.
   Per-block sim only required when bb = HD fn.fn_blocks (entry) or
   vs_prev_bb <> NONE (reachable non-entry). Guard maintained across
   iterations via run_block_ok_sets_prev_bb. *)
Theorem block_sim_function_reachable_proof:
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
