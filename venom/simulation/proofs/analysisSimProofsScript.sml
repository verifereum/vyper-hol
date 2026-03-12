(*
 * Analysis-Driven Simulation — Proofs
 *
 * TOP-LEVEL:
 *   analysis_inst_sim_block_sim_proof       — inst sim ⟹ block sim (at idx=0)
 *   df_analysis_pass_correct_proof          — dataflow ⟹ function sim (at idx=0)
 *   df_analysis_pass_correct_sound_proof    — with soundness threading
 *   df_analysis_pass_correct_widen_sound_proof — widening variant
 *   analysis_inst_simulates_from_1_proof    — 1:1 as special case of 1:N
 *
 * Helper:
 *   run_insts_singleton, abt_label, abt_widen_label,
 *   step_inst_idx_indep, run_insts_idx_indep, run_insts_preserves_idx
 *)

Theory analysisSimProofs
Ancestors
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState
Libs
  listTheory

(* ===== Helpers ===== *)

Triviality run_insts_singleton:
  !fuel ctx (x:instruction) s.
    run_insts fuel ctx [x] s = step_inst fuel ctx x s
Proof
  rw[run_insts_def] >> CASE_TAC >> simp[run_insts_def]
QED

Triviality abt_label:
  !bottom result (f:'a -> instruction -> instruction list) bb.
    (analysis_block_transform bottom result f bb).bb_label = bb.bb_label
Proof
  simp[analysis_block_transform_def]
QED

Triviality abt_widen_label:
  !bottom result (f:'a -> instruction -> instruction list) bb.
    (analysis_block_transform_widen bottom result f bb).bb_label = bb.bb_label
Proof
  simp[analysis_block_transform_widen_def]
QED

(* step_inst for non-term non-INVOKE is idx-independent (bridges to instIdxIndep) *)
Triviality step_inst_idx_indep:
  !fuel ctx inst s n.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (step_inst fuel ctx inst s)
Proof
  rw[step_inst_non_invoke, step_inst_inst_idx_indep]
QED

(* run_insts on non-term non-INVOKE instructions is idx-independent *)
Triviality run_insts_idx_indep:
  !fuel ctx insts s n.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    run_insts fuel ctx insts (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (run_insts fuel ctx insts s)
Proof
  Induct_on `insts` >> simp[run_insts_def, exec_result_map_def] >>
  rpt gen_tac >> strip_tac >>
  simp[run_insts_def, step_inst_idx_indep] >>
  Cases_on `step_inst fuel ctx h s` >>
  simp[exec_result_map_def, run_insts_def] >>
  `v.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `n`] mp_tac) >>
  simp[] >>
  strip_tac >> simp[exec_result_map_def]
QED

(* run_insts preserves vs_inst_idx on OK results *)
Triviality run_insts_preserves_idx:
  !fuel ctx insts s s'.
    run_insts fuel ctx insts s = OK s' /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    s'.vs_inst_idx = s.vs_inst_idx
Proof
  Induct_on `insts` >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  fs[run_insts_def] >>
  BasicProvers.FULL_CASE_TAC >> fs[] >>
  `v.vs_inst_idx = s.vs_inst_idx` by metis_tac[step_inst_preserves_inst_idx] >>
  metis_tac[]
QED

(* ===== 1:1 as special case ===== *)

Theorem analysis_inst_simulates_from_1_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (g : 'a -> instruction -> instruction).
    analysis_inst_simulates_1 R_ok R_term sound g ==>
    analysis_inst_simulates R_ok R_term sound (\v inst. [g v inst])
Proof
  rw[analysis_inst_simulates_def, analysis_inst_simulates_1_def]
  >- (rw[run_insts_def] >> CASE_TAC >> simp[run_insts_def] >> metis_tac[])
  >> simp[]
QED

(* EL into FLAT at offset = LENGTH(FLAT(TAKE i ...)) indexes into EL i *)
(* Decompose MAPi g xs at index i *)
Triviality MAPi_decompose:
  !i (g : num -> 'a -> 'b list) xs.
    i < LENGTH xs ==>
    FLAT (MAPi g xs) =
      FLAT (TAKE i (MAPi g xs)) ++ g i (EL i xs) ++
      FLAT (DROP (SUC i) (MAPi g xs))
Proof
  rpt strip_tac >>
  `i < LENGTH (MAPi g xs)` by simp[indexedListsTheory.LENGTH_MAPi] >>
  `TAKE i (MAPi g xs) ++ [EL i (MAPi g xs)] ++ DROP (SUC i) (MAPi g xs) =
   MAPi g xs` by metis_tac[rich_listTheory.TAKE_DROP_SUC] >>
  `EL i (MAPi g xs) = g i (EL i xs)` by
    simp[indexedListsTheory.EL_MAPi] >>
  `FLAT (MAPi g xs) =
   FLAT (TAKE i (MAPi g xs) ++ [g i (EL i xs)] ++ DROP (SUC i) (MAPi g xs))` by
    metis_tac[] >>
  fs[FLAT_APPEND, FLAT]
QED

(* EL into FLAT at offset = LENGTH(FLAT(TAKE i ...)) indexes into EL i *)
Triviality EL_FLAT_MAPi:
  !i (g : num -> 'a -> 'b list) xs k.
    i < LENGTH xs /\ k < LENGTH (g i (EL i xs)) ==>
    EL (LENGTH (FLAT (TAKE i (MAPi g xs))) + k)
       (FLAT (MAPi g xs)) = EL k (g i (EL i xs))
Proof
  rpt strip_tac >>
  `FLAT (MAPi g xs) =
     FLAT (TAKE i (MAPi g xs)) ++ g i (EL i xs) ++
     FLAT (DROP (SUC i) (MAPi g xs))` by metis_tac[MAPi_decompose] >>
  pop_assum SUBST1_TAC >>
  simp[EL_APPEND_EQN]
QED

(* The FLAT offset + prefix length stays within bounds *)
Triviality FLAT_MAPi_offset_bound:
  !i (g : num -> 'a -> 'b list) xs.
    i < LENGTH xs ==>
    LENGTH (FLAT (TAKE i (MAPi g xs))) + LENGTH (g i (EL i xs))
      <= LENGTH (FLAT (MAPi g xs))
Proof
  rpt strip_tac >>
  `FLAT (MAPi g xs) =
     FLAT (TAKE i (MAPi g xs)) ++ g i (EL i xs) ++
     FLAT (DROP (SUC i) (MAPi g xs))` by metis_tac[MAPi_decompose] >>
  pop_assum SUBST1_TAC >>
  simp[]
QED

(* TAKE (SUC i) advances the FLAT offset by LENGTH (g i (EL i xs)) *)
Triviality FLAT_MAPi_offset_SUC:
  !i (g : num -> 'a -> 'b list) xs.
    i < LENGTH xs ==>
    LENGTH (FLAT (TAKE (SUC i) (MAPi g xs))) =
    LENGTH (FLAT (TAKE i (MAPi g xs))) + LENGTH (g i (EL i xs))
Proof
  rpt strip_tac >>
  `SUC i <= LENGTH (MAPi g xs)` by simp[indexedListsTheory.LENGTH_MAPi] >>
  `TAKE (SUC i) (MAPi g xs) = SNOC (EL i (MAPi g xs)) (TAKE i (MAPi g xs))` by
    simp[rich_listTheory.TAKE_SUC_BY_TAKE] >>
  `EL i (MAPi g xs) = g i (EL i xs)` by
    simp[indexedListsTheory.EL_MAPi] >>
  gvs[SNOC_APPEND, FLAT_APPEND, FLAT]
QED

(* When run_insts succeeds on a non-term non-INVOKE prefix, run_block
   skips past those instructions and continues from the resulting state. *)
Triviality run_block_skip_prefix:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s'
  ==>
    run_block fuel ctx bb (s with vs_inst_idx := j) =
    run_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[get_instruction_def] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `s'`]
    mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES])
  >> simp[]
QED

(* R_term tolerates vs_inst_idx changes *)
Triviality R_term_idx_change:
  !R_ok R_term s n.
    valid_state_rel R_ok R_term ==> R_term (s with vs_inst_idx := n) s
Proof
  rw[] >>
  `R_term s s` by metis_tac[vsr_R_term_refl] >>
  pop_assum mp_tac >> fs[valid_state_rel_def] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`s`, `s`, `s with vs_inst_idx := n`, `s`] mp_tac) >>
  simp[]
QED

Triviality R_term_idx_change2:
  !R_ok R_term s n.
    valid_state_rel R_ok R_term ==> R_term s (s with vs_inst_idx := n)
Proof
  rw[] >>
  `R_term s s` by metis_tac[vsr_R_term_refl] >>
  pop_assum mp_tac >> fs[valid_state_rel_def] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`s`, `s`, `s`, `s with vs_inst_idx := n`] mp_tac) >>
  simp[]
QED

(* R_ok tolerates vs_inst_idx changes when both sides change to the same value *)
Triviality R_ok_idx_change:
  !R_ok R_term s1 s2 n.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  rw[valid_state_rel_def] >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`s1`, `s2`] >> simp[]
QED

(* R_term tolerates vs_inst_idx changes on both sides *)
Triviality R_term_idx_change_both:
  !R_ok R_term s1 s2 n.
    valid_state_rel R_ok R_term /\ R_term s1 s2 ==>
    R_term (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  rpt strip_tac >>
  qpat_x_assum `R_term _ _` mp_tac >>
  fs[valid_state_rel_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`s1`, `s2`,
    `s1 with vs_inst_idx := n`, `s2 with vs_inst_idx := n`] mp_tac) >>
  simp[]
QED

(* lift_result preserved by exec_result_map when g preserves R_ok/R_term *)
Triviality lift_result_exec_result_map:
  !R_ok R_term g r1 r2.
    lift_result R_ok R_term r1 r2 /\
    (!s1 s2. R_ok s1 s2 ==> R_ok (g s1) (g s2)) /\
    (!s1 s2. R_term s1 s2 ==> R_term (g s1) (g s2))
  ==> lift_result R_ok R_term (exec_result_map g r1) (exec_result_map g r2)
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def, exec_result_map_def]
QED

(* Block-level run_block_preserves_R: same block, R_ok states.
   The operand condition is carried as a premise (not assumed globally). *)
Triviality run_block_preserves_R_block:
  !R_ok R_term.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) ==>
    !fuel ctx bb s1 s2.
      (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      R_ok s1 s2 ==>
      lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
  gvs[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[lift_result_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def] >> irule listTheory.EL_MEM >> simp[]) >>
  `lift_result R_ok R_term (step_inst fuel ctx inst s1)
     (step_inst fuel ctx inst s2)` by
    (irule step_inst_preserves_R_proof >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[lift_result_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[lift_result_def]
  >- (`v.vs_halted <=> v'.vs_halted` by
        (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
      Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
      metis_tac[vsr_R_ok_R_term])
  >>
  first_x_assum irule >> conj_tac >- fs[] >>
  irule R_ok_idx_change >> fs[] >> metis_tac[]
QED

(* For a terminator instruction, run_block's one-step result is
   lift_result-compatible between states differing only in vs_inst_idx.
   Proof: case split on terminator opcodes; jump_to erases idx to 0,
   halt_state preserves idx but routes to Halt (R_term), others are
   Error/IntRet/Abort (R_term or trivial). *)
Triviality terminator_run_block_step_lift:
  !R_ok R_term. valid_state_rel R_ok R_term ==>
  !fuel ctx inst s j.
    is_terminator inst.inst_opcode ==>
    lift_result R_ok R_term
      (case step_inst fuel ctx inst s of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s'
       | Error e => Error e)
      (case step_inst fuel ctx inst (s with vs_inst_idx := j) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s'
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  simp[step_inst_non_invoke] >>
  (* Fact A: normalizing idx to 0, both sides equal *)
  `exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst (s with vs_inst_idx := j)) =
   exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst s)` by
    simp[terminator_step_inst_base_idx_norm0] >>
  (* Case split on one side; norm0 constrains the other *)
  Cases_on `step_inst_base inst s` >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := j)` >>
  gvs[exec_result_map_def, venom_state_component_equality, lift_result_def]
  >- (
    (* OK-OK: both idx=0 by terminator_OK_inst_idx_0 *)
    `v.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
    `v'.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
    `v' = v` by gvs[venom_state_component_equality] >>
    gvs[] >> irule lift_result_refl_proof >>
    metis_tac[vsr_R_ok_refl, vsr_R_term_refl]
  ) >>
  (* Non-OK cases: v' = v with idx updated → R_term *)
  (`v' = v with vs_inst_idx := v'.vs_inst_idx` by
     gvs[venom_state_component_equality] >>
   pop_assum SUBST1_TAC >>
   metis_tac[R_term_idx_change2])
QED

(* INVOKE step_inst is idx-independent: setup_callee sets idx=0,
   merge_callee_state preserves caller structure.
   step_inst INVOKE on (s with idx := j) = exec_result_map (with idx := j) (step_inst INVOKE s) *)
Triviality foldl_update_var_idx:
  !pairs s0 j.
    FOLDL (\s' (out,val). s' with vs_vars := s'.vs_vars |+ (out,val))
      (s0 with vs_inst_idx := j) pairs =
    (FOLDL (\s' (out,val). s' with vs_vars := s'.vs_vars |+ (out,val))
       s0 pairs) with vs_inst_idx := j
Proof
  Induct >- simp[venom_state_component_equality] >>
  simp[pairTheory.FORALL_PROD] >> rpt gen_tac >>
  first_x_assum (qspecl_then
    [`s0 with vs_vars := s0.vs_vars |+ (p_1, p_2)`, `j`] mp_tac) >>
  simp[venom_state_component_equality]
QED

Triviality merge_callee_state_idx:
  !caller callee j.
    merge_callee_state (caller with vs_inst_idx := j) callee =
    (merge_callee_state caller callee) with vs_inst_idx := j
Proof
  simp[merge_callee_state_def, venom_state_component_equality]
QED

Triviality bind_outputs_idx:
  !outs vals s j.
    bind_outputs outs vals (s with vs_inst_idx := j) =
    OPTION_MAP (\s'. s' with vs_inst_idx := j) (bind_outputs outs vals s)
Proof
  simp[bind_outputs_def, update_var_def] >> rw[] >>
  simp[foldl_update_var_idx]
QED

(* For INVOKE, only the OK case shifts idx; Halt/Abort/Error are identical *)
Triviality invoke_step_inst_idx_OK_only:
  !fuel ctx inst s j.
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst (s with vs_inst_idx := j) =
    case step_inst fuel ctx inst s of
      OK s'' => OK (s'' with vs_inst_idx := j)
    | x => x
Proof
  rpt strip_tac >>
  simp[step_inst_def, eval_ops_inst_idx, setup_callee_def,
       merge_callee_state_idx, bind_outputs_idx,
       venom_state_component_equality] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[decode_invoke_def]
QED

(* step_inst at idx=0: if step_inst ... s = OK v and inst is non-terminator,
   then step_inst ... (s with idx := 0) = OK (v with idx := 0).
   Unifies INVOKE (invoke_step_inst_idx_OK_only) and non-term non-INVOKE
   (step_inst_idx_indep) cases. *)
Triviality step_inst_at_0:
  !fuel ctx inst s v.
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK v ==>
    step_inst fuel ctx inst (s with vs_inst_idx := 0) =
      OK (v with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    `step_inst fuel ctx inst (s with vs_inst_idx := 0) =
     case step_inst fuel ctx inst s of
       OK s'' => OK (s'' with vs_inst_idx := 0)
     | x => x` by simp[invoke_step_inst_idx_OK_only] >>
    fs[]
  )
  >- (
    `step_inst fuel ctx inst (s with vs_inst_idx := 0) =
     exec_result_map (\s'. s' with vs_inst_idx := 0)
       (step_inst fuel ctx inst s)` by
      simp[step_inst_idx_indep] >>
    fs[exec_result_map_def]
  )
QED

(* Combined: transfer_sound + step_inst_at_0.
   Given soundness at (s with idx := 0), derives soundness at (v with idx := 0)
   after a successful non-terminator step. *)
Triviality transfer_sound_at_0:
  !sound transfer ctx fuel run_ctx inst s v val.
    transfer_sound sound transfer ctx /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel run_ctx inst s = OK v /\
    sound val (s with vs_inst_idx := 0) ==>
    sound (transfer ctx inst val) (v with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  `step_inst fuel run_ctx inst (s with vs_inst_idx := 0) =
   OK (v with vs_inst_idx := 0)` by
    (irule step_inst_at_0 >> fs[]) >>
  fs[transfer_sound_def] >>
  first_x_assum irule >>
  qexistsl_tac [`fuel`, `run_ctx`, `s with vs_inst_idx := 0`] >> fs[]
QED

(* For INVOKE, run_block one-step result is lift_result-compatible between
   states differing only in vs_inst_idx, IF the caller handles the OK case.
   Non-OK cases are handled internally via invoke_step_inst_idx_OK_only. *)
Triviality invoke_run_block_step_lift:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
  valid_state_rel R_ok R_term ==>
  !fuel ctx inst s i j bb bb'.
    inst.inst_opcode = INVOKE /\
    (!v'. step_inst fuel ctx inst s = OK v' ==>
       lift_result R_ok R_term
         (run_block fuel ctx bb (v' with vs_inst_idx := SUC i))
         (run_block fuel ctx bb'
            (v' with vs_inst_idx := SUC j)))
  ==>
    lift_result R_ok R_term
      (case step_inst fuel ctx inst s of
         OK s'' => run_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s'
       | Error e => Error e)
      (case step_inst fuel ctx inst (s with vs_inst_idx := j) of
         OK s'' => run_block fuel ctx bb' (s'' with vs_inst_idx := SUC j)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s'
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst (s with vs_inst_idx := j) =
    case step_inst fuel ctx inst s of
      OK s'' => OK (s'' with vs_inst_idx := j)
    | x => x` by simp[invoke_step_inst_idx_OK_only] >>
  Cases_on `step_inst fuel ctx inst s` >> fs[lift_result_def] >>
  metis_tac[vsr_R_ok_refl, vsr_R_term_refl]
QED

(* When run_insts fails (non-OK), run_block on the same instructions
   produces a lift_result-compatible result (R_term allows idx difference). *)
Triviality run_block_prefix_fail_lift:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) prefix.
  valid_state_rel R_ok R_term ==>
  !fuel ctx bb s j.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    ~(?s'. run_insts fuel ctx prefix s = OK s')
  ==>
    lift_result R_ok R_term
      (run_block fuel ctx bb (s with vs_inst_idx := j))
      (run_insts fuel ctx prefix s)
Proof
  gen_tac >> gen_tac >> Induct >- rw[run_insts_def] >>
  rpt strip_tac >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by fs[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    (fs[] >> simp[step_inst_idx_indep]) >>
  fs[run_insts_def] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def]
  >- (
    (* OK: recurse *)
    `v.vs_inst_idx = s.vs_inst_idx` by
      (fs[] >> metis_tac[step_inst_preserves_inst_idx]) >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `v`, `SUC j`] mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES] >>
    impl_tac
    >- (fs[] >> rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
        simp[arithmeticTheory.ADD_CLAUSES])
    >> simp[]
  )
  >> simp[lift_result_def] >> metis_tac[R_term_idx_change]
QED

(* Reversed direction: run_insts first, run_block second.
   Same induction as run_block_prefix_fail_lift but swapped order. *)
Triviality run_insts_lift_run_block:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) prefix.
  valid_state_rel R_ok R_term ==>
  !fuel ctx bb s j.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    ~(?s'. run_insts fuel ctx prefix s = OK s')
  ==>
    lift_result R_ok R_term
      (run_insts fuel ctx prefix s)
      (run_block fuel ctx bb (s with vs_inst_idx := j))
Proof
  gen_tac >> gen_tac >> Induct >- rw[run_insts_def] >>
  rpt strip_tac >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by fs[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    (fs[] >> simp[step_inst_idx_indep]) >>
  fs[run_insts_def] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def]
  >- (
    (* OK: recurse *)
    `v.vs_inst_idx = s.vs_inst_idx` by
      (fs[] >> metis_tac[step_inst_preserves_inst_idx]) >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `v`, `SUC j`] mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES] >>
    impl_tac
    >- (fs[] >> rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >>
        simp[arithmeticTheory.ADD_CLAUSES])
    >> simp[]
  )
  >> simp[lift_result_def] >> metis_tac[R_term_idx_change2]
QED

(* ===== Block-level simulation (idx=0 precondition) ===== *)

(* General block sim helper with sound predicate.
   Used for both trivial soundness (sound = \v s. T) and real soundness.
   Induction on remaining instructions (LENGTH - vs_inst_idx). *)
Triviality analysis_block_sim_gen:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!i s. i < LENGTH bb.bb_instructions ==>
           sound (df_at bottom result bb.bb_label i) s)
  ==>
    !fuel ctx s.
      s.vs_inst_idx <= LENGTH bb.bb_instructions ==>
      lift_result R_ok R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx
           (analysis_block_transform bottom result f bb)
           (s with vs_inst_idx :=
              LENGTH (FLAT (TAKE s.vs_inst_idx
                (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                       bb.bb_instructions)))))
Proof
  rpt strip_tac >>
  simp[analysis_block_transform_def] >>
  qabbrev_tac `g = \idx inst. f (df_at bottom result bb.bb_label idx) inst` >>
  (* Complete induction on LENGTH - vs_inst_idx *)
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions ==>
     lift_result R_ok R_term (run_block fuel ctx bb s)
       (run_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s with vs_inst_idx :=
             LENGTH (FLAT (TAKE s.vs_inst_idx (MAPi g bb.bb_instructions)))))`
    suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    (* Base: i >= LENGTH, both Error *)
    `i = LENGTH bb.bb_instructions` by fs[] >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def, lift_result_def,
         TAKE_LENGTH_TOO_LONG, indexedListsTheory.LENGTH_MAPi]
  ) >>
  (* Inductive step: i < LENGTH *)
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qabbrev_tac `v = df_at bottom result bb.bb_label i` >>
  (* AIS facts (keep AIS in assumptions, extract what we need) *)
  `(!fuel' ctx' v' inst' s''. sound v' s'' ==>
       lift_result R_ok R_term (step_inst fuel' ctx' inst' s'')
         (run_insts fuel' ctx' (f v' inst') s'')) /\
   (!v' inst'. is_terminator inst'.inst_opcode ==> f v' inst' = [inst']) /\
   (!v' inst'. inst'.inst_opcode = INVOKE ==> f v' inst' = [inst']) /\
   (!v' inst'. ~is_terminator inst'.inst_opcode /\ inst'.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (f v' inst'))`
    by fs[analysis_inst_simulates_def] >>
  (* EL into FLAT for transformed block — use sg to keep assumption context *)
  sg `!k. k < LENGTH (g i (EL i bb.bb_instructions)) ==>
       EL (LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) + k)
          (FLAT (MAPi g bb.bb_instructions)) =
       EL k (g i (EL i bb.bb_instructions))`
  >- (rpt strip_tac >> irule EL_FLAT_MAPi >> simp[]) >>
  sg `LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
      LENGTH (g i (EL i bb.bb_instructions)) <=
      LENGTH (FLAT (MAPi g bb.bb_instructions))`
  >- (irule FLAT_MAPi_offset_bound >> simp[]) >>
  (* Abbreviate for readability *)
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  qabbrev_tac `j = LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions)))` >>
  `g i inst = f v inst` by simp[Abbr `g`, Abbr `v`, Abbr `inst`] >>
  (* Unroll run_block on original side *)
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[get_instruction_def, Abbr `inst`] >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  (* Case split on instruction type *)
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    (* Terminator: f v inst = [inst] *)
    `f v inst = [inst]` by (
      qpat_x_assum `!v' inst'. is_terminator inst'.inst_opcode ==> _`
        (qspecl_then [`v`, `inst`] mp_tac) >> simp[]) >>
    `g i inst = [inst]` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`, Abbr `j`]) >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[get_instruction_def] >>
    irule terminator_run_block_step_lift >> simp[]
  ) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE: f v inst = [inst], so transformed block has same inst at position j *)
    `f v inst = [inst]` by (
      qpat_x_assum `!v' inst'. inst'.inst_opcode = INVOKE ==> _`
        (qspecl_then [`v`, `inst`] mp_tac) >> simp[]) >>
    `g i inst = [inst]` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`, Abbr `j`]) >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[get_instruction_def, is_terminator_def] >>
    irule invoke_run_block_step_lift >> simp[] >>
    (* OK case: IH *)
    rpt strip_tac >>
    `v'.vs_inst_idx = s'.vs_inst_idx` by (
      `step_inst fuel ctx inst s' = OK v' /\ ~is_terminator inst.inst_opcode`
        by fs[is_terminator_def] >>
      imp_res_tac step_inst_preserves_inst_idx) >>
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) = SUC j` by (
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
       LENGTH (g i (EL i bb.bb_instructions))`
        by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
      fs[Abbr `j`, Abbr `inst`]
    ) >>
    qpat_x_assum `!m. m < n ==> _`
      (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
    impl_tac >- fs[] >>
    disch_then (qspecl_then [`fuel`, `ctx`,
                              `v' with vs_inst_idx := SUC i`] mp_tac) >>
    simp[] >>
    fs[Abbr `i`]
  ) >>
  (* Non-term non-INVOKE: f v inst may expand to multiple instructions *)
  `EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
    (f v inst)` by fs[analysis_inst_simulates_def] >>
  `sound v s'` by fs[Abbr `v`] >>
  `lift_result R_ok R_term (step_inst fuel ctx inst s')
    (run_insts fuel ctx (f v inst) s')` by fs[analysis_inst_simulates_def] >>
  (* Use let+THENL to avoid >> distribution across Cases_on branches *)
  let
    val step_non_ok = (
      `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
        (Cases_on `run_insts fuel ctx (f v inst) s'` >>
         gvs[lift_result_def]) >>
      irule lift_result_trans_proof >>
      conj_tac >- fs[] >> conj_tac >- fs[] >>
      qexists_tac `run_insts fuel ctx (f v inst) s'` >> fs[] >>
      irule run_insts_lift_run_block >> fs[] >>
      qexists_tac `f v inst` >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!k. k < LENGTH (f v _) ==> _` (qspec_then `k` mp_tac) >>
      simp[Abbr `inst`, Abbr `j`])
    val run_insts_non_ok = fs[lift_result_def]
  in
    Cases_on `step_inst fuel ctx inst s'`
    >- (
      (* step_inst OK *)
      rename1 `step_inst _ _ _ _ = OK st1` >> fs[] >>
      imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
        step_inst_preserves_inst_idx) >>
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       j + LENGTH (g i inst)` by (
        `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
         LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
         LENGTH (g i (EL i bb.bb_instructions))`
          by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
        fs[Abbr `j`, Abbr `inst`]) >>
      Cases_on `run_insts fuel ctx (f v inst) s'`
      >- (
        (* run_insts OK *)
        rename1 `run_insts _ _ _ _ = OK st2` >> fs[] >>
        imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
          run_insts_preserves_idx) >>
        `run_block fuel ctx
           (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
           (s' with vs_inst_idx := j) =
         run_block fuel ctx
           (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
           (st2 with vs_inst_idx := j + LENGTH (f v inst))` by (
          irule run_block_skip_prefix >> simp[]) >>
        `R_ok st1 st2` by fs[lift_result_def] >>
        irule lift_result_trans_proof >>
        conj_tac >- fs[] >> conj_tac >- fs[] >>
        qexists_tac `run_block fuel ctx bb (st2 with vs_inst_idx := SUC i)` >>
        conj_tac
        >- (
          irule run_block_preserves_R_block >> rpt conj_tac
          >- (rpt strip_tac >> res_tac)
          >- fs[]
          >- fs[]
          >- (irule R_ok_idx_change >> fs[] >> metis_tac[])
          >- fs[]
        )
        >- (
          qpat_x_assum `!m. m < LENGTH bb.bb_instructions - i ==> _`
            (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
          impl_tac >- fs[] >>
          disch_then (qspecl_then [`fuel`, `ctx`,
                                    `st2 with vs_inst_idx := SUC i`] mp_tac) >>
          simp[] >> fs[Abbr `i`]
        )
      )
      >- run_insts_non_ok
      >- run_insts_non_ok
      >- run_insts_non_ok
      >- run_insts_non_ok
    )
    >- step_non_ok
    >- step_non_ok
    >- step_non_ok
    >- step_non_ok
  end
QED

(* Variant of analysis_block_sim_gen with execution-threaded soundness.
   Instead of requiring universal soundness (∀i s. sound (df_at ... i) s),
   this version threads soundness through execution using transfer_sound
   and idx-independence of step_inst.

   Key insight: at instruction i, the run_block state has vs_inst_idx = i,
   but soundness holds at the "natural" state with vs_inst_idx = 0
   (step_inst preserves idx, run_block adjusts it). Using
   step_inst_idx_indep, we factor out the idx shift and apply the
   simulation at the natural state where soundness holds. *)
Triviality analysis_block_sim_gen_sound:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    transfer_sound sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s ==>
      lift_result R_ok R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx
           (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  simp[analysis_block_transform_def] >>
  qabbrev_tac `g = \idx inst. f (df_at bottom result bb.bb_label idx) inst` >>
  (* Complete induction on LENGTH - i, with execution-threaded soundness.
     The IH carries sound (df_at ... i) (s with idx := 0) — soundness
     at the "natural" state (before run_block's idx adjustment). *)
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx)
           (s with vs_inst_idx := 0) ==>
     lift_result R_ok R_term (run_block fuel ctx bb s)
       (run_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s with vs_inst_idx :=
             LENGTH (FLAT (TAKE s.vs_inst_idx (MAPi g bb.bb_instructions)))))`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      `s with vs_inst_idx := 0 = s` by fs[venom_state_component_equality] >>
      simp[TAKE_0]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    (* Base: i >= LENGTH, both Error *)
    `i = LENGTH bb.bb_instructions` by fs[] >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def, lift_result_def,
         TAKE_LENGTH_TOO_LONG, indexedListsTheory.LENGTH_MAPi]
  ) >>
  (* Inductive step: i < LENGTH *)
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qabbrev_tac `v = df_at bottom result bb.bb_label i` >>
  (* AIS facts *)
  qpat_x_assum `analysis_inst_simulates _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [analysis_inst_simulates_def]) >>
  (* EL into FLAT for transformed block *)
  sg `!k. k < LENGTH (g i (EL i bb.bb_instructions)) ==>
       EL (LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) + k)
          (FLAT (MAPi g bb.bb_instructions)) =
       EL k (g i (EL i bb.bb_instructions))`
  >- (rpt strip_tac >> irule EL_FLAT_MAPi >> simp[]) >>
  sg `LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
      LENGTH (g i (EL i bb.bb_instructions)) <=
      LENGTH (FLAT (MAPi g bb.bb_instructions))`
  >- (irule FLAT_MAPi_offset_bound >> simp[]) >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  qabbrev_tac `j = LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions)))` >>
  `g i inst = f v inst` by simp[Abbr `g`, Abbr `v`, Abbr `inst`] >>
  (* Unroll run_block on original side *)
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[get_instruction_def, Abbr `inst`] >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  (* === Terminator case === *)
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `f v inst = [inst]` by (
      qpat_x_assum `!v' inst'. is_terminator inst'.inst_opcode ==> _`
        (qspecl_then [`v`, `inst`] mp_tac) >> simp[]) >>
    `g i inst = [inst]` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`, Abbr `j`]) >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[get_instruction_def] >>
    irule terminator_run_block_step_lift >> simp[]
  ) >>
  (* === INVOKE case === *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    `f v inst = [inst]` by (
      qpat_x_assum `!v' inst'. inst'.inst_opcode = INVOKE ==> _`
        (qspecl_then [`v`, `inst`] mp_tac) >> simp[]) >>
    `g i inst = [inst]` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`, Abbr `j`]) >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[get_instruction_def, is_terminator_def] >>
    irule invoke_run_block_step_lift >> simp[] >>
    rpt strip_tac >>
    `v'.vs_inst_idx = s'.vs_inst_idx` by (
      `step_inst fuel ctx inst s' = OK v' /\ ~is_terminator inst.inst_opcode`
        by fs[is_terminator_def] >>
      imp_res_tac step_inst_preserves_inst_idx) >>
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) = SUC j` by (
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
       LENGTH (g i (EL i bb.bb_instructions))`
        by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
      fs[Abbr `j`, Abbr `inst`]) >>
    (* Soundness for SUC i *)
    `sound (df_at bottom result bb.bb_label (SUC i))
           (v' with vs_inst_idx := 0)` by (
      `df_at bottom result bb.bb_label (SUC i) =
       transfer run_ctx (EL i bb.bb_instructions)
         (df_at bottom result bb.bb_label i)` by fs[] >>
      pop_assum SUBST1_TAC >>
      irule transfer_sound_at_0 >>
      simp[Abbr `v`, Abbr `inst`] >>
      qexistsl_tac [`fuel`, `ctx`, `s'`] >> fs[]) >>
    (* Apply IH *)
    qpat_x_assum `!m. m < n ==> _`
      (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
    impl_tac >- fs[] >>
    disch_then (qspecl_then [`fuel`, `ctx`,
                              `v' with vs_inst_idx := SUC i`] mp_tac) >>
    simp[] >>
    (* Discharge soundness condition in IH *)
    disch_then match_mp_tac >>
    `df_at bottom result bb.bb_label (SUC i) =
     transfer run_ctx inst v` by (
      first_x_assum (qspec_then `i` mp_tac) >>
      simp[Abbr `v`, Abbr `inst`]) >>
    metis_tac[]
  ) >>
  (* === Non-term non-INVOKE case === *)
  `EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
    (f v inst)` by (
    first_x_assum (qspecl_then [`v`, `inst`] mp_tac) >> simp[]) >>
  (* Derive simulation at s' via idx-independence detour through idx=0 *)
  `lift_result R_ok R_term (step_inst fuel ctx inst s')
    (run_insts fuel ctx (f v inst) s')` by (
    qabbrev_tac `s_nat = s' with vs_inst_idx := 0` >>
    `sound v s_nat` by fs[Abbr `v`, Abbr `s_nat`] >>
    `lift_result R_ok R_term (step_inst fuel ctx inst s_nat)
      (run_insts fuel ctx (f v inst) s_nat)` by (
      first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`, `s_nat`] mp_tac) >>
      fs[]) >>
    `s' = s_nat with vs_inst_idx := i` by
      simp[Abbr `s_nat`, Abbr `i`, venom_state_component_equality] >>
    `step_inst fuel ctx inst s' =
     exec_result_map (\s''. s'' with vs_inst_idx := i)
       (step_inst fuel ctx inst s_nat)` by (
      qpat_assum `s' = _` (fn th =>
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[step_inst_idx_indep]) >>
    `run_insts fuel ctx (f v inst) s' =
     exec_result_map (\s''. s'' with vs_inst_idx := i)
       (run_insts fuel ctx (f v inst) s_nat)` by (
      qpat_x_assum `s' = _` (fn th =>
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[run_insts_idx_indep]) >>
    ntac 2 (pop_assum SUBST1_TAC) >>
    irule lift_result_exec_result_map >>
    simp[] >> metis_tac[R_ok_idx_change, R_term_idx_change_both]) >>
  (* Now case split - no s_nat pollution in assumptions *)
  let
    val step_non_ok = (
      `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
        (Cases_on `run_insts fuel ctx (f v inst) s'` >>
         gvs[lift_result_def]) >>
      irule lift_result_trans_proof >>
      conj_tac >- fs[] >> conj_tac >- fs[] >>
      qexists_tac `run_insts fuel ctx (f v inst) s'` >> fs[] >>
      irule run_insts_lift_run_block >> fs[] >>
      qexists_tac `f v inst` >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!k. k < LENGTH (f v _) ==> _` (qspec_then `k` mp_tac) >>
      simp[Abbr `inst`, Abbr `j`])
    val run_insts_non_ok = fs[lift_result_def]
  in
    Cases_on `step_inst fuel ctx inst s'`
    >- (
      (* step_inst OK *)
      rename1 `step_inst _ _ _ _ = OK st1` >> fs[] >>
      imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
        step_inst_preserves_inst_idx) >>
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       j + LENGTH (g i inst)` by (
        `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
         LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
         LENGTH (g i (EL i bb.bb_instructions))`
          by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
        fs[Abbr `j`, Abbr `inst`]) >>
      Cases_on `run_insts fuel ctx (f v inst) s'`
      >- (
        (* run_insts OK *)
        rename1 `run_insts _ _ _ _ = OK st2` >> fs[] >>
        imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
          run_insts_preserves_idx) >>
        `run_block fuel ctx
           (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
           (s' with vs_inst_idx := j) =
         run_block fuel ctx
           (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
           (st2 with vs_inst_idx := j + LENGTH (f v inst))` by (
          irule run_block_skip_prefix >> simp[]) >>
        `R_ok st1 st2` by fs[lift_result_def] >>
        (* Soundness at SUC i for st1 *)
        `sound (df_at bottom result bb.bb_label (SUC i))
               (st1 with vs_inst_idx := 0)` by (
          `df_at bottom result bb.bb_label (SUC i) =
           transfer run_ctx (EL i bb.bb_instructions)
             (df_at bottom result bb.bb_label i)` by fs[] >>
          pop_assum SUBST1_TAC >>
          irule transfer_sound_at_0 >>
          simp[Abbr `v`, Abbr `inst`] >>
          qexistsl_tac [`fuel`, `ctx`, `s'`] >> fs[]) >>
        irule lift_result_trans_proof >>
        conj_tac >- fs[] >> conj_tac >- fs[] >>
        qexists_tac `run_block fuel ctx bb (st2 with vs_inst_idx := SUC i)` >>
        conj_tac
        >- (
          irule run_block_preserves_R_block >> rpt conj_tac
          >- (rpt strip_tac >> res_tac)
          >- fs[]
          >- fs[]
          >- (irule R_ok_idx_change >> fs[] >> metis_tac[])
          >- fs[]
        )
        >- (
          qpat_x_assum `!m. m < LENGTH bb.bb_instructions - i ==> _`
            (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
          impl_tac >- fs[] >>
          disch_then (qspecl_then [`fuel`, `ctx`,
                                    `st2 with vs_inst_idx := SUC i`] mp_tac) >>
          simp[] >>
          disch_then match_mp_tac >>
          `transfer run_ctx inst v =
           df_at bottom result bb.bb_label (SUC i)` by (
            qpat_x_assum `Abbrev (inst = _)`
              (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
            qpat_x_assum `Abbrev (v = _)`
              (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
            first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
          pop_assum SUBST1_TAC >>
          first_x_assum (qspecl_then
            [`df_at bottom result bb.bb_label (SUC i)`,
             `st1 with vs_inst_idx := 0`,
             `st2 with vs_inst_idx := 0`] mp_tac) >>
          disch_then match_mp_tac >>
          conj_tac
          >- (irule R_ok_idx_change >> fs[] >> metis_tac[])
          >- first_assum ACCEPT_TAC
        )
      )
      >- run_insts_non_ok
      >- run_insts_non_ok
      >- run_insts_non_ok
      >- run_insts_non_ok
    )
    >- step_non_ok
    >- step_non_ok
    >- step_non_ok
    >- step_non_ok
  end
QED

(* Specialization for trivial soundness: sound = \v s. T.
   vs_inst_idx = 0: required because FLAT expansion changes block length;
   false at arbitrary idx (see counterexampleScript.sml). *)
Theorem analysis_inst_sim_block_sim_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f : 'a -> instruction -> instruction list) bb.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term (\v s. T) f /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result R_ok R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by simp[] >>
  `TAKE 0 (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
           bb.bb_instructions) = []` by simp[] >>
  `lift_result R_ok R_term (run_block fuel ctx bb s)
     (run_block fuel ctx (analysis_block_transform bottom result f bb)
        (s with vs_inst_idx :=
           LENGTH (FLAT (TAKE s.vs_inst_idx
             (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                    bb.bb_instructions)))))` suffices_by
    simp[] >>
  irule analysis_block_sim_gen >>
  rpt (conj_tac >- (first_x_assum ACCEPT_TAC)) >>
  qexists_tac `\v s. T` >>
  simp[]
QED

(* ===== Function-level: dataflow ⟹ function sim ===== *)

Theorem df_analysis_pass_correct_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (f : 'a -> instruction -> instruction list)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let all_lbls = MAP (\bb. bb.bb_label) bbs in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      analysis_inst_simulates R_ok R_term (\(v:'a) s. T) f /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx (analysis_function_transform bottom result f fn) s)
Proof
  simp[LET_THM, analysis_function_transform_def] >>
  rpt strip_tac >>
  irule block_sim_function_proof >>
  simp[abt_label] >> rpt strip_tac
  >- res_tac
  >- (irule analysis_inst_sim_block_sim_proof >> fs[] >>
      rpt strip_tac >> res_tac >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
QED

(* ===== With soundness threading ===== *)

(* FOLDL preserves a predicate when bottom satisfies it and join preserves it *)
Triviality foldl_sound:
  !l (bottom:'a) join (sound : 'a -> 'b -> bool).
    (!s. sound bottom s) /\
    (!a b s. sound a s ==> sound (join a b) s) ==>
    !s. sound (FOLDL join bottom l) s
Proof
  Induct >> rw[] >> metis_tac[]
QED

(* Like block_sim_function_proof, but block sim only required for
   lookup_block-returned blocks (avoids shadowed block issue) *)
Triviality block_sim_function_by_lookup:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
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
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  sg `lift_result R_ok R_term (run_block fuel ctx bb s1)
                               (run_block fuel ctx (bt bb) s2)`
  >- (irule lift_result_trans_proof >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `run_block fuel ctx bb s2` >>
      conj_tac
      >- (first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `s2`] mp_tac) >>
          simp[])
      >- (first_x_assum (qspecl_then [`s2.vs_current_bb`, `bb`] mp_tac) >> simp[])) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def] >>
  `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
  Cases_on `v.vs_halted` >> fs[] >>
  gvs[lift_result_def, function_map_transform_def] >>
  `v.vs_inst_idx = 0 /\ v'.vs_inst_idx = 0` by
    metis_tac[venomExecProofsTheory.run_block_OK_inst_idx_0] >>
  first_x_assum irule >> metis_tac[]
QED

(* Forward-specialized dataflow theorems for sound/widen proofs *)
val fixpoint_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_proof));
val inter_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_inter_transfer_proof));
val intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_intra_transfer_proof));
val widen_fixpoint_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeWidenProofsTheory.df_analyze_widen_fixpoint_proof));
val widen_inter_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeWidenProofsTheory.df_widen_at_inter_transfer_proof));
val widen_intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeWidenProofsTheory.df_widen_at_intra_transfer_proof));
val widen_entry_sound = SIMP_RULE (srw_ss()) [LET_THM]
  dfAnalyzeWidenProofsTheory.df_widen_entry_sound_proof;

(* dir = Forward required: backward analysis computes post-conditions, so
   sound(df_at(0), s) fails for entering states. See backwardCexScript.sml.
   vs_inst_idx = 0: see counterexampleScript.sml. *)
Theorem df_analysis_pass_correct_sound_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let all_lbls = (cfg_analyze fn).cfg_dfs_pre in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      dir = Forward /\
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      transfer_sound sound transfer ctx /\
      edge_transfer_sound sound edge_transfer ctx /\
      (!a b s. sound a s ==> sound (join a b) s) /\
      (!s. sound bottom s) /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => !s. sound v s) /\
      analysis_inst_simulates R_ok R_term sound f /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb. MEM bb fn.fn_blocks ==>
            MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx (analysis_function_transform bottom result f fn) s)
Proof
  simp[LET_THM, analysis_function_transform_def] >>
  rpt strip_tac >> fs[] >>
  (* Establish fixpoint *)
  sg `is_fixpoint
     (df_process_block Forward bottom join transfer edge_transfer ctx
        entry_val (cfg_analyze fn) fn.fn_blocks)
     (cfg_analyze fn).cfg_dfs_pre
     (df_analyze Forward bottom join transfer edge_transfer ctx entry_val fn)`
  >- (irule fixpoint_fwd >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`P`, `b`, `leq`, `m`] >> fs[]) >>
  irule block_sim_function_by_lookup >>
  simp[abt_label] >>
  rpt conj_tac
  (* lookup_var *)
  >- first_assum ACCEPT_TAC
  (* block sim *)
  >- (rpt strip_tac >>
      `MEM bb fn.fn_blocks` by
        metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
      `bb.bb_label = lbl` by (
        qpat_x_assum `lookup_block _ _ = _` mp_tac >>
        simp[lookup_block_def] >>
        qspec_tac (`fn.fn_blocks`, `bbs`) >>
        Induct >> rw[FIND_thm] >> fs[]) >>
      `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by metis_tac[] >>
      (* Establish soundness at idx 0 *)
      `!s. sound (df_at bottom
           (df_analyze Forward bottom join transfer edge_transfer ctx
              entry_val fn) bb.bb_label 0) s` by (
        imp_res_tac inter_fwd >> fs[] >>
        Cases_on `MAP (\nbr. edge_transfer ctx nbr lbl
                    (df_boundary bottom
                       (df_analyze Forward bottom join transfer edge_transfer
                          ctx entry_val fn) nbr))
                  (cfg_preds_of (cfg_analyze fn) lbl)` >> fs[]
        >- (Cases_on `entry_val` >> fs[] >>
            Cases_on `x` >> fs[] >>
            Cases_on `lbl = q` >> fs[])
        >- (rpt strip_tac >> irule foldl_sound >> metis_tac[])) >>
      irule analysis_block_sim_gen_sound >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (rpt strip_tac >> res_tac >> NO_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      qexistsl_tac [`ctx`, `sound`, `transfer`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      rpt strip_tac >> imp_res_tac intra_fwd >> fs[])
  (* R_ok trans, R_term trans *)
  >- metis_tac[]
  >- metis_tac[]
QED

(* ===== Widening variant with soundness ===== *)

(* Bridge: convert df_widen_state to df_state so we can reuse
   analysis_block_sim_gen_sound without duplicating 500 lines of proof *)
val widen_to_df_def = Define `
  widen_to_df (st : 'a df_widen_state) : 'a df_state =
    <| ds_inst := st.dws_inst; ds_boundary := st.dws_boundary |>`;

Triviality df_widen_at_eq_df_at:
  !bottom st lbl idx.
    df_widen_at bottom st lbl idx = df_at bottom (widen_to_df st) lbl idx
Proof
  rw[df_widen_at_def, df_at_def, widen_to_df_def]
QED

Triviality abt_widen_eq_abt:
  !bottom result f bb.
    analysis_block_transform_widen bottom result f bb =
    analysis_block_transform bottom (widen_to_df result) f bb
Proof
  rw[analysis_block_transform_widen_def, analysis_block_transform_def,
     df_widen_at_eq_df_at]
QED

Triviality aft_widen_eq_aft:
  !bottom result f fn.
    analysis_function_transform_widen bottom result f fn =
    analysis_function_transform bottom (widen_to_df result) f fn
Proof
  rw[analysis_function_transform_widen_def, analysis_function_transform_def,
     function_map_transform_def] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rw[FUN_EQ_THM, listTheory.MAP_EQ_f, abt_widen_eq_abt]
QED

Triviality df_widen_boundary_eq_df_boundary:
  !bottom st lbl.
    df_widen_boundary bottom st lbl = df_boundary bottom (widen_to_df st) lbl
Proof
  rw[df_widen_boundary_def, df_boundary_def, widen_to_df_def]
QED

(* Same preconditions as _sound variant: dir = Forward (backwardCexScript.sml),
   vs_inst_idx = 0 (counterexampleScript.sml). Uses widen_to_df bridge. *)
Theorem df_analysis_pass_correct_widen_sound_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list)
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (P : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let all_lbls = (cfg_analyze fn).cfg_dfs_pre in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      dir = Forward /\
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      transfer_sound sound transfer ctx /\
      edge_transfer_sound sound edge_transfer ctx /\
      (!a b s. sound a s ==> sound (join a b) s) /\
      (!a b s. sound a s ==> sound (widen a b) s) /\
      (!s. sound bottom s) /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => !s. sound v s) /\
      analysis_inst_simulates R_ok R_term sound f /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb. MEM bb fn.fn_blocks ==>
            MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 ==>
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  simp[LET_THM, aft_widen_eq_aft, analysis_function_transform_def] >>
  rpt strip_tac >> fs[] >>
  (* Establish widen fixpoint *)
  sg `is_fixpoint
     (df_process_block_widen Forward bottom join widen threshold
        transfer edge_transfer ctx entry_val (cfg_analyze fn) fn.fn_blocks)
     (cfg_analyze fn).cfg_dfs_pre
     (df_analyze_widen Forward bottom join widen threshold
        transfer edge_transfer ctx entry_val fn)`
  >- (irule widen_fixpoint_fwd >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`P`, `b`, `leq`, `m`] >> fs[]) >>
  irule block_sim_function_by_lookup >>
  simp[abt_label] >>
  rpt conj_tac
  (* lookup_var *)
  >- first_assum ACCEPT_TAC
  (* block sim *)
  >- (rpt strip_tac >>
      `MEM bb fn.fn_blocks` by
        metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
      `bb.bb_label = lbl` by (
        qpat_x_assum `lookup_block _ _ = _` mp_tac >>
        simp[lookup_block_def] >>
        qspec_tac (`fn.fn_blocks`, `bbs`) >>
        Induct >> rw[FIND_thm] >> fs[]) >>
      `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by metis_tac[] >>
      imp_res_tac widen_inter_fwd >>
      irule analysis_block_sim_gen_sound >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (rpt strip_tac >> res_tac >> NO_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      qexistsl_tac [`ctx`, `sound`, `transfer`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      TRY (rpt strip_tac >> imp_res_tac widen_intra_fwd >>
           fs[df_widen_at_eq_df_at] >> NO_TAC) >>
      (* Entry soundness: df_at = df_widen_at = df_widen_entry *)
      simp[GSYM df_widen_at_eq_df_at] >>
      ASM_REWRITE_TAC[] >>
      irule widen_entry_sound >> fs[] >>
      qexistsl_tac [`P`, `b`, `leq`, `m`] >> fs[])
  (* R_ok trans, R_term trans *)
  >- metis_tac[]
  >- metis_tac[]
QED

(* ===== Prepend correctness ===== *)

(* Prepend-aware pass correctness (non-widening, state-dependent).
   Extends df_analysis_pass_correct_sound_proof for transforms that
   insert instructions at the start of blocks (0:N prepend).

   The prepended instructions define fresh variables not referenced
   by any original instruction. Executing them is a no-op modulo
   the fresh vars: state_equiv fresh still holds after the prepend.

   Key insight: run_insts of prepended PHIs only adds bindings for
   fresh vars, then the per-instruction simulation proceeds as in
   the non-prepend case. The overall relation uses state_equiv fresh
   instead of state_equiv {} to account for the extra bindings.

   fresh = set of output variables defined by prepended instructions. *)
Theorem df_analysis_pass_correct_prepend_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list)
   (prepend : string -> instruction list)
   (fresh : string set).
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      transfer_sound sound transfer ctx /\
      edge_transfer_sound sound edge_transfer ctx /\
      (!a b s. sound a s ==> sound (join a b) s) /\
      (!s. sound bottom s) /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => !s. sound v s) /\
      analysis_inst_simulates R_ok R_term sound f /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (* Prepended instructions only define fresh variables *)
      (!lbl inst. MEM inst (prepend lbl) ==>
         EVERY (\v. v IN fresh) inst.inst_outputs) /\
      (* Fresh variables are not referenced by original instructions *)
      (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
         EVERY (\op. case op of Var v => v NOTIN fresh | _ => T)
               inst.inst_operands) /\
      (* Prepended instructions are non-terminator, non-INVOKE *)
      (!lbl inst. MEM inst (prepend lbl) ==>
         ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE)
    ==>
      !fuel ctx s.
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_prepend
               bottom result prepend f fn) s)
Proof
  cheat
QED
