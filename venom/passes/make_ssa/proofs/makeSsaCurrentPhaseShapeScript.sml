Theory makeSsaCurrentPhaseShape
Ancestors makeSsaCurrentReinsertionSlots makeSsaCurrentFinalSlots makeSsaCurrentCleanupShape
  makeSsaCurrentCleanupBoundary makeSsaCurrentDefs venomInst list rich_list

(* Stable filter rank tracks occurrences even when instructions are equal. *)
Theorem current_filter_rank:
  !P xs k. k < LENGTH xs /\ P (EL k xs) ==>
    LENGTH (FILTER P (TAKE k xs)) < LENGTH (FILTER P xs) /\
    EL (LENGTH (FILTER P (TAKE k xs))) (FILTER P xs) = EL k xs
Proof
  gen_tac >> Induct >> simp[] >> gen_tac >> Cases_on `k` >> simp[] >>
  Cases_on `P h` >> simp[]
QED

Theorem current_filter_partition_rank:
  !P xs k. k < LENGTH xs ==>
  (if P (EL k xs) then LENGTH (FILTER P (TAKE k xs))
   else LENGTH (FILTER P xs) + LENGTH (FILTER (\x. ~P x) (TAKE k xs))) <
    LENGTH (FILTER P xs ++ FILTER (\x. ~P x) xs) /\
  EL (if P (EL k xs) then LENGTH (FILTER P (TAKE k xs))
      else LENGTH (FILTER P xs) + LENGTH (FILTER (\x. ~P x) (TAKE k xs)))
    (FILTER P xs ++ FILTER (\x. ~P x) xs) = EL k xs
Proof
  rpt gen_tac >> strip_tac >> Cases_on `P (EL k xs)` >> simp[]
  >- (drule_all current_filter_rank >> strip_tac >> simp[EL_APPEND_EQN]) >>
  `LENGTH (FILTER (\x. ~P x) (TAKE k xs)) < LENGTH (FILTER (\x. ~P x) xs) /\
   EL (LENGTH (FILTER (\x. ~P x) (TAKE k xs))) (FILTER (\x. ~P x) xs) = EL k xs` by
    (irule current_filter_rank >> simp[]) >>
  simp[EL_APPEND_EQN]
QED

Definition current_cleanup_occurrence_rank_def:
  current_cleanup_occurrence_rank pre k =
    if (simplify_current_phi (EL k pre)).inst_opcode = PHI then
      LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi (TAKE k pre)))
    else
      LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)) +
      LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi (TAKE k pre)))
End

Theorem current_cleanup_occurrence:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ k < LENGTH pre ==>
  current_cleanup_occurrence_rank pre k < LENGTH pre /\
  current_inst_no_id (EL (current_cleanup_occurrence_rank pre k)
    (simplify_current_phi_prefix (pre ++ tail))) =
  current_inst_no_id (simplify_current_phi (EL k pre))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `current_cleanup_occurrence_rank pre k <
    LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
      FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) /\
   EL (current_cleanup_occurrence_rank pre k)
    (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
      FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)) =
      simplify_current_phi (EL k pre)` by
    (qspecl_then [`\i. i.inst_opcode = PHI`, `MAP simplify_current_phi pre`, `k`]
       mp_tac (GEN_ALL current_filter_partition_rank) >>
     simp[current_cleanup_occurrence_rank_def, EL_MAP, MAP_TAKE]) >>
  `current_cleanup_occurrence_rank pre k < LENGTH pre` by
    metis_tac[current_cleanup_partition_length, LENGTH_MAP, LENGTH_APPEND] >>
  simp[] >>
  drule_all current_cleanup_partition >> strip_tac >>
  simp[simplify_current_phi_prefix_def] >>
  qmatch_goalsub_abbrev_tac `reassign_current_inst_ids ids insts` >>
  `LENGTH ids = LENGTH insts` by
    (simp[Abbr `ids`, Abbr `insts`] >>
     qspec_then `MAP simplify_current_phi pre` mp_tac current_cleanup_partition_length >>
     simp[]) >>
  `current_cleanup_occurrence_rank pre k < LENGTH insts` by
    (simp[Abbr `insts`] >> gvs[LENGTH_APPEND]) >>
  drule current_reassign_no_id >>
  disch_then (mp_tac o Q.AP_TERM `EL (current_cleanup_occurrence_rank pre k)`) >>
  simp[EL_MAP, current_reassign_length] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[Abbr `insts`, EL_APPEND_EQN]
QED

Theorem current_cleanup_block_occurrence:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ k < LENGTH pre ==>
  current_cleanup_occurrence_rank pre k < LENGTH pre /\
  current_inst_no_id (EL (current_cleanup_occurrence_rank pre k)
    (simplify_current_phi_block bb).bb_instructions) =
  current_inst_no_id (simplify_current_phi (EL k pre))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_cleanup_occurrence >> strip_tac >>
  Cases_on `pre` >- gvs[] >>
  gvs[] >> simp[simplify_current_phi_block_def]
QED

Theorem current_cleanup_if_occurrence:
  lookup_block l bbs = SOME bb /\ bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ k < LENGTH pre ==>
  ?bb'. lookup_block l (simplify_current_phis_if enabled bbs) = SOME bb' /\
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    (if enabled then current_cleanup_occurrence_rank pre k else k) < LENGTH pre /\
    current_inst_no_id (EL
      (if enabled then current_cleanup_occurrence_rank pre k else k) bb'.bb_instructions) =
    current_inst_no_id (if enabled then simplify_current_phi (EL k pre) else EL k pre)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[current_cleanup_if_lookup] >> Cases_on `enabled` >>
  simp[current_cleanup_block_length]
  >- (drule_all current_cleanup_block_occurrence >> simp[]) >>
  simp[EL_APPEND_EQN]
QED

(* Consumer ranks distinguish the retained parallel batch from sequential copies. *)
Theorem current_cleanup_retained_rank:
  k < LENGTH pre /\ (simplify_current_phi (EL k pre)).inst_opcode = PHI ==>
  current_cleanup_occurrence_rank pre k =
    LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi (TAKE k pre))) /\
  current_cleanup_occurrence_rank pre k <
    LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre))
Proof
  strip_tac >> simp[current_cleanup_occurrence_rank_def] >>
  qspecl_then [`\i. i.inst_opcode = PHI`, `MAP simplify_current_phi pre`, `k`]
    mp_tac current_filter_rank >>
  simp[EL_MAP, MAP_TAKE]
QED

Theorem current_cleanup_copy_rank:
  k < LENGTH pre /\ (simplify_current_phi (EL k pre)).inst_opcode <> PHI ==>
  current_cleanup_occurrence_rank pre k =
    LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)) +
    LENGTH (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi (TAKE k pre))) /\
  LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)) <=
    current_cleanup_occurrence_rank pre k
Proof
  strip_tac >> simp[current_cleanup_occurrence_rank_def]
QED

(* The certificate's concrete replay block may be consumed with any established
   leading-PHI split. No instruction-ID equality identifies an occurrence. *)
Theorem current_replay_cleanup_occurrence:
  fn'.fn_blocks = simplify_current_phis_if enabled renamed /\
  lookup_block h renamed = SOME final /\
  final.bb_instructions = phis ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ k < LENGTH phis ==>
  ?out. lookup_block h fn'.fn_blocks = SOME out /\
    LENGTH out.bb_instructions = LENGTH final.bb_instructions /\
    (if enabled then current_cleanup_occurrence_rank phis k else k) < LENGTH phis /\
    current_inst_no_id (EL
      (if enabled then current_cleanup_occurrence_rank phis k else k) out.bb_instructions) =
    current_inst_no_id (if enabled then simplify_current_phi (EL k phis) else EL k phis)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_cleanup_if_occurrence >>
  disch_then (qspec_then `enabled` mp_tac) >> gvs[]
QED

Theorem current_replay_phi_flags:
  current_phi_view insts' =
    FOLDL (\view ev. current_event_slot_action sm h ev view)
      (current_phi_view insts) events ==>
  MAP (\i. i.inst_opcode = PHI) insts' = MAP (\i. i.inst_opcode = PHI) insts
Proof
  rewrite_tac[current_event_view_fold] >>
  disch_then (mp_tac o Q.AP_TERM `MAP IS_SOME`) >>
  simp[current_phi_view_def, MAP_MAP_o, combinTheory.o_DEF,
    COND_RAND, COND_RATOR]
QED

Theorem current_replay_phase_split:
  current_phi_view insts' =
    FOLDL (\view ev. current_event_slot_action sm h ev view)
      (current_phi_view (pre ++ tail)) events /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
  ?pp tt. insts' = pp ++ tt /\ LENGTH pp = LENGTH pre /\
    LENGTH tt = LENGTH tail /\ EVERY (\i. i.inst_opcode = PHI) pp /\
    (tt = [] \/ (HD tt).inst_opcode <> PHI)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule current_replay_phi_flags >> strip_tac >>
  `?pp tt. insts' = pp ++ tt /\
    MAP (\i. i.inst_opcode = PHI) pp = MAP (\i. i.inst_opcode = PHI) pre /\
    MAP (\i. i.inst_opcode = PHI) tt = MAP (\i. i.inst_opcode = PHI) tail` by
    (qpat_x_assum `current_phi_view _ = _` kall_tac >>
     gvs[MAP_APPEND, MAP_EQ_APPEND] >> metis_tac[]) >>
  qexistsl_tac [`pp`, `tt`] >> simp[] >>
  `LENGTH pp = LENGTH pre /\ LENGTH tt = LENGTH tail` by
    metis_tac[LENGTH_MAP] >> simp[] >> conj_tac
  >- (qpat_x_assum `MAP _ pp = MAP _ pre`
        (mp_tac o Q.AP_TERM `EVERY I`) >>
      simp[EVERY_MAP, combinTheory.o_DEF]) >>
  Cases_on `tt` >> Cases_on `tail` >> gvs[]
QED

Theorem current_certificate_phase_blocks:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
  ?pre renamed final pp tt out.
    A h = current_block_annotations old pre /\
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\ lookup_block h fn'.fn_blocks = SOME out /\
    final.bb_instructions = pp ++ tt /\
    LENGTH pp = LENGTH pre + LENGTH phis /\ LENGTH tt = LENGTH tail /\
    EVERY (\i. i.inst_opcode = PHI) pp /\
    (tt = [] \/ (HD tt).inst_opcode <> PHI) /\
    LENGTH out.bb_instructions = LENGTH final.bb_instructions /\
    current_phi_view final.bb_instructions =
      FOLDL (\view ev. current_event_slot_action (current_succ_map fn) h ev view)
        (current_phi_view (pre ++ old.bb_instructions)) events /\
    (!v. current_actual_inserted fn v h <=>
      ?inst. MEM inst pre /\ MEM v inst.inst_outputs) /\
    (!k v. k < LENGTH pre /\ (EL k pre).inst_outputs = [v] ==>
      k < LENGTH final.bb_instructions /\ ?n.
      (EL k final.bb_instructions).inst_outputs = [n] /\
      current_token_name H (CurrentInserted v h) = SOME n) /\
    (!i v. i < LENGTH old.bb_instructions /\
      (EL i old.bb_instructions).inst_opcode = PHI /\
      (EL i old.bb_instructions).inst_outputs = [v] ==>
      LENGTH pre+i < LENGTH final.bb_instructions /\ ?src.
      (EL (LENGTH pre+i) final.bb_instructions).inst_outputs = [src] /\
      current_token_name H (CurrentOriginal h i 0) = SOME src /\
      (fn_phis_non_degenerate fn ==>
        simplify_current_phi (EL (LENGTH pre+i) final.bb_instructions) =
          EL (LENGTH pre+i) final.bb_instructions))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_block_replay >> strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI) pre` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     simp[build_phi_inst_supply_def] >> rpt strip_tac >> gvs[]) >>
  `?pp tt. final.bb_instructions = pp ++ tt /\
    LENGTH pp = LENGTH pre + LENGTH phis /\ LENGTH tt = LENGTH tail /\
    EVERY (\i. i.inst_opcode = PHI) pp /\
    (tt = [] \/ (HD tt).inst_opcode <> PHI)` by
    (`current_phi_view final.bb_instructions =
       FOLDL (\view ev. current_event_slot_action (current_succ_map fn) h ev view)
         (current_phi_view ((pre ++ phis) ++ tail)) events` by
       simp[APPEND_ASSOC] >>
     drule current_replay_phase_split >>
     simp[EVERY_APPEND] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `?out. lookup_block h fn'.fn_blocks = SOME out /\
    LENGTH out.bb_instructions = LENGTH final.bb_instructions` by
    (gvs[current_cleanup_if_lookup] >>
     Cases_on `blocks_have_leading_phi fn.fn_blocks` >>
     simp[current_cleanup_block_length]) >>
  qexistsl_tac [`pre`, `renamed`, `final`, `pp`, `tt`, `out`] >> simp[]
QED

Theorem current_phase_phi_position:
  fn'.fn_blocks = simplify_current_phis_if enabled renamed /\
  lookup_block h renamed = SOME final /\ lookup_block h fn'.fn_blocks = SOME out /\
  final.bb_instructions = pp ++ tt /\
  EVERY (\i. i.inst_opcode = PHI) pp /\
  (tt = [] \/ (HD tt).inst_opcode <> PHI) /\ k < LENGTH pp ==>
  (if enabled then current_cleanup_occurrence_rank pp k else k) < LENGTH pp /\
  current_inst_no_id (EL
    (if enabled then current_cleanup_occurrence_rank pp k else k) out.bb_instructions) =
  current_inst_no_id (if enabled then simplify_current_phi (EL k pp) else EL k pp)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_replay_cleanup_occurrence >> strip_tac >> gvs[]
QED

Theorem current_phase_retained_position:
  fn'.fn_blocks = simplify_current_phis_if enabled renamed /\
  lookup_block h renamed = SOME final /\ lookup_block h fn'.fn_blocks = SOME out /\
  final.bb_instructions = pp ++ tt /\
  EVERY (\i. i.inst_opcode = PHI) pp /\
  (tt = [] \/ (HD tt).inst_opcode <> PHI) /\ k < LENGTH pp /\
  simplify_current_phi (EL k pp) = EL k pp ==>
  (if enabled then current_cleanup_occurrence_rank pp k else k) < LENGTH pp /\
  current_inst_no_id (EL
    (if enabled then current_cleanup_occurrence_rank pp k else k) out.bb_instructions) =
    current_inst_no_id (EL k final.bb_instructions) /\
  (enabled ==> current_cleanup_occurrence_rank pp k <
    LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_phase_phi_position >> strip_tac >>
  `((EL k pp).inst_opcode = PHI)` by
    (gvs[EVERY_EL] >> metis_tac[]) >>
  `(simplify_current_phi (EL k pp)).inst_opcode = PHI` by simp[] >>
  drule_all current_cleanup_retained_rank >> strip_tac >>
  simp[EL_APPEND_EQN]
QED

Theorem current_phase_ordinary_position:
  fn'.fn_blocks = simplify_current_phis_if enabled renamed /\
  lookup_block h renamed = SOME final /\ lookup_block h fn'.fn_blocks = SOME out /\
  final.bb_instructions = pp ++ tt /\
  EVERY (\i. i.inst_opcode = PHI) pp /\
  (tt = [] \/ (HD tt).inst_opcode <> PHI) /\ j < LENGTH tt ==>
  LENGTH pp + j < LENGTH out.bb_instructions /\
  current_inst_no_id (EL (LENGTH pp+j) out.bb_instructions) =
    current_inst_no_id (EL j tt)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_cleanup_if_ordinary_index >>
  disch_then (qspec_then `enabled` strip_assume_tac) >> gvs[]
QED

Theorem current_phase_collapsed_position:
  fn'.fn_blocks = simplify_current_phis_if enabled renamed /\
  lookup_block h renamed = SOME final /\ lookup_block h fn'.fn_blocks = SOME out /\
  final.bb_instructions = pp ++ tt /\
  EVERY (\i. i.inst_opcode = PHI) pp /\
  (tt = [] \/ (HD tt).inst_opcode <> PHI) /\ k < LENGTH pp /\
  (simplify_current_phi (EL k pp)).inst_opcode <> PHI ==>
  (if enabled then current_cleanup_occurrence_rank pp k else k) < LENGTH pp /\
  current_inst_no_id (EL
    (if enabled then current_cleanup_occurrence_rank pp k else k) out.bb_instructions) =
  current_inst_no_id (if enabled then simplify_current_phi (EL k pp) else EL k pp) /\
  (enabled ==> LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pp)) <=
    current_cleanup_occurrence_rank pp k)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_phase_phi_position >> strip_tac >>
  drule_all current_cleanup_copy_rank >> simp[]
QED

Theorem current_no_id_fields:
  current_inst_no_id a = current_inst_no_id b ==>
  a.inst_opcode = b.inst_opcode /\ a.inst_operands = b.inst_operands /\
  a.inst_outputs = b.inst_outputs
Proof
  simp[current_inst_no_id_def, instruction_component_equality]
QED
