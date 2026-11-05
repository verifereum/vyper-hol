Theory makeSsaCurrentReinsertionOrder
Ancestors makeSsaCurrentPhaseShape makeSsaCurrentReinsertionSlots
  makeSsaCurrentCleanupBoundary makeSsaCurrentCleanupShape makeSsaCurrentDefs
  venomInst list rich_list

Theorem current_reassign_phi_flags:
  !ids insts. MAP (\p. p.inst_opcode = PHI) (reassign_current_inst_ids ids insts) =
    MAP (\p. p.inst_opcode = PHI) insts
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem current_cleanup_batch_boundary:
  EVERY (\p. p.inst_opcode = PHI) pp /\
  (tt = [] \/ (HD tt).inst_opcode <> PHI) ==>
  EVERY (\p. p.inst_opcode = PHI)
    (TAKE (LENGTH (FILTER (\p. p.inst_opcode = PHI) (MAP simplify_current_phi pp)))
      (simplify_current_phi_prefix (pp ++ tt))) /\
  (DROP (LENGTH (FILTER (\p. p.inst_opcode = PHI) (MAP simplify_current_phi pp)))
      (simplify_current_phi_prefix (pp ++ tt)) = [] \/
   (HD (DROP (LENGTH (FILTER (\p. p.inst_opcode = PHI) (MAP simplify_current_phi pp)))
      (simplify_current_phi_prefix (pp ++ tt)))).inst_opcode <> PHI)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_cleanup_partition >> strip_tac >>
  `MAP (\p. p.inst_opcode = PHI) (simplify_current_phi_prefix (pp ++ tt)) =
   MAP (\p. p.inst_opcode = PHI)
     (FILTER (\p. p.inst_opcode = PHI) (MAP simplify_current_phi pp) ++
      FILTER (\p. p.inst_opcode <> PHI) (MAP simplify_current_phi pp) ++ tt)` by
    simp[simplify_current_phi_prefix_def, current_reassign_phi_flags] >>
  qabbrev_tac `kept = FILTER (\p. p.inst_opcode = PHI) (MAP simplify_current_phi pp)` >>
  qabbrev_tac `rest = FILTER (\p. p.inst_opcode <> PHI) (MAP simplify_current_phi pp) ++ tt` >>
  qabbrev_tac `result = simplify_current_phi_prefix (pp ++ tt)` >>
  `MAP (\p. p.inst_opcode = PHI) result =
   MAP (\p. p.inst_opcode = PHI) (kept ++ rest)` by
    simp[Abbr `result`, Abbr `kept`, Abbr `rest`, MAP_APPEND] >>
  `EVERY (\p. p.inst_opcode = PHI) kept` by
    simp[Abbr `kept`, EVERY_FILTER] >>
  `rest <> [] ==> (HD rest).inst_opcode <> PHI` by
    (simp[Abbr `rest`] >>
     Cases_on `FILTER (\p. p.inst_opcode <> PHI) (MAP simplify_current_phi pp)`
     >- (gvs[] >> metis_tac[]) >>
     gvs[] >>
     `EVERY (\p. p.inst_opcode <> PHI)
       (FILTER (\p. p.inst_opcode <> PHI) (MAP simplify_current_phi pp))` by
       simp[EVERY_FILTER] >> gvs[]) >>
  `MAP (\p. p.inst_opcode = PHI) (TAKE (LENGTH kept) result) =
   MAP (\p. p.inst_opcode = PHI) kept` by
    (qpat_assum `MAP _ result = MAP _ (kept ++ rest)` (mp_tac o Q.AP_TERM `TAKE (LENGTH kept)`) >>
     simp[GSYM MAP_TAKE, TAKE_APPEND]) >>
  `MAP (\p. p.inst_opcode = PHI) (DROP (LENGTH kept) result) =
   MAP (\p. p.inst_opcode = PHI) rest` by
    (qpat_assum `MAP _ result = MAP _ (kept ++ rest)` (mp_tac o Q.AP_TERM `DROP (LENGTH kept)`) >>
     pure_rewrite_tac[GSYM MAP_DROP, DROP_LENGTH_APPEND] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `MAP _ (TAKE _ _) = _` (mp_tac o Q.AP_TERM `EVERY I`) >>
      simp[EVERY_MAP, combinTheory.o_DEF]) >>
  qpat_x_assum `MAP _ (DROP _ _) = MAP _ rest` mp_tac >>
  Cases_on `DROP (LENGTH kept) result` >> Cases_on `rest` >>
  fs[] >> qpat_x_assum `F::_ = _` (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Theorem current_cleanup_retained_before_copy:
  EVERY (\p. p.inst_opcode = PHI) pp /\
  (tt = [] \/ (HD tt).inst_opcode <> PHI) /\
  i < LENGTH pp /\ j < LENGTH pp /\
  (simplify_current_phi (EL i pp)).inst_opcode = PHI /\
  (simplify_current_phi (EL j pp)).inst_opcode = ASSIGN ==>
  ?r c batch.
    r < batch /\ batch <= c /\
    c < LENGTH (simplify_current_phi_prefix (pp ++ tt)) /\
    current_inst_no_id (EL r (simplify_current_phi_prefix (pp ++ tt))) =
      current_inst_no_id (simplify_current_phi (EL i pp)) /\
    current_inst_no_id (EL c (simplify_current_phi_prefix (pp ++ tt))) =
      current_inst_no_id (simplify_current_phi (EL j pp)) /\
    EVERY (\p. p.inst_opcode = PHI)
      (TAKE batch (simplify_current_phi_prefix (pp ++ tt))) /\
    (DROP batch (simplify_current_phi_prefix (pp ++ tt)) = [] \/
     (HD (DROP batch (simplify_current_phi_prefix (pp ++ tt)))).inst_opcode <> PHI)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `current_cleanup_occurrence_rank pp i < LENGTH pp /\
   current_inst_no_id (EL (current_cleanup_occurrence_rank pp i)
     (simplify_current_phi_prefix (pp ++ tt))) =
   current_inst_no_id (simplify_current_phi (EL i pp))` by
    (irule current_cleanup_occurrence >> simp[]) >>
  `current_cleanup_occurrence_rank pp j < LENGTH pp /\
   current_inst_no_id (EL (current_cleanup_occurrence_rank pp j)
     (simplify_current_phi_prefix (pp ++ tt))) =
   current_inst_no_id (simplify_current_phi (EL j pp))` by
    (irule current_cleanup_occurrence >> simp[]) >>
  drule_all current_cleanup_retained_rank >> strip_tac >>
  `(simplify_current_phi (EL j pp)).inst_opcode <> PHI` by simp[] >>
  drule_all current_cleanup_copy_rank >> strip_tac >>
  qexistsl_tac [`current_cleanup_occurrence_rank pp i`,
    `current_cleanup_occurrence_rank pp j`,
    `LENGTH (FILTER (\p. p.inst_opcode = PHI) (MAP simplify_current_phi pp))`] >>
  drule_all current_cleanup_batch_boundary >> simp[]
QED

Theorem current_certificate_reinsertion_order:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h /\
  fn_phis_non_degenerate fn /\ old.bb_instructions = phis ++ tail /\
  EVERY (\p. p.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis ==>
  ?out src r c batch.
    lookup_block h fn'.fn_blocks = SOME out /\
    current_token_name H (CurrentOriginal h i 0) = SOME src /\ src <> v /\
    r < batch /\ batch <= c /\ c < LENGTH out.bb_instructions /\
    (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [src] /\
    (EL c out.bb_instructions).inst_opcode = ASSIGN /\
    (EL c out.bb_instructions).inst_operands = [Var src] /\
    (EL c out.bb_instructions).inst_outputs = [v] /\
    EVERY (\p. p.inst_opcode = PHI) (TAKE batch out.bb_instructions) /\
    (DROP batch out.bb_instructions = [] \/
     (HD (DROP batch out.bb_instructions)).inst_opcode <> PHI)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_reinsertion_copy >> strip_tac >>
  `?pp tt. final.bb_instructions = pp ++ tt /\
    LENGTH pp = LENGTH pre + LENGTH phis /\
    EVERY (\p. p.inst_opcode = PHI) pp /\
    (tt = [] \/ (HD tt).inst_opcode <> PHI)` by
    (`current_phi_view final.bb_instructions =
      FOLDL (\view ev. current_event_slot_action (current_succ_map fn) h ev view)
        (current_phi_view ((pre ++ phis) ++ tail)) events` by simp[APPEND_ASSOC] >>
     drule current_replay_phase_split >> simp[EVERY_APPEND] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `LENGTH pre + i < LENGTH pp /\ k < LENGTH pp` by decide_tac >>
  `simplify_current_phi (EL (LENGTH pre+i) pp) = EL (LENGTH pre+i) pp /\
   (EL (LENGTH pre+i) pp).inst_outputs = [src] /\
   (EL k pp).inst_outputs = [v] /\
   simplify_current_phi (EL k pp) =
     (EL k pp) with <|inst_opcode := ASSIGN; inst_operands := [Var src]|>` by
    (gvs[EL_APPEND_EQN]) >>
  `(simplify_current_phi (EL (LENGTH pre+i) pp)).inst_opcode = PHI /\
   (simplify_current_phi (EL k pp)).inst_opcode = ASSIGN` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  qspecl_then [`tt`, `LENGTH pre+i`, `k`] mp_tac
    (Q.GENL [`tt`, `i`, `j`] current_cleanup_retained_before_copy) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `lookup_block h fn'.fn_blocks = SOME (simplify_current_phi_block final)` by
    simp[current_cleanup_if_lookup] >>
  `(simplify_current_phi_block final).bb_instructions =
    simplify_current_phi_prefix (pp ++ tt)` by
    (Cases_on `pp` >- gvs[] >>
     gvs[EVERY_DEF] >> simp[simplify_current_phi_block_def]) >>
  imp_res_tac current_no_id_fields >>
  qexistsl_tac [`simplify_current_phi_block final`, `src`, `r`, `c`, `batch`] >>
  gvs[]
QED
