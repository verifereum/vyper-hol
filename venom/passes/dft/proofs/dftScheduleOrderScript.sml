(*
 * What DFT's schedule keeps in order.
 *
 * dft_fn reschedules the non-pseudo instructions of each block (the body
 * and its terminator) and keeps the pseudo prefix (PHI, PARAM, ...) as is.
 * dft_block_rel says what the result is, block by block: the same label,
 * the same pseudos first, then a permutation of the input's non-pseudo
 * instructions, each one either unchanged or with its operands flipped,
 * in which every pair the input orders by dft_must_order keeps that order.
 *
 * dft_must_order x y (x before y in the input) holds when
 *   - y uses an output of x;
 *   - x and y have conflicting effects (one writes an effect the other
 *     reads or writes);
 *   - x is a root of the dependency graph that nothing can depend on: it
 *     has no outputs and no effects (ASSERT, ASSERT_UNREACHABLE, INVALID).
 *     DFT schedules roots in block order, after only their own earlier
 *     dependencies, so nothing after a root is scheduled before it;
 *   - y is a terminator.
 *
 * The schedule does not keep fallible instructions (is_fallible: ASSERT,
 * ASSERT_UNREACHABLE, RETURNDATACOPY, INVALID, INVOKE) in order: an ASSERT
 * can move above an INVOKE that came before it.  dft_fallible_order_kept
 * states that it does, for one input function and its schedule; the pass
 * contract takes it as its pre-condition, until the pinned DFT orders
 * fallible instructions (add_abort_deps).
 *)
Theory dftScheduleOrder
Ancestors
  dftCorrectness dftStructural dftDefs dftTopoSort dftWf dftIdempotent passSharedDefs venomWf venomInst venomEffects list rich_list

(* a comes before b in the list l. *)
Definition id_before_def:
  id_before l a b <=> ?i j. i < j /\ j < LENGTH l /\ EL i l = a /\ EL j l = b
End

Definition dft_must_order_def:
  dft_must_order x y <=>
    ~DISJOINT (set (inst_defs x)) (set (inst_uses y)) \/
    ~DISJOINT (write_effects x.inst_opcode)
              (read_effects y.inst_opcode UNION write_effects y.inst_opcode) \/
    ~DISJOINT (read_effects x.inst_opcode) (write_effects y.inst_opcode) \/
    (x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
     write_effects x.inst_opcode = empty_effects) \/
    is_terminator y.inst_opcode
End

Definition dft_block_rel_def:
  dft_block_rel bb bb' <=>
    bb'.bb_label = bb.bb_label /\
    ?body.
      bb'.bb_instructions =
        FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ body /\
      PERM (MAP (\i. i.inst_id) body)
           (MAP (\i. i.inst_id)
              (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)) /\
      EVERY (from_block bb.bb_instructions) body /\
      !x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
            ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
            id_before (MAP (\i. i.inst_id) bb.bb_instructions)
              x.inst_id y.inst_id /\
            dft_must_order x y ==>
            id_before (MAP (\i. i.inst_id) body) x.inst_id y.inst_id
End

(* Fallible instructions keep their relative order in every block. *)
Definition dft_fallible_order_kept_def:
  dft_fallible_order_kept fn fn' <=>
    LIST_REL
      (\bb bb'.
         !x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
               is_fallible x /\ is_fallible y /\
               id_before (MAP (\i. i.inst_id) bb.bb_instructions)
                 x.inst_id y.inst_id ==>
               id_before (MAP (\i. i.inst_id) bb'.bb_instructions)
                 x.inst_id y.inst_id)
      fn.fn_blocks fn'.fn_blocks
End

Theorem id_before_cons:
  id_before (h::t) a b <=>
  (h = a /\ MEM b t) \/ id_before t a b
Proof
  simp[id_before_def, MEM_EL] >> eq_tac
  >- (rpt strip_tac >> Cases_on `i`
      >- (gvs[] >> Cases_on `j` >> gvs[] >> metis_tac[])
      >> Cases_on `j` >> gvs[] >> metis_tac[])
  >> rpt strip_tac
  >- (qexistsl [`0`, `SUC n`] >> simp[])
  >> qexistsl [`SUC i`, `SUC j`] >> simp[]
QED

Theorem id_before_mem:
  id_before l a b ==> MEM a l /\ MEM b l
Proof
  rw[id_before_def] >> metis_tac[MEM_EL, arithmeticTheory.LESS_TRANS]
QED

Theorem id_before_trans:
  ALL_DISTINCT l /\ id_before l a b /\ id_before l b c ==>
  id_before l a c
Proof
  rw[id_before_def] >>
  `j = i'` by metis_tac[ALL_DISTINCT_EL_IMP, arithmeticTheory.LESS_TRANS] >>
  qexistsl [`i`, `j'`] >> simp[]
QED

Theorem id_before_filter:
  P a /\ P b ==>
  (id_before (FILTER P l) a b <=> id_before l a b)
Proof
  Induct_on `l` >> simp[id_before_cons] >>
  rpt strip_tac >> Cases_on `P h` >> gvs[id_before_cons, MEM_FILTER] >>
  metis_tac[]
QED

Theorem id_before_append_suffix:
  ~MEM a p /\ ~MEM b p ==>
  (id_before (p ++ l) a b <=> id_before l a b)
Proof
  Induct_on `p` >> simp[id_before_cons] >> metis_tac[]
QED

Theorem id_before_map_filter:
  (!x. MEM x l /\ (f x = a \/ f x = b) ==> P x) ==>
  (id_before (MAP f (FILTER P l)) a b <=> id_before (MAP f l) a b)
Proof
  Induct_on `l` >- simp[id_before_def] >>
  rpt strip_tac >>
  `!x. MEM x l /\ (f x = a \/ f x = b) ==> P x` by metis_tac[MEM] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `P h` >> simp[id_before_cons, MEM_MAP, MEM_FILTER] >>
  gvs[MEM] >> metis_tac[]
QED

Theorem flip_operands_order_fields:
  !i. set (inst_uses (flip_operands i)) = set (inst_uses i) /\
      read_effects (flip_operands i).inst_opcode = read_effects i.inst_opcode /\
      write_effects (flip_operands i).inst_opcode = write_effects i.inst_opcode /\
      is_terminator (flip_operands i).inst_opcode = is_terminator i.inst_opcode
Proof
  gen_tac >> rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  IF_CASES_TAC >> simp[inst_uses_def, MEM_operand_vars_iff,
                         pred_setTheory.EXTENSION] >>
  gvs[is_comparator_def] >>
  simp[flip_comparison_opcode_def, read_effects_def, write_effects_def,
       is_terminator_def, inst_uses_def, MEM_operand_vars_iff,
       pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem from_block_id_cases:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM x bi /\
  from_block bi x' /\ x'.inst_id = x.inst_id ==>
  x' = x \/ x' = flip_operands x
Proof
  rw[from_block_def] >>
  `j = x` by
    (gvs[] >>
     qpat_x_assum `MEM j bi` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     qpat_x_assum `MEM x bi` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     `n = n'` by
       (qspec_then `MAP (\i. i.inst_id) bi` mp_tac ALL_DISTINCT_EL_IMP >>
        simp[EL_MAP] >> metis_tac[]) >>
     gvs[]) >> simp[]
QED

Theorem from_block_must_order:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM x bi /\ MEM y bi /\
  from_block bi x' /\ from_block bi y' /\
  x'.inst_id = x.inst_id /\ y'.inst_id = y.inst_id ==>
  (dft_must_order x' y' <=> dft_must_order x y)
Proof
  rpt strip_tac >>
  `x' = x \/ x' = flip_operands x` by metis_tac[from_block_id_cases] >>
  `y' = y \/ y' = flip_operands y` by metis_tac[from_block_id_cases] >>
  gvs[dft_must_order_def, inst_defs_def, flip_operands_order_fields]
QED

Theorem dft_block_suffix_decomposition:
  !order bb. (dft_block order bb).bb_instructions =
  FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
  FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions
Proof
  rpt gen_tac >>
  simp[dft_block_def, LET_THM, rich_listTheory.FILTER_APPEND,
       rich_listTheory.FILTER_FILTER] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode /\ is_pseudo i.inst_opcode)
     bb.bb_instructions = []` by simp[FILTER_EQ_NIL] >>
  simp[] >> sym_tac >>
  simp[FILTER_EQ_ID, EVERY_MEM] >> rpt strip_tac >>
  metis_tac[schedule_output_from_block, build_eda_wf, entry_instructions_mem]
QED

Theorem dft_block_suffix_structure:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions ==>
  PERM (MAP (\i. i.inst_id)
          (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions))
       (MAP (\i. i.inst_id)
          (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)) /\
  EVERY (from_block bb.bb_instructions)
    (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions)
Proof
  rpt strip_tac
  >- metis_tac[dft_block_perm_ids]
  >> simp[EVERY_MEM] >> metis_tac[dft_block_from_orig]
QED

Theorem dft_block_suffix_producers:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions ==>
  output_producer_before bb.bb_instructions
    (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions)
Proof
  rpt strip_tac >>
  qspecl_then [`order`, `bb`] mp_tac dft_block_suffix_decomposition >>
  simp[Once dft_block_def, LET_THM] >> disch_then (SUBST1_TAC o SYM) >>
  irule schedule_output_producer_before >>
  simp[build_eda_wf, entry_instructions_mem] >>
  conj_tac
  >- gvs[bb_well_formed_def] >>
  conj_tac
  >- gvs[non_pseudo_defs_before_uses_def] >>
  conj_tac
  >- gvs[bb_well_formed_def] >>
  irule eda_topo_compatible_gen_weak_plain >>
  gvs[bb_well_formed_def, non_pseudo_defs_before_uses_def]
QED

Theorem producing_inst_distinct_outputs:
  !bi x v.
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) /\
  MEM x bi /\ MEM v x.inst_outputs ==>
  producing_inst bi v = SOME x
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND, producing_inst_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem dft_block_suffix_data_order:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~DISJOINT (set (inst_defs x)) (set (inst_uses y)) ==>
  id_before
    (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions))
    x.inst_id y.inst_id
Proof
  rpt strip_tac >>
  `output_producer_before bb.bb_instructions
    (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions)` by
      metis_tac[dft_block_suffix_producers] >>
  drule_all dft_block_suffix_structure >>
  disch_then (qspec_then `order` strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `MAP (\i. i.inst_id) sched_out` >>
  `MEM y.inst_id (MAP (\i. i.inst_id) sched_out)` by
    (drule sortingTheory.PERM_MEM_EQ >>
     disch_then (qspec_then `y.inst_id` mp_tac) >> simp[MEM_MAP, MEM_FILTER] >>
     metis_tac[]) >>
  gvs[MEM_MAP] >> rename1 `MEM y' sched_out` >>
  `y' = y \/ y' = flip_operands y` by
    (irule from_block_id_cases >> simp[] >>
     qexists_tac `bb.bb_instructions` >> gvs[EVERY_MEM]) >>
  `set (inst_uses y') = set (inst_uses y)` by gvs[flip_operands_order_fields] >>
  `?v. MEM v x.inst_outputs /\ MEM (Var v) y'.inst_operands` by
    (gvs[inst_defs_def, pred_setTheory.DISJOINT_DEF,
         pred_setTheory.EXTENSION, inst_uses_def, MEM_operand_vars_iff] >>
     metis_tac[]) >>
  `producing_inst bb.bb_instructions v = SOME x` by
    metis_tac[producing_inst_distinct_outputs] >>
  qpat_x_assum `MEM y' sched_out` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  gvs[output_producer_before_def] >>
  first_x_assum (qspecl_then [`n`, `v`, `x`] mp_tac) >> simp[] >> strip_tac >>
  `m < LENGTH sched_out` by decide_tac >>
  simp[id_before_def] >> qexistsl [`m`, `n`] >> simp[EL_MAP]
QED

Theorem dft_block_suffix_representative:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  MEM x bb.bb_instructions /\ ~is_pseudo x.inst_opcode ==>
  ?k. k < LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode)
                   (dft_block order bb).bb_instructions) /\
      (EL k (FILTER (\i. ~is_pseudo i.inst_opcode)
                   (dft_block order bb).bb_instructions) = x \/
       EL k (FILTER (\i. ~is_pseudo i.inst_opcode)
                   (dft_block order bb).bb_instructions) = flip_operands x)
Proof
  rpt strip_tac >> drule_all dft_block_suffix_structure >>
  disch_then (qspec_then `order` strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `LENGTH sched_out` >>
  `MEM x.inst_id (MAP (\i. i.inst_id) sched_out)` by
    (drule sortingTheory.PERM_MEM_EQ >>
     disch_then (qspec_then `x.inst_id` mp_tac) >>
     simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  gvs[MEM_MAP] >> rename1 `MEM x' sched_out` >>
  `x' = x \/ x' = flip_operands x` by
    (irule from_block_id_cases >> simp[] >>
     qexists_tac `bb.bb_instructions` >> gvs[EVERY_MEM]) >>
  metis_tac[MEM_EL]
QED

Theorem dft_block_suffix_terminator_order:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  x.inst_id <> y.inst_id /\ is_terminator y.inst_opcode ==>
  id_before
    (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions))
    x.inst_id y.inst_id
Proof
  rpt strip_tac >>
  `?i. i < LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions) /\
       (EL i (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions)).inst_id = x.inst_id` by
    metis_tac[dft_block_suffix_representative, flip_operands_inst_id] >>
  `?j. j < LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions) /\
       (EL j (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions)).inst_id = y.inst_id /\
       is_terminator (EL j (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions)).inst_opcode` by
    metis_tac[dft_block_suffix_representative, flip_operands_inst_id,
              flip_operands_order_fields] >>
  qmatch_goalsub_abbrev_tac `MAP (\i. i.inst_id) sched_out` >>
  `bb_well_formed (dft_block order bb)` by metis_tac[dft_block_well_formed_gen] >>
  qpat_x_assum `bb_well_formed (dft_block _ _)` mp_tac >>
  rewrite_tac[bb_well_formed_def] >>
  once_rewrite_tac[dft_block_suffix_decomposition] >>
  simp[] >> strip_tac >>
  qpat_x_assum `!k. _ /\ is_terminator _ ==> _` (qspec_then
    `LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) + j` mp_tac) >>
  simp[rich_listTheory.EL_APPEND2] >> strip_tac >>
  `i < j` by (Cases_on `i = j` >> gvs[] >> decide_tac) >>
  simp[id_before_def] >> qexistsl [`i`, `j`] >> simp[EL_MAP]
QED

Theorem id_before_distinct_endpoints:
  ALL_DISTINCT l /\ id_before l a b ==> a <> b
Proof
  rw[id_before_def] >>
  `i < LENGTH l /\ i <> j` by decide_tac >>
  qspec_then `l` mp_tac ALL_DISTINCT_EL_IMP >> simp[] >> metis_tac[]
QED

Theorem dft_block_suffix_data_terminator_order:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
  (~DISJOINT (set (inst_defs x)) (set (inst_uses y)) \/
   is_terminator y.inst_opcode) ==>
  id_before
    (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions))
    x.inst_id y.inst_id
Proof
  rpt strip_tac
  >- metis_tac[dft_block_suffix_data_order]
  >> metis_tac[dft_block_suffix_terminator_order, id_before_distinct_endpoints]
QED

(* Exact effect-state projections.  Membership is enough for the read frontier,
   so repeated effects do not require a list-normalization convention. *)
Theorem write_effect_fold_lookup:
  !effs et inst eff.
    FLOOKUP (FOLDL (\acc weff.
      <| et_last_write := acc.et_last_write |+ (weff, inst);
         et_all_reads := acc.et_all_reads |+ (weff, []) |>)
      et effs).et_last_write eff =
    if MEM eff effs then SOME inst else FLOOKUP et.et_last_write eff
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `h = eff` >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem write_effect_fold_reads:
  !effs et inst eff.
    et_get_reads (FOLDL (\acc weff.
      <| et_last_write := acc.et_last_write |+ (weff, inst);
         et_all_reads := acc.et_all_reads |+ (weff, []) |>)
      et effs) eff =
    if MEM eff effs then [] else et_get_reads et eff
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `h = eff` >>
  simp[et_get_reads_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem read_effect_fold_reads:
  !effs et inst eff r.
    MEM r (et_get_reads (FOLDL (\acc reff.
      acc with et_all_reads :=
        acc.et_all_reads |+ (reff, et_get_reads acc reff ++ [inst]))
      et effs) eff) <=>
    MEM r (et_get_reads et eff) \/ (MEM eff effs /\ r = inst)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `h = eff` >>
  simp[et_get_reads_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem compute_effect_last_write:
  FLOOKUP (SND (compute_effect_deps et inst)).et_last_write eff =
    if MEM eff (effects_to_list (write_effects inst.inst_opcode))
    then SOME inst else FLOOKUP et.et_last_write eff
Proof
  simp[compute_effect_deps_def, read_foldl_last_write,
       write_effect_fold_lookup]
QED

Theorem compute_effect_reads:
  MEM r (et_get_reads (SND (compute_effect_deps et inst)) eff) <=>
    (~MEM eff (effects_to_list (write_effects inst.inst_opcode)) /\
       MEM r (et_get_reads et eff)) \/
    (MEM eff (effects_to_list (read_effects inst.inst_opcode)) /\ r = inst)
Proof
  simp[compute_effect_deps_def, read_effect_fold_reads,
       write_effect_fold_reads] >>
  IF_CASES_TAC >> simp[]
QED

Theorem compute_effect_write_dep:
  MEM eff (effects_to_list (write_effects inst.inst_opcode)) /\
  (MEM d (et_get_reads et eff) \/
   FLOOKUP et.et_last_write eff = SOME d) ==>
  MEM d (FST (compute_effect_deps et inst))
Proof
  strip_tac >>
  simp[compute_effect_deps_def, MEM_FLAT, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
  disj1_tac >> qexists `eff` >> simp[] >>
  Cases_on `FLOOKUP et.et_last_write eff` >> gvs[]
QED

Theorem compute_effect_read_dep:
  MEM eff (effects_to_list (read_effects inst.inst_opcode)) /\
  FLOOKUP et.et_last_write eff = SOME d /\
  d.inst_id <> inst.inst_id ==>
  MEM d (FST (compute_effect_deps et inst))
Proof
  rpt strip_tac >>
  Cases_on `MEM eff (effects_to_list (write_effects inst.inst_opcode))`
  >- (irule compute_effect_write_dep >> metis_tac[]) >>
  simp[compute_effect_deps_def, MEM_FLAT, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
  disj2_tac >> qexists `eff` >> simp[]
QED

(* A writer frontier summarizes all preceding writers; a reader either remains
   active or has already been ordered before the writer that cleared it. *)
Definition effect_history_def:
  effect_history R prefix et <=>
    (!eff w. MEM w prefix /\
       MEM eff (effects_to_list (write_effects w.inst_opcode)) ==>
       ?last. FLOOKUP et.et_last_write eff = SOME last /\
         (w.inst_id = last.inst_id \/ R w.inst_id last.inst_id)) /\
    (!eff r. MEM r prefix /\
       MEM eff (effects_to_list (read_effects r.inst_opcode)) ==>
       MEM r (et_get_reads et eff) \/
       ?last. FLOOKUP et.et_last_write eff = SOME last /\
         R r.inst_id last.inst_id) /\
    (!eff w. FLOOKUP et.et_last_write eff = SOME w ==>
       MEM w prefix /\ MEM eff (effects_to_list (write_effects w.inst_opcode))) /\
    (!eff r. MEM r (et_get_reads et eff) ==>
       MEM r prefix /\ MEM eff (effects_to_list (read_effects r.inst_opcode)))
End

Theorem effect_history_empty:
  effect_history R [] empty_effect_track
Proof
  simp[effect_history_def, empty_effect_track_def, et_get_reads_def,
       finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem effect_history_write_conflict:
  effect_history R prefix et /\ transitive R /\
  (!d. MEM d (FST (compute_effect_deps et inst)) ==>
       R d.inst_id inst.inst_id) /\
  MEM x prefix /\
  MEM eff (effects_to_list (write_effects inst.inst_opcode)) /\
  (MEM eff (effects_to_list (write_effects x.inst_opcode)) \/
   MEM eff (effects_to_list (read_effects x.inst_opcode))) ==>
  R x.inst_id inst.inst_id
Proof
  simp[effect_history_def, relationTheory.transitive_def] >>
  rpt strip_tac >>
  metis_tac[compute_effect_write_dep]
QED

Theorem effect_history_read_conflict:
  effect_history R prefix et /\ transitive R /\
  (!d. MEM d (FST (compute_effect_deps et inst)) ==>
       R d.inst_id inst.inst_id) /\
  (!d. MEM d prefix ==> d.inst_id <> inst.inst_id) /\
  MEM x prefix /\
  MEM eff (effects_to_list (read_effects inst.inst_opcode)) /\
  MEM eff (effects_to_list (write_effects x.inst_opcode)) ==>
  R x.inst_id inst.inst_id
Proof
  simp[effect_history_def, relationTheory.transitive_def] >>
  rpt strip_tac >>
  metis_tac[compute_effect_read_dep]
QED

Theorem effect_history_conflict:
  effect_history R prefix et /\ transitive R /\
  (!d. MEM d (FST (compute_effect_deps et inst)) ==>
       R d.inst_id inst.inst_id) /\
  (!d. MEM d prefix ==> d.inst_id <> inst.inst_id) /\
  MEM x prefix /\
  ~effects_independent x.inst_opcode inst.inst_opcode ==>
  R x.inst_id inst.inst_id
Proof
  `!eff s. MEM eff (effects_to_list s) <=> eff IN s` by
    (rpt gen_tac >> once_rewrite_tac[effects_to_list_def] >>
     simp_tac pure_ss [MEM_FILTER] >> Cases_on `eff` >> simp[]) >>
  simp[effects_independent_def, pred_setTheory.DISJOINT_DEF,
       pred_setTheory.EXTENSION, pred_setTheory.IN_INTER,
       pred_setTheory.IN_UNION, pred_setTheory.NOT_IN_EMPTY] >>
  metis_tac[effect_history_write_conflict, effect_history_read_conflict]
QED

Theorem effect_history_step:
  effect_history R prefix et /\ transitive R /\
  (!d. MEM d (FST (compute_effect_deps et inst)) ==>
       R d.inst_id inst.inst_id) ==>
  effect_history R (prefix ++ [inst]) (SND (compute_effect_deps et inst))
Proof
  rpt strip_tac >>
  `!eff x. MEM x prefix /\
     MEM eff (effects_to_list (write_effects inst.inst_opcode)) /\
     (MEM eff (effects_to_list (write_effects x.inst_opcode)) \/
      MEM eff (effects_to_list (read_effects x.inst_opcode))) ==>
     R x.inst_id inst.inst_id` by
    metis_tac[effect_history_write_conflict] >>
  qpat_x_assum `effect_history _ _ _` mp_tac >>
  simp[effect_history_def] >> strip_tac >>
  simp[effect_history_def, MEM_APPEND] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `MEM eff (effects_to_list (write_effects inst.inst_opcode))` >>
      simp[compute_effect_last_write] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `MEM eff (effects_to_list (write_effects inst.inst_opcode))` >>
      simp[compute_effect_reads, compute_effect_last_write] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >>
      Cases_on `MEM eff (effects_to_list (write_effects inst.inst_opcode))` >>
      simp[compute_effect_last_write] >> metis_tac[]) >>
  rpt gen_tac >> simp[compute_effect_reads] >> metis_tac[]
QED

Theorem effect_scan_lookup_preserved:
  !suffix acc et k.
    ~MEM k (MAP (\i. i.inst_id) suffix) ==>
    FLOOKUP (FST (FOLDL (\(m, s) i.
      (m |+ (i.inst_id, FST (compute_effect_deps s i)),
       SND (compute_effect_deps s i))) (acc, et) suffix)) k =
    FLOOKUP acc k
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then
    [`acc |+ (h.inst_id, FST (compute_effect_deps et h))`,
     `SND (compute_effect_deps et h)`, `k`] mp_tac) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem effect_scan_lookup_source:
  !prefix acc et k ds.
  FLOOKUP (FST (FOLDL (\(m, s) i.
    (m |+ (i.inst_id, FST (compute_effect_deps s i)),
     SND (compute_effect_deps s i))) (acc, et) prefix)) k = SOME ds ==>
  MEM k (MAP (\i. i.inst_id) prefix) \/ FLOOKUP acc k = SOME ds
Proof
  rpt gen_tac >> Cases_on `MEM k (MAP (\i. i.inst_id) prefix)` >>
  simp[effect_scan_lookup_preserved]
QED

Theorem effect_scan_history:
  !suffix prefix acc et R.
    ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ suffix)) /\
    effect_history R prefix et /\ transitive R /\
    (!k ds d.
       FLOOKUP (FST (FOLDL (\(m, s) i.
         (m |+ (i.inst_id, FST (compute_effect_deps s i)),
          SND (compute_effect_deps s i))) (acc, et) suffix)) k = SOME ds /\
       MEM d ds ==> R d.inst_id k) ==>
    effect_history R (prefix ++ suffix)
      (SND (FOLDL (\(m, s) i.
         (m |+ (i.inst_id, FST (compute_effect_deps s i)),
          SND (compute_effect_deps s i))) (acc, et) suffix))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `~MEM h.inst_id (MAP (\i. i.inst_id) suffix)` by
    gvs[ALL_DISTINCT_APPEND] >>
  `!d. MEM d (FST (compute_effect_deps et h)) ==> R d.inst_id h.inst_id` by
    (rpt strip_tac >>
     qpat_x_assum `!k ds d. _` (qspecl_then
       [`h.inst_id`, `FST (compute_effect_deps et h)`, `d`] mp_tac) >>
     simp[effect_scan_lookup_preserved, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `effect_history R (prefix ++ [h]) (SND (compute_effect_deps et h))` by
    (irule effect_history_step >> simp[]) >>
  first_x_assum (qspecl_then
    [`prefix ++ [h]`, `acc |+ (h.inst_id, FST (compute_effect_deps et h))`,
     `SND (compute_effect_deps et h)`, `R`] mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem effect_scan_prefix_history:
  ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ suffix)) /\ transitive R /\
  FOLDL (\(m, s) i.
    (m |+ (i.inst_id, FST (compute_effect_deps s i)),
     SND (compute_effect_deps s i))) (FEMPTY, empty_effect_track) prefix =
    (acc, et) /\
  (!k ds d.
    FLOOKUP (FST (FOLDL (\(m, s) i.
      (m |+ (i.inst_id, FST (compute_effect_deps s i)),
       SND (compute_effect_deps s i))) (acc, et) suffix)) k = SOME ds /\
    MEM d ds ==> R d.inst_id k) ==>
  effect_history R prefix et
Proof
  rpt strip_tac >>
  `!k ds. FLOOKUP acc k = SOME ds ==>
           MEM k (MAP (\i. i.inst_id) prefix)` by
    (rpt strip_tac >>
     qspecl_then [`prefix`, `FEMPTY`, `empty_effect_track`]
       mp_tac effect_scan_lookup_source >>
     simp[finite_mapTheory.FLOOKUP_EMPTY] >>
     disch_then drule >> simp[]) >>
  `!k ds d. FLOOKUP acc k = SOME ds /\ MEM d ds ==> R d.inst_id k` by
    (rpt strip_tac >>
     `~MEM k (MAP (\i. i.inst_id) suffix)` by
       (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
     qpat_x_assum `!k ds d. _` (qspecl_then [`k`, `ds`, `d`] mp_tac) >>
     simp[effect_scan_lookup_preserved]) >>
  qspecl_then [`prefix`, `[]`] mp_tac effect_scan_history >>
  disch_then (qspecl_then [`FEMPTY`, `empty_effect_track`, `R`] mp_tac) >>
  gvs[effect_history_empty, ALL_DISTINCT_APPEND]
QED

Theorem effect_scan_conflict:
  ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ inst::suffix)) /\ transitive R /\
  (!k ds d.
    FLOOKUP (FST (FOLDL (\(m, s) i.
      (m |+ (i.inst_id, FST (compute_effect_deps s i)),
       SND (compute_effect_deps s i)))
      (FEMPTY, empty_effect_track) (prefix ++ inst::suffix))) k = SOME ds /\
    MEM d ds ==> R d.inst_id k) /\
  MEM x prefix /\ ~effects_independent x.inst_opcode inst.inst_opcode ==>
  R x.inst_id inst.inst_id
Proof
  rpt strip_tac >>
  Cases_on `FOLDL (\(m, s) i.
    (m |+ (i.inst_id, FST (compute_effect_deps s i)),
     SND (compute_effect_deps s i))) (FEMPTY, empty_effect_track) prefix` >>
  rename1 `_ = (acc, et)` >>
  `effect_history R prefix et` by
    (irule effect_scan_prefix_history >> simp[] >>
     qexists `inst::suffix` >>
     gvs[FOLDL_APPEND]) >>
  `~MEM inst.inst_id (MAP (\i. i.inst_id) suffix)` by
    gvs[ALL_DISTINCT_APPEND] >>
  `!d. MEM d (FST (compute_effect_deps et inst)) ==> R d.inst_id inst.inst_id` by
    (rpt strip_tac >>
     qpat_x_assum `!k ds d. _` (qspecl_then
       [`inst.inst_id`, `FST (compute_effect_deps et inst)`, `d`] mp_tac) >>
     simp[FOLDL_APPEND, effect_scan_lookup_preserved,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  irule effect_history_conflict >> simp[] >>
  qexistsl [`et`, `prefix`] >> simp[] >>
  gvs[ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[]
QED

Theorem build_eda_scan:
  build_eda bi =
    FST (FOLDL (\(m, s) i.
      (m |+ (i.inst_id, FST (compute_effect_deps s i)),
       SND (compute_effect_deps s i)))
      (FEMPTY, empty_effect_track) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  simp[build_eda_def] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM] >> Cases >> rpt gen_tac >>
  rename1 `compute_effect_deps et inst` >>
  Cases_on `compute_effect_deps et inst` >> simp[]
QED

Theorem build_eda_conflict_order:
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\ transitive R /\
  (!k ds d. FLOOKUP (build_eda bi) k = SOME ds /\ MEM d ds ==>
            R d.inst_id k) /\
  FILTER (\i. ~is_pseudo i.inst_opcode) bi = prefix ++ y::suffix /\
  MEM x prefix /\ ~effects_independent x.inst_opcode y.inst_opcode ==>
  R x.inst_id y.inst_id
Proof
  rpt strip_tac >> irule effect_scan_conflict >> simp[] >>
  qexistsl [`prefix`, `suffix`] >> gvs[build_eda_scan]
QED

Theorem dft_block_suffix_eda:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions ==>
  output_eda_before (build_eda bb.bb_instructions)
    (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions)
Proof
  rpt strip_tac >>
  qspecl_then [`order`, `bb`] mp_tac dft_block_suffix_decomposition >>
  simp[Once dft_block_def, LET_THM] >> disch_then (SUBST1_TAC o SYM) >>
  irule schedule_output_eda_before >>
  simp[build_eda_wf, entry_instructions_mem] >>
  conj_tac >- gvs[bb_well_formed_def] >>
  conj_tac >- gvs[non_pseudo_defs_before_uses_def] >>
  conj_tac >- gvs[bb_well_formed_def] >>
  irule eda_topo_compatible_gen_weak_plain >>
  gvs[bb_well_formed_def, non_pseudo_defs_before_uses_def]
QED

Theorem build_eda_key_member:
  FLOOKUP (build_eda bi) k = SOME ds ==>
  MEM k (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  simp[build_eda_scan] >> strip_tac >>
  drule effect_scan_lookup_source >> simp[finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem output_eda_order_edge:
  output_eda_before (build_eda bi) sched_out /\
  PERM (MAP (\i. i.inst_id) sched_out)
       (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
  FLOOKUP (build_eda bi) k = SOME ds /\ MEM d ds ==>
  id_before (MAP (\i. i.inst_id) sched_out) d.inst_id k
Proof
  rpt strip_tac >>
  `MEM k (MAP (\i. i.inst_id) sched_out)` by
    metis_tac[build_eda_key_member, sortingTheory.PERM_MEM_EQ] >>
  `?j. j < LENGTH sched_out /\ (EL j sched_out).inst_id = k` by
    (gvs[MEM_EL, EL_MAP] >> metis_tac[]) >>
  `~is_pseudo d.inst_opcode` by
    metis_tac[build_eda_wf, eda_wf_def] >>
  gvs[output_eda_before_def] >>
  first_x_assum (qspecl_then [`j`, `d`] mp_tac) >> simp[] >> strip_tac >>
  simp[id_before_def] >> qexistsl [`m`, `j`] >> simp[EL_MAP]
QED

Theorem id_before_map_split:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM x bi /\ MEM y bi /\
  id_before (MAP (\i. i.inst_id) bi) x.inst_id y.inst_id ==>
  ?prefix suffix. bi = prefix ++ y::suffix /\ MEM x prefix
Proof
  rpt strip_tac >>
  `!a b. MEM a bi /\ MEM b bi /\ a.inst_id = b.inst_id ==> a = b` by
    metis_tac[all_distinct_map_mem_inj] >>
  `?prefix suffix. bi = prefix ++ y::suffix` by metis_tac[MEM_SPLIT] >>
  qpat_x_assum `bi = _` SUBST_ALL_TAC >>
  qexistsl [`prefix`, `suffix`] >> simp[] >>
  spose_not_then assume_tac >>
  `~MEM x.inst_id (MAP (\i. i.inst_id) prefix)` by
    (simp[MEM_MAP] >> rpt strip_tac >>
     `x = i` by metis_tac[MEM_APPEND, MEM] >>
     gvs[]) >>
  `~MEM y.inst_id (MAP (\i. i.inst_id) prefix) /\
   ~MEM y.inst_id (MAP (\i. i.inst_id) suffix)` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  gvs[id_before_append_suffix, id_before_cons] >>
  metis_tac[id_before_mem]
QED

Theorem id_before_non_pseudo:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM x bi /\ MEM y bi /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bi) x.inst_id y.inst_id ==>
  id_before (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
    x.inst_id y.inst_id
Proof
  rpt strip_tac >>
  `!i. MEM i bi /\ (i.inst_id = x.inst_id \/ i.inst_id = y.inst_id) ==>
       ~is_pseudo i.inst_opcode` by
    (rpt strip_tac >>
     metis_tac[all_distinct_map_mem_inj]) >>
  drule (SIMP_RULE (srw_ss()) []
    (Q.ISPECL [`\i. i.inst_id`, `\i. ~is_pseudo i.inst_opcode`]
      (Q.GENL [`f`, `P`] id_before_map_filter))) >> simp[]
QED

Theorem dft_block_suffix_effect_order:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
  ~effects_independent x.inst_opcode y.inst_opcode ==>
  id_before
    (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions))
    x.inst_id y.inst_id
Proof
  rpt strip_tac >>
  drule_all dft_block_suffix_structure >>
  disch_then (qspec_then `order` strip_assume_tac) >>
  `output_eda_before (build_eda bb.bb_instructions)
    (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions)` by
    metis_tac[dft_block_suffix_eda] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
    metis_tac[all_distinct_map_filter] >>
  `id_before (MAP (\i. i.inst_id)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))
    x.inst_id y.inst_id` by metis_tac[id_before_non_pseudo] >>
  `?prefix suffix. FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions =
    prefix ++ y::suffix /\ MEM x prefix` by
    (irule id_before_map_split >> simp[MEM_FILTER]) >>
  irule build_eda_conflict_order >> simp[] >>
  conj_tac
  >- (simp[relationTheory.transitive_def] >> rpt strip_tac >>
      irule id_before_trans >> conj_tac
      >- metis_tac[sortingTheory.ALL_DISTINCT_PERM, sortingTheory.PERM_SYM] >>
      metis_tac[]) >>
  qexistsl [`bb.bb_instructions`, `prefix`, `suffix`] >> simp[] >>
  metis_tac[output_eda_order_edge]
QED

Theorem inst_data_deps_has_outputs:
  !bi order i d. MEM d (inst_data_deps bi order i) ==> d.inst_outputs <> []
Proof
  rpt gen_tac >>
  simp[inst_data_deps_def, MEM_nub_first, MEM_MAP, MEM_FILTER] >>
  Cases_on `is_terminator i.inst_opcode` >> simp[MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >>
  TRY (rename1 `operand_producer bi op = SOME _` >>
       Cases_on `op` >> gvs[operand_producer_def]) >>
  metis_tac[producing_inst_mem_outputs, MEM]
QED

Theorem compute_effect_dep_frontier:
  MEM d (FST (compute_effect_deps et inst)) ==>
  ?eff. MEM d (et_get_reads et eff) \/
        FLOOKUP et.et_last_write eff = SOME d
Proof
  simp[compute_effect_deps_def, MEM_nub_first, MEM_FLAT, MEM_MAP,
       MEM_FILTER, PULL_EXISTS] >>
  rpt strip_tac
  >- metis_tac[]
  >- (Cases_on `FLOOKUP et.et_last_write weff` >> gvs[] >> metis_tac[]) >>
  gvs[optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >> metis_tac[]
QED

Theorem compute_effect_dep_has_effects:
  effect_history R prefix et /\ MEM d (FST (compute_effect_deps et inst)) ==>
  read_effects d.inst_opcode <> empty_effects \/
  write_effects d.inst_opcode <> empty_effects
Proof
  strip_tac >> drule compute_effect_dep_frontier >> strip_tac >>
  gvs[effect_history_def] >>
  `effects_to_list empty_effects = []` by EVAL_TAC >>
  metis_tac[MEM]
QED

Theorem effect_scan_deps_have_effects:
  !suffix prefix acc et.
  effect_history (\a b. T) prefix et /\
  (!k ds d. FLOOKUP acc k = SOME ds /\ MEM d ds ==>
    read_effects d.inst_opcode <> empty_effects \/
    write_effects d.inst_opcode <> empty_effects) ==>
  !k ds d.
    FLOOKUP (FST (FOLDL (\(m, s) i.
      (m |+ (i.inst_id, FST (compute_effect_deps s i)),
       SND (compute_effect_deps s i))) (acc, et) suffix)) k = SOME ds /\
    MEM d ds ==>
    read_effects d.inst_opcode <> empty_effects \/
    write_effects d.inst_opcode <> empty_effects
Proof
  Induct >- (simp[] >> metis_tac[]) >>
  pure_rewrite_tac[FOLDL] >> CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then
    [`prefix ++ [h]`, `acc |+ (h.inst_id, FST (compute_effect_deps et h))`,
     `SND (compute_effect_deps et h)`] mp_tac) >>
  impl_tac >- (conj_tac
  >- (irule effect_history_step >> simp[relationTheory.transitive_def]) >>
  rpt gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `h.inst_id = k` >> simp[] >> rpt strip_tac >>
  metis_tac[compute_effect_dep_has_effects]) >> simp[]
QED

Theorem build_eda_deps_have_effects:
  FLOOKUP (build_eda bi) k = SOME ds /\ MEM d ds ==>
  read_effects d.inst_opcode <> empty_effects \/
  write_effects d.inst_opcode <> empty_effects
Proof
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`, `[]`,
               `FEMPTY`, `empty_effect_track`]
    mp_tac effect_scan_deps_have_effects >>
  simp[effect_history_empty, finite_mapTheory.FLOOKUP_EMPTY] >>
  simp[build_eda_scan] >> metis_tac[]
QED

Theorem root_not_dep_target:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM r bi /\
  r.inst_outputs = [] /\ read_effects r.inst_opcode = empty_effects /\
  write_effects r.inst_opcode = empty_effects /\
  MEM d (inst_all_deps bi order (build_eda bi) i) ==>
  d.inst_id <> r.inst_id
Proof
  rpt strip_tac >>
  `MEM d bi` by metis_tac[inst_all_deps_mem, build_eda_wf] >>
  `d = r` by metis_tac[all_distinct_map_mem_inj] >> gvs[] >>
  qpat_x_assum `MEM _ (inst_all_deps _ _ _ _)` mp_tac >>
  simp[inst_all_deps_def, MEM_nub_first] >> strip_tac
  >- metis_tac[inst_data_deps_has_outputs] >>
  Cases_on `FLOOKUP (build_eda bi) i.inst_id` >> gvs[] >>
  metis_tac[build_eda_deps_have_effects]
QED

Theorem root_is_entry:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM r bi /\
  ~is_pseudo r.inst_opcode /\ r.inst_outputs = [] /\
  read_effects r.inst_opcode = empty_effects /\
  write_effects r.inst_opcode = empty_effects ==>
  MEM r (entry_instructions bi order (build_eda bi))
Proof
  rpt strip_tac >>
  simp[entry_instructions_def, MEM_FILTER, MEM_nub] >>
  spose_not_then assume_tac >>
  gvs[MEM_FLAT, MEM_MAP, MEM_FILTER] >>
  metis_tac[root_not_dep_target]
QED

(* A cut separates all work strictly earlier than a distinguished root from
   the untouched suffix of entries. Process items retain source instructions;
   emit items need only retain their IDs (operand flipping is harmless). *)
Definition dfs_cut_work_def:
  (dfs_cut_work bi P (DfsProcess i) <=> MEM i bi /\ P i.inst_id) /\
  (dfs_cut_work bi P (DfsEmit i) <=> P i.inst_id)
End

Definition dfs_cut_done_def:
  dfs_cut_done P rid out <=>
    ?pre post. MAP (\i. i.inst_id) out = pre ++ [rid] ++ post /\ EVERY P pre
End

Definition dfs_cut_def:
  dfs_cut bi P r s <=>
    dfs_cut_done P r.inst_id s.ds_output \/
    (EVERY (\i. P i.inst_id) s.ds_output /\
     ?work tail marker.
       s.ds_stack = work ++ [marker] ++ tail /\
       EVERY (dfs_cut_work bi P) work /\
       ((marker = DfsProcess r /\ ~MEM r.inst_id s.ds_visited) \/
        ?i. marker = DfsEmit i /\ i.inst_id = r.inst_id))
End

Theorem dfs_cut_init:
  EVERY (\i. MEM i bi /\ P i.inst_id) pre ==>
  dfs_cut bi P r
    <| ds_stack := MAP DfsProcess pre ++ [DfsProcess r] ++ MAP DfsProcess post;
       ds_output := []; ds_visited := [] |>
Proof
  strip_tac >> simp[dfs_cut_def] >> disj2_tac >>
  qexistsl [`MAP DfsProcess pre`, `MAP DfsProcess post`, `DfsProcess r`] >>
  gvs[EVERY_MAP, EVERY_MEM, dfs_cut_work_def]
QED

Theorem dfs_cut_done_append:
  dfs_cut_done P rid out ==> dfs_cut_done P rid (out ++ more)
Proof
  rw[dfs_cut_done_def] >> qexistsl [`pre`, `post ++ MAP (\i. i.inst_id) more`] >>
  simp[]
QED

Theorem dfs_cut_done_step:
  dfs_cut_done P rid s.ds_output ==>
  dfs_cut_done P rid (dfs_step bi order eda om do_flip s).ds_output
Proof
  strip_tac >> Cases_on `s.ds_stack` >> simp[dfs_step_def] >>
  rename1 `item :: rest` >> Cases_on `item` >>
  simp[dfs_step_def, LET_THM, dfs_cut_done_append] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem dfs_cut_children:
  (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
         (P i.inst_id \/ i.inst_id = r.inst_id) /\
         MEM d (inst_all_deps bi order eda i) ==> MEM d bi /\ P d.inst_id) /\
  MEM i bi /\ ~is_pseudo i.inst_opcode /\
  (P i.inst_id \/ i.inst_id = r.inst_id) ==>
  EVERY (dfs_cut_work bi P)
    (MAP DfsProcess
      (sort_children bi order eda om i (inst_all_deps bi order eda i)))
Proof
  simp[EVERY_MAP, EVERY_MEM, dfs_cut_work_def] >>
  metis_tac[sort_children_mem]
QED

Theorem dfs_cut_pending:
  EVERY (\i. P i.inst_id) s.ds_output /\
  s.ds_stack = work ++ [marker] ++ tail /\
  EVERY (dfs_cut_work bi P) work /\
  ((marker = DfsProcess r /\ ~MEM r.inst_id s.ds_visited) \/
   ?i. marker = DfsEmit i /\ i.inst_id = r.inst_id) ==>
  dfs_cut bi P r s
Proof
  simp[dfs_cut_def] >> metis_tac[]
QED

Theorem dfs_cut_work_step:
  (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
         (P i.inst_id \/ i.inst_id = r.inst_id) /\
         MEM d (inst_all_deps bi order eda i) ==> MEM d bi /\ P d.inst_id) /\
  ~P r.inst_id /\
  EVERY (\i. P i.inst_id) s.ds_output /\
  s.ds_stack = (h :: work) ++ [marker] ++ tail /\
  dfs_cut_work bi P h /\ EVERY (dfs_cut_work bi P) work /\
  ((marker = DfsProcess r /\ ~MEM r.inst_id s.ds_visited) \/
   ?i. marker = DfsEmit i /\ i.inst_id = r.inst_id) ==>
  dfs_cut bi P r (dfs_step bi order eda om do_flip s)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `h` >> gns[dfs_cut_work_def]
  >- (rename1 `MEM inst bi /\ P inst.inst_id` >>
      `inst.inst_id <> r.inst_id` by metis_tac[] >>
      Cases_on `MEM inst.inst_id s.ds_visited`
      >- (irule dfs_cut_pending >>
          (conj_tac >- simp[dfs_step_def]) >>
          qexistsl [`marker`, `tail`, `work`] >>
          simp[dfs_step_def]) >>
      Cases_on `is_pseudo inst.inst_opcode`
      >- (irule dfs_cut_pending >>
          (conj_tac >- simp[dfs_step_def]) >>
          qexistsl [`marker`, `tail`, `work`] >>
          simp[dfs_step_def]) >>
      `EVERY (dfs_cut_work bi P)
        (MAP DfsProcess (sort_children bi order eda om inst
          (inst_all_deps bi order eda inst)))` by
        (irule dfs_cut_children >> metis_tac[]) >>
      irule dfs_cut_pending >>
      (conj_tac >- simp[dfs_step_def, LET_THM]) >>
      qexistsl [`marker`, `tail`,
        `MAP DfsProcess (sort_children bi order eda om inst
          (inst_all_deps bi order eda inst)) ++
         [DfsEmit (if do_flip /\ is_flippable inst.inst_opcode /\
           sort_children bi order eda om inst (inst_all_deps bi order eda inst) <>
             inst_all_deps bi order eda inst
          then flip_operands inst else inst)] ++ work`] >>
      simp[dfs_step_def, LET_THM, dfs_cut_work_def] >>
      IF_CASES_TAC >> simp[]) >>
  irule dfs_cut_pending >> (conj_tac >- simp[dfs_step_def]) >>
  qexistsl [`marker`, `tail`, `work`] >> simp[dfs_step_def]
QED

Theorem dfs_cut_marker_step:
  (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
         (P i.inst_id \/ i.inst_id = r.inst_id) /\
         MEM d (inst_all_deps bi order eda i) ==> MEM d bi /\ P d.inst_id) /\
  MEM r bi /\ ~is_pseudo r.inst_opcode /\
  EVERY (\i. P i.inst_id) s.ds_output /\
  s.ds_stack = marker :: tail /\
  ((marker = DfsProcess r /\ ~MEM r.inst_id s.ds_visited) \/
   ?i. marker = DfsEmit i /\ i.inst_id = r.inst_id) ==>
  dfs_cut bi P r (dfs_step bi order eda om do_flip s)
Proof
  strip_tac >> gvs[]
  >- (`EVERY (dfs_cut_work bi P)
        (MAP DfsProcess (sort_children bi order eda om r
          (inst_all_deps bi order eda r)))` by
        (irule dfs_cut_children >> metis_tac[]) >>
      simp[dfs_step_def, LET_THM] >>
      qmatch_goalsub_abbrev_tac `DfsEmit inst` >>
      `inst.inst_id = r.inst_id` by (simp[Abbr `inst`] >>
        IF_CASES_TAC >> simp[]) >>
      irule dfs_cut_pending >> simp[] >>
      qexistsl [`DfsEmit inst`, `tail`,
        `MAP DfsProcess (sort_children bi order eda om r
          (inst_all_deps bi order eda r))`] >> simp[]) >>
  simp[dfs_step_def, dfs_cut_def] >> disj1_tac >>
  simp[dfs_cut_done_def] >>
  qexistsl [`MAP (\i. i.inst_id) s.ds_output`, `[]`] >>
  gvs[EVERY_MAP]
QED

Theorem dfs_cut_step:
  (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
         (P i.inst_id \/ i.inst_id = r.inst_id) /\
         MEM d (inst_all_deps bi order eda i) ==> MEM d bi /\ P d.inst_id) /\
  MEM r bi /\ ~is_pseudo r.inst_opcode /\ ~P r.inst_id /\
  dfs_cut bi P r s ==>
  dfs_cut bi P r (dfs_step bi order eda om do_flip s)
Proof
  rpt strip_tac >>
  qpat_x_assum `dfs_cut bi P r s`
    (strip_assume_tac o REWRITE_RULE [dfs_cut_def])
  >- (simp[dfs_cut_def] >> metis_tac[dfs_cut_done_step]) >>
  (Cases_on `work`
   >- (irule dfs_cut_marker_step >> gvs[] >> metis_tac[])) >>
  irule dfs_cut_work_step >> gvs[] >> metis_tac[]
QED

Theorem dfs_cut_run:
  (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
         (P i.inst_id \/ i.inst_id = r.inst_id) /\
         MEM d (inst_all_deps bi order eda i) ==> MEM d bi /\ P d.inst_id) /\
  MEM r bi /\ ~is_pseudo r.inst_opcode /\ ~P r.inst_id /\
  dfs_cut bi P r s ==>
  dfs_cut bi P r (FUNPOW (dfs_step bi order eda om do_flip) n s)
Proof
  qid_spec_tac `s` >> Induct_on `n` >> simp[arithmeticTheory.FUNPOW] >>
  rpt strip_tac >> first_x_assum irule >>
  (conj_tac >- metis_tac[]) >> simp[] >>
  irule dfs_cut_step >> simp[] >> metis_tac[]
QED

Theorem dfs_cut_done_before:
  dfs_cut_done P rid out /\ ~P rid /\ ~P yid /\ rid <> yid /\
  MEM yid (MAP (\i. i.inst_id) out) ==>
  id_before (MAP (\i. i.inst_id) out) rid yid
Proof
  rw[dfs_cut_done_def] >>
  `~MEM rid pre /\ ~MEM yid pre` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  gvs[] >> pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
  asm_rewrite_tac[APPEND] >> simp[id_before_append_suffix, id_before_cons]
QED

Theorem dfs_cut_before:
  dfs_cut bi P r s /\ ~P r.inst_id /\ ~P yid /\ r.inst_id <> yid /\
  MEM yid (MAP (\i. i.inst_id) s.ds_output) ==>
  id_before (MAP (\i. i.inst_id) s.ds_output) r.inst_id yid
Proof
  rw[dfs_cut_def]
  >- metis_tac[dfs_cut_done_before] >>
  gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem schedule_cut_before:
  (!i d. MEM i bi /\ ~is_pseudo i.inst_opcode /\
         (P i.inst_id \/ i.inst_id = r.inst_id) /\
         MEM d (inst_all_deps bi order eda i) ==> MEM d bi /\ P d.inst_id) /\
  MEM r bi /\ ~is_pseudo r.inst_opcode /\ ~P r.inst_id /\
  EVERY (\i. MEM i bi /\ P i.inst_id) pre /\
  ~P yid /\ r.inst_id <> yid /\
  MEM yid (MAP (\i. i.inst_id)
    (schedule_from_entries bi order eda om (pre ++ [r] ++ post))) ==>
  id_before (MAP (\i. i.inst_id)
    (schedule_from_entries bi order eda om (pre ++ [r] ++ post))) r.inst_id yid
Proof
  rpt strip_tac >> fs[schedule_from_entries_def, LET_THM] >>
  irule dfs_cut_before >> simp[] >>
  qexistsl [`P`, `bi`] >> simp[] >>
  irule dfs_cut_run >> simp[dfs_cut_init] >> metis_tac[]
QED

Definition dft_root_cut_def:
  dft_root_cut bi rid iid <=>
    (?i. MEM i bi /\ is_pseudo i.inst_opcode /\ i.inst_id = iid) \/
    id_before (MAP (\i. i.inst_id) bi) iid rid
End

Theorem dft_root_cut_non_pseudo:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM i bi /\
  ~is_pseudo i.inst_opcode ==>
  (dft_root_cut bi rid i.inst_id <=>
   id_before (MAP (\i. i.inst_id) bi) i.inst_id rid)
Proof
  rw[dft_root_cut_def] >>
  metis_tac[all_distinct_map_mem_inj]
QED

Theorem dft_root_cut_closed:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  eda_wf eda bi /\ eda_topo_compatible bi eda order /\
  MEM i bi /\ ~is_pseudo i.inst_opcode /\
  (dft_root_cut bi r.inst_id i.inst_id \/ i.inst_id = r.inst_id) /\
  MEM d (inst_all_deps bi order eda i) ==>
  MEM d bi /\ dft_root_cut bi r.inst_id d.inst_id
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM d bi` by metis_tac[inst_all_deps_mem] >> simp[] >>
  Cases_on `is_pseudo d.inst_opcode`
  >- (simp[dft_root_cut_def] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) bi) d.inst_id i.inst_id` by
    (fs[eda_topo_compatible_def] >>
     qpat_x_assum `!inst dep. _`
       (qspecl_then [`i`, `d`] mp_tac) >> simp[] >>
     strip_tac >> rename1 `EL k bi = d` >>
     simp[id_before_def] >> qexistsl [`k`, `j`] >> simp[EL_MAP]) >>
  simp[dft_root_cut_def] >> disj2_tac >>
  metis_tac[dft_root_cut_non_pseudo, id_before_trans]
QED

Theorem id_before_append_member:
  MEM a pre /\ MEM b post ==> id_before (pre ++ post) a b
Proof
  Induct_on `pre` >> simp[id_before_cons] >> metis_tac[MEM_APPEND]
QED

Theorem dft_root_cut_entries:
  MEM r (FILTER Q bi) ==>
  ?pre post. FILTER Q bi = pre ++ [r] ++ post /\
    EVERY (\i. MEM i bi /\ dft_root_cut bi r.inst_id i.inst_id) pre
Proof
  simp[MEM_FILTER] >> strip_tac >>
  `?prefix suffix. bi = prefix ++ r::suffix` by metis_tac[MEM_SPLIT] >>
  qpat_x_assum `bi = _` SUBST_ALL_TAC >>
  qexistsl [`FILTER Q prefix`, `FILTER Q suffix`] >>
  simp[rich_listTheory.FILTER_APPEND, EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
  simp[dft_root_cut_def] >> disj2_tac >>
  simp[] >> irule id_before_append_member >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem schedule_root_cut_before:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  eda_wf eda bi /\ eda_topo_compatible bi eda order /\
  MEM r bi /\ ~is_pseudo r.inst_opcode /\
  MEM y bi /\ ~is_pseudo y.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bi) r.inst_id y.inst_id /\
  MEM r (entry_instructions bi order eda) /\
  MEM y.inst_id (MAP (\i. i.inst_id)
    (schedule_from_entries bi order eda om (entry_instructions bi order eda))) ==>
  id_before (MAP (\i. i.inst_id)
    (schedule_from_entries bi order eda om (entry_instructions bi order eda)))
    r.inst_id y.inst_id
Proof
  rpt strip_tac >>
  `?Q. entry_instructions bi order eda = FILTER Q bi` by
    (simp[entry_instructions_def, rich_listTheory.FILTER_FILTER] >> metis_tac[]) >>
  `?pre post. entry_instructions bi order eda = pre ++ [r] ++ post /\
     EVERY (\i. MEM i bi /\ dft_root_cut bi r.inst_id i.inst_id) pre` by
    metis_tac[dft_root_cut_entries] >>
  `~dft_root_cut bi r.inst_id r.inst_id /\
   ~dft_root_cut bi r.inst_id y.inst_id /\ r.inst_id <> y.inst_id` by
    (simp[dft_root_cut_non_pseudo] >>
     metis_tac[id_before_distinct_endpoints, id_before_trans]) >>
  qpat_x_assum `entry_instructions _ _ _ = pre ++ [r] ++ post` SUBST_ALL_TAC >>
  irule schedule_cut_before >> simp[] >>
  qexists `dft_root_cut bi r.inst_id` >> simp[] >>
  metis_tac[dft_root_cut_closed]
QED

Theorem dft_block_suffix_root_order:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  MEM r bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo r.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  r.inst_outputs = [] /\ read_effects r.inst_opcode = empty_effects /\
  write_effects r.inst_opcode = empty_effects /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) r.inst_id y.inst_id ==>
  id_before
    (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions))
    r.inst_id y.inst_id
Proof
  rpt strip_tac >>
  `MEM y.inst_id (MAP (\i. i.inst_id)
     (FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions))` by
    (drule_all dft_block_suffix_representative >> strip_tac >>
     simp[MEM_MAP] >> metis_tac[MEM_EL, flip_operands_inst_id]) >>
  qspecl_then [`order`, `bb`] mp_tac dft_block_suffix_decomposition >>
  simp[Once dft_block_def, LET_THM] >> disch_then (SUBST_ALL_TAC o SYM) >>
  irule schedule_root_cut_before >> simp[build_eda_wf, root_is_entry] >>
  irule eda_topo_compatible_gen_weak_plain >>
  gvs[bb_well_formed_def, non_pseudo_defs_before_uses_def]
QED

Theorem dft_block_rel_step:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
  dft_block_rel bb (dft_block order bb)
Proof
  strip_tac >> simp[dft_block_rel_def] >> conj_tac
  >- simp[dft_block_def, LET_THM] >>
  qexists `FILTER (\i. ~is_pseudo i.inst_opcode)
    (dft_block order bb).bb_instructions` >>
  simp[GSYM dft_block_suffix_decomposition] >> conj_tac
  >- metis_tac[dft_block_suffix_structure] >> conj_tac
  >- metis_tac[dft_block_suffix_structure] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `dft_must_order x y`
    (strip_assume_tac o REWRITE_RULE [dft_must_order_def])
  >- metis_tac[dft_block_suffix_data_order]
  >- (irule dft_block_suffix_effect_order >> simp[] >>
      simp[effects_independent_def] >> metis_tac[])
  >- (irule dft_block_suffix_effect_order >> simp[] >>
      simp[effects_independent_def] >> metis_tac[])
  >- metis_tac[dft_block_suffix_root_order] >>
  metis_tac[dft_block_suffix_terminator_order, id_before_distinct_endpoints]
QED

Theorem dft_block_rel_refl:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  pseudos_prefix bb ==> dft_block_rel bb bb
Proof
  strip_tac >> simp[dft_block_rel_def] >>
  qexists `FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions` >>
  conj_tac
  >- (qpat_x_assum `pseudos_prefix bb` mp_tac >>
      simp[pseudos_prefix_def] >>
      Q.SPEC_TAC (`bb.bb_instructions`, `l`) >> Induct >> simp[] >>
      gen_tac >> ASM_CASES_TAC ``is_pseudo h.inst_opcode`` >> simp[] >> strip_tac
      >- (first_x_assum irule >> rpt strip_tac >>
          qpat_x_assum `!i j. _`
            (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      `EVERY (\i. ~is_pseudo i.inst_opcode) l` by
        (simp[EVERY_MEM] >> rpt strip_tac >>
         `?j. j < LENGTH l /\ EL j l = i` by metis_tac[MEM_EL] >>
         qpat_x_assum `!i j. _`
           (qspecl_then [`0`, `SUC j`] mp_tac) >> simp[]) >>
      `FILTER (\i. is_pseudo i.inst_opcode) l = []` by
        (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM]) >>
      `FILTER (\i. ~is_pseudo i.inst_opcode) l = l` by
        simp[FILTER_EQ_ID] >> simp[]) >>
  simp[EVERY_MEM, MEM_FILTER, from_block_def] >>
  metis_tac[id_before_non_pseudo]
QED

Theorem dft_block_rel_body:
  dft_block_rel a b ==>
  b.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) a.bb_instructions ++
    FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions
Proof
  rw[dft_block_rel_def] >> rename1 `EVERY (from_block _) bod` >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) bod` by
    (gvs[EVERY_MEM, from_block_def] >> metis_tac[flip_operands_is_pseudo]) >>
  simp[rich_listTheory.FILTER_APPEND, rich_listTheory.FILTER_FILTER,
       FILTER_EQ_NIL, FILTER_EQ_ID, EVERY_MEM] >> gvs[EVERY_MEM]
QED

Theorem dft_block_rel_pseudos:
  dft_block_rel a b ==>
  FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions =
  FILTER (\i. is_pseudo i.inst_opcode) a.bb_instructions
Proof
  strip_tac >> drule dft_block_rel_body >> disch_then SUBST1_TAC >>
  simp[rich_listTheory.FILTER_APPEND, rich_listTheory.FILTER_FILTER,
       FILTER_EQ_NIL]
QED

Theorem dft_block_rel_normal:
  dft_block_rel a b ==>
  b.bb_label = a.bb_label /\
  b.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) a.bb_instructions ++
    FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions /\
  PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions))
       (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) a.bb_instructions)) /\
  EVERY (from_block a.bb_instructions)
    (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions) /\
  (!x y. MEM x a.bb_instructions /\ MEM y a.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) a.bb_instructions) x.inst_id y.inst_id /\
    dft_must_order x y ==>
    id_before (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions)) x.inst_id y.inst_id)
Proof
  strip_tac >> drule dft_block_rel_body >>
  gvs[dft_block_rel_def] >> disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Theorem dft_block_rel_representative:
  dft_block_rel a b /\ MEM x a.bb_instructions /\ ~is_pseudo x.inst_opcode ==>
  ?z. MEM z b.bb_instructions /\ ~is_pseudo z.inst_opcode /\
      from_block a.bb_instructions z /\ z.inst_id = x.inst_id
Proof
  strip_tac >> drule dft_block_rel_normal >> strip_tac >>
  `MEM x.inst_id
    (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions))` by
    (drule sortingTheory.PERM_MEM_EQ >> simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  gvs[MEM_MAP, MEM_FILTER, EVERY_MEM] >> metis_tac[]
QED

Theorem dft_block_rel_trans:
  ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions) /\
  dft_block_rel a b /\ dft_block_rel b c ==> dft_block_rel a c
Proof
  strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions =
   FILTER (\i. is_pseudo i.inst_opcode) a.bb_instructions` by
    metis_tac[dft_block_rel_pseudos] >>
  qpat_assum `dft_block_rel b c` (strip_assume_tac o MATCH_MP dft_block_rel_normal) >>
  qpat_assum `dft_block_rel a b` (strip_assume_tac o MATCH_MP dft_block_rel_normal) >>
  simp[dft_block_rel_def] >>
  qexists `FILTER (\i. ~is_pseudo i.inst_opcode) c.bb_instructions` >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[sortingTheory.PERM_TRANS] >>
  conj_tac
  >- (simp[EVERY_MEM, MEM_FILTER] >> rpt strip_tac >>
      irule from_block_trans >> qexists `b.bb_instructions` >>
      gvs[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `?u. MEM u b.bb_instructions /\ ~is_pseudo u.inst_opcode /\
       from_block a.bb_instructions u /\ u.inst_id = x.inst_id` by
    metis_tac[dft_block_rel_representative] >>
  `?v. MEM v b.bb_instructions /\ ~is_pseudo v.inst_opcode /\
       from_block a.bb_instructions v /\ v.inst_id = y.inst_id` by
    metis_tac[dft_block_rel_representative] >>
  `dft_must_order u v` by
    (irule (iffRL from_block_must_order) >>
     qexistsl [`a.bb_instructions`, `x`, `y`] >> simp[]) >>
  `id_before (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions)) x.inst_id y.inst_id` by
    metis_tac[] >>
  `!pre. id_before (pre ++ MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions)) x.inst_id y.inst_id` by
    (Induct >> simp[id_before_cons]) >>
  `id_before (MAP (\i. i.inst_id) b.bb_instructions) u.inst_id v.inst_id` by
    (qpat_x_assum `b.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
     simp[MAP_APPEND]) >>
  metis_tac[]
QED

Theorem dft_block_rel_replace:
  EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) orig /\
  LIST_REL dft_block_rel orig curr /\
  ALL_DISTINCT (MAP (\b. b.bb_label) curr) /\ MEM bb curr /\
  dft_block_rel bb bb' ==>
  LIST_REL dft_block_rel orig
    (MAP (\b. if b.bb_label = bb.bb_label then bb' else b) curr)
Proof
  strip_tac >> simp[LIST_REL_EL_EQN] >>
  `LENGTH orig = LENGTH curr` by gvs[LIST_REL_EL_EQN] >> simp[] >>
  rpt strip_tac >> simp[EL_MAP] >>
  Cases_on `(EL n curr).bb_label = bb.bb_label`
  >- (`EL n curr = bb` by
        (irule (Q.ISPEC `\b. b.bb_label` all_distinct_map_mem_inj) >>
         simp[] >> qexists `curr` >> simp[MEM_EL] >> metis_tac[]) >>
      simp[] >> irule dft_block_rel_trans >> conj_tac
      >- (gvs[EVERY_EL] >> metis_tac[]) >>
      qexists `bb` >> gvs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  gvs[LIST_REL_EL_EQN]
QED

Theorem dft_block_rel_labels:
  LIST_REL dft_block_rel orig curr ==>
  MAP (\b. b.bb_label) orig = MAP (\b. b.bb_label) curr
Proof
  qid_spec_tac `curr` >> Induct_on `orig` >> Cases_on `curr` >>
  simp[] >> rpt strip_tac >>
  imp_res_tac dft_block_rel_normal >> simp[]
QED

Theorem dft_process_one_block_rel:
  EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) orig /\
  LIST_REL dft_block_rel orig st.dls_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) st.dls_blocks) /\ dft_inv st.dls_blocks ==>
  LIST_REL dft_block_rel orig (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  strip_tac >> simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  `MEM bb st.dls_blocks /\ bb.bb_label = lbl` by
    (gvs[lookup_block_def] >> drule venomExecPropsTheory.FIND_P >>
     simp[] >> metis_tac[venomExecPropsTheory.FIND_MEM]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST1_TAC o SYM) >>
  irule dft_block_rel_replace >> simp[] >>
  irule dft_block_rel_step >> gvs[dft_inv_def, EVERY_MEM]
QED

Theorem dft_loop_step_block_rel:
  EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) orig /\
  LIST_REL dft_block_rel orig (FST trip).dls_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) (FST trip).dls_blocks) /\
  dft_inv (FST trip).dls_blocks ==>
  LIST_REL dft_block_rel orig (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  PairCases_on `trip` >> simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >> Cases_on `trip1` >> simp[] >> strip_tac >>
  `LIST_REL dft_block_rel orig
    (FST (dft_process_one cfg lr fn trip0 h)).dls_blocks` by
    (irule dft_process_one_block_rel >> simp[]) >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> gvs[]
QED

Theorem funpow_dft_loop_block_rel:
  !n trip.
  EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) orig /\
  ALL_DISTINCT (MAP (\b. b.bb_label) orig) /\
  LIST_REL dft_block_rel orig (FST trip).dls_blocks /\
  dft_inv (FST trip).dls_blocks ==>
  LIST_REL dft_block_rel orig (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[arithmeticTheory.FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_block_rel >> simp[] >>
  `LIST_REL dft_block_rel orig
     (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks` by
    (first_x_assum irule >> simp[]) >>
  drule dft_block_rel_labels >> strip_tac >> simp[] >> conj_tac
  >- metis_tac[] >>
  irule funpow_dft_loop_preserves_inv >> simp[]
QED

(* These probes deliberately have indirect conflicts: a cleared reader and
   a superseded writer must still precede the third instruction by transitivity.
   MCOPY also tests the same-effect read/write update. *)
Theorem effect_read_write_write_probe[local]:
  let a = mk_inst 0 MLOAD [] ["a"];
      b = mk_inst 1 MCOPY [] [];
      c = mk_inst 2 MSTORE [] [];
      s1 = SND (compute_effect_deps empty_effect_track a);
      s2 = SND (compute_effect_deps s1 b) in
  MAP (\i. i.inst_id) (FST (compute_effect_deps s1 b)) = [0] /\
  MAP (\i. i.inst_id) (FST (compute_effect_deps s2 c)) = [1] /\
  FLOOKUP s2.et_last_write Eff_MEMORY = SOME b /\
  et_get_reads s2 Eff_MEMORY = [b]
Proof
  EVAL_TAC
QED

Theorem effect_write_write_read_probe[local]:
  let a = mk_inst 0 MSTORE [] [];
      b = mk_inst 1 MSTORE [] [];
      c = mk_inst 2 MLOAD [] ["c"];
      s1 = SND (compute_effect_deps empty_effect_track a);
      s2 = SND (compute_effect_deps s1 b) in
  MAP (\i. i.inst_id) (FST (compute_effect_deps s1 b)) = [0] /\
  MAP (\i. i.inst_id) (FST (compute_effect_deps s2 c)) = [1]
Proof
  EVAL_TAC
QED

(* Why it holds (unchecked notes):
   - Permutation, flips, labels and pseudo prefix: dft_fn_all_perm_of and
     dft_fn_dft_inv (dftCorrectness).  Blocks the loop never reaches come out
     unchanged, which is why fn_pseudos_prefix is needed.
   - A root (no outputs, no effects) is never a dependency: inst_data_deps
     (terminator order deps too) only finds producers, build_eda only records
     instructions with effects.  So it is an entry; entries are processed in
     block order, every dependency is earlier in the block (SSA
     defs-before-uses), so nothing after a root is emitted before it.  The
     terminator is the last entry.
   - Effect conflicts: WAW chain, RAW to the last writer, WAR (reads are
     cleared after a write, but ordered through the intermediate writer).
     schedule_output_eda_before (dftTopoSort) gives dependencies first.
   - Each loop iteration keeps dft_inv, flip_operands keeps outputs, used
     variables, effects and is_terminator, and flips are involutive. *)
Theorem dft_fn_block_rel:
  !fn. wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
       (dft_fn fn).fn_name = fn.fn_name /\
       LIST_REL dft_block_rel fn.fn_blocks (dft_fn fn).fn_blocks
Proof
  rpt strip_tac >>
  `dft_inv fn.fn_blocks` by (irule wf_fn_initial_dft_inv >> simp[]) >>
  `EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) fn.fn_blocks` by
    (gvs[dft_inv_def, EVERY_MEM]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `LIST_REL dft_block_rel fn.fn_blocks fn.fn_blocks` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule dft_block_rel_refl >>
     gvs[EVERY_EL, fn_pseudos_prefix_def] >> metis_tac[MEM_EL]) >>
  simp[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> simp[] >>
  irule funpow_dft_loop_block_rel >> simp[]
QED
