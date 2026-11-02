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
  dftCorrectness dftStructural dftDefs dftTopoSort dftWf passSharedDefs venomWf venomInst venomEffects list

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
  cheat
QED
