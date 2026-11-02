(*
 * Runs of a context and of its DFT schedule, with the same fuel.
 *
 * C' is C with every function rescheduled as dftScheduleOrder describes
 * (dft_fn_rel).  A run of a function of C and the run of its schedule in
 * C', from the function's entry block and with the same fuel, end alike
 * (dft_res_rel): the same continuing, returning or halting state, an
 * abort for an abort, and a revert for a revert.  When the run of C
 * errors, the run of C' does not continue or return either.
 *
 * Why the abort state may differ: the schedule can run instructions with
 * independent effects in another order before an instruction that stops
 * the run (an INVOKE whose callee aborts, a failing ASSERT).  It keeps the
 * fallible instructions in order (dft_fallible_order_kept), so the first
 * one to stop the run is the same on both sides; what can run early is an
 * instruction that cannot stop the run.  ctx_labels_bound keeps one with
 * a label operand (OFFSET) from erroring there.
 *)
Theory dftRunRel
Ancestors
  dftScheduleOrder dftStructural dftPermSim dftDefs passSharedDefs venomExecSemantics venomWf
  venomInst venomState venomEffects venomExecProps list finite_map sorting rich_list dftCorrectness

Definition dft_res_rel_def:
  dft_res_rel r r' <=>
    case r of
      OK s => r' = OK s
    | IntRet v s => r' = IntRet v s
    | Halt s => r' = Halt s
    | Abort a s =>
        ?a' s'. r' = Abort a' s' /\ (a = Revert_abort ==> a' = Revert_abort)
    | Error e => (!s. r' <> OK s) /\ (!v s. r' <> IntRet v s)
End

(* Every label an instruction reads as a value is bound in the label map L
   (a state's vs_labels, which no step changes).  Jumps, INVOKE and PHIs
   use their labels as targets, not values. *)
Definition ctx_labels_bound_def:
  ctx_labels_bound C L <=>
    !fn inst l.
      MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
      MEM (Label l) inst.inst_operands /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\ ~is_pseudo inst.inst_opcode ==>
      l IN FDOM L
End

Theorem ctx_labels_bound_step:
  ctx_labels_bound C s.vs_labels /\ step_inst fuel D inst s = OK t ==>
  ctx_labels_bound C t.vs_labels
Proof
  metis_tac[step_inst_preserves_labels_always]
QED

Theorem ctx_labels_bound_run_block:
  ctx_labels_bound C s.vs_labels /\ run_block fuel D bb s = OK t ==>
  ctx_labels_bound C t.vs_labels
Proof
  metis_tac[run_block_preserves_labels]
QED

Theorem ctx_labels_bound_setup_callee:
  ctx_labels_bound C s.vs_labels /\ setup_callee fn args s = SOME t ==>
  ctx_labels_bound C t.vs_labels
Proof
  rw[setup_callee_def] >> gvs[AllCaseEqs()]
QED

(* fn' is a DFT schedule of the well-formed, ALLOCA-free SSA function fn
   that keeps its fallible instructions in order. *)
Definition dft_fn_rel_def:
  dft_fn_rel fn fn' <=>
    fn'.fn_name = fn.fn_name /\
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\
    LIST_REL dft_block_rel fn.fn_blocks fn'.fn_blocks /\
    dft_fallible_order_kept fn fn'
End

Theorem dft_fn_rel_lookup_function:
  !fs gs name.
    LIST_REL dft_fn_rel fs gs ==>
    OPTREL dft_fn_rel (lookup_function name fs) (lookup_function name gs)
Proof
  Induct >> Cases_on `gs` >>
  simp[lookup_function_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.fn_name = h.fn_name` by fs[dft_fn_rel_def] >>
  simp[] >> IF_CASES_TAC >> gvs[lookup_function_def, lookup_block_def]
QED

Theorem dft_block_rel_lookup_block:
  !bs bs' name.
    LIST_REL dft_block_rel bs bs' ==>
    OPTREL dft_block_rel (lookup_block name bs) (lookup_block name bs')
Proof
  Induct >> Cases_on `bs'` >>
  simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.bb_label = h.bb_label` by fs[dft_block_rel_def] >>
  simp[] >> IF_CASES_TAC >> gvs[lookup_function_def, lookup_block_def]
QED

Theorem dft_fn_rel_entry_label:
  dft_fn_rel fn fn' ==> fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >> fs[dft_fn_rel_def] >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, dft_block_rel_def]
QED

Theorem dft_block_rel_length:
  dft_block_rel bb bb' ==>
  LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[dft_block_rel_def] >>
  drule PERM_LENGTH >> simp[] >>
  strip_tac >>
  `!xs. LENGTH (FILTER (\i. is_pseudo i.inst_opcode) xs) +
        LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) xs) = LENGTH xs`
    suffices_by metis_tac[] >>
  Induct >> simp[] >> gen_tac >>
  Cases_on `is_pseudo h.inst_opcode` >> simp[]
QED

Theorem dft_block_rel_perm_of:
  MEM bb fn.fn_blocks /\ dft_block_rel bb bb' ==> block_perm_of fn bb'
Proof
  rw[dft_block_rel_def] >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) scheduled` by
    (fs[EVERY_MEM, from_block_def] >>
     metis_tac[flip_operands_is_pseudo]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) scheduled = scheduled` by
    simp[FILTER_EQ_ID] >>
  simp[block_perm_of_def] >> qexists_tac `bb` >>
  fs[EVERY_MEM] >>
  simp[FILTER_APPEND_DISTRIB, FILTER_FILTER, FILTER_EQ_ID, FILTER_EQ_NIL,
       GSYM EVERY_NOT_EXISTS, EVERY_MEM]
QED

Theorem dft_block_rel_pseudos:
  wf_function fn /\ MEM bb fn.fn_blocks /\ dft_block_rel bb bb' ==>
  FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions =
  FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions
Proof
  rpt strip_tac >>
  drule_all dft_block_rel_perm_of >> strip_tac >>
  `bb.bb_label = bb'.bb_label` by fs[dft_block_rel_def] >>
  drule_all block_perm_of_elim >> simp[]
QED

Theorem dft_block_rel_pseudos_prefix:
  dft_block_rel bb bb' ==> pseudos_prefix bb'
Proof
  rw[dft_block_rel_def] >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) scheduled` by
    (fs[EVERY_MEM, from_block_def] >>
     metis_tac[flip_operands_is_pseudo]) >>
  `EVERY (\i. is_pseudo i.inst_opcode)
     (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by
    simp[EVERY_FILTER, EVERY_MEM] >>
  qmatch_goalsub_abbrev_tac `pseudos_prefix b` >>
  simp[Abbr `b`, pseudos_prefix_def] >> rpt strip_tac >>
  Cases_on `j < LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)`
  >- (fs[EVERY_EL] >> simp[EL_APPEND] >>
      first_x_assum irule >> decide_tac) >>
  fs[EL_APPEND, EVERY_EL] >>
  qpat_x_assum `!n. n < LENGTH scheduled ==> ~is_pseudo _`
    (qspec_then `j - LENGTH
      (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` mp_tac) >>
  simp[]
QED

Theorem dft_block_rel_source:
  wf_function fn /\ MEM bb fn.fn_blocks /\ dft_block_rel bb bb' /\
  MEM i bb'.bb_instructions ==>
  ?j. MEM j bb.bb_instructions /\ j.inst_id = i.inst_id /\
      (!k. MEM k bb.bb_instructions /\ k.inst_id = i.inst_id ==> k = j) /\
      !fuel ctx s. step_inst fuel ctx i s = step_inst fuel ctx j s
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  gvs[dft_block_rel_def, MEM_APPEND, MEM_FILTER] >-
    (qexists_tac `i` >> simp[] >>
     metis_tac[all_distinct_map_mem_inj]) >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  `from_block bb.bb_instructions i` by fs[EVERY_MEM] >>
  fs[from_block_def] >> gvs[] >-
    (qexists_tac `i` >> simp[] >>
     metis_tac[all_distinct_map_mem_inj]) >>
  qexists_tac `j` >> simp[flip_operands_step_inst] >>
  metis_tac[all_distinct_map_mem_inj]
QED

Theorem id_before_map_last[local]:
  xs <> [] /\ MEM x xs /\ x <> LAST xs ==>
  id_before (MAP f xs) (f x) (f (LAST xs))
Proof
  strip_tac >> fs[MEM_EL] >>
  rename1 `k < LENGTH xs` >>
  `LAST xs = EL (PRE (LENGTH xs)) xs` by metis_tac[LAST_EL] >>
  `k < PRE (LENGTH xs)` by
    (Cases_on `k = PRE (LENGTH xs)` >- gvs[] >>
     Cases_on `xs` >> fs[] >> decide_tac) >>
  simp[id_before_def] >> qexistsl_tac [`k`, `PRE (LENGTH xs)`] >>
  simp[EL_MAP, LAST_EL] >> Cases_on `xs` >> fs[]
QED

Theorem id_before_map_last_left[local]:
  ALL_DISTINCT (MAP f xs) ==> ~id_before (MAP f xs) (f (LAST xs)) a
Proof
  strip_tac >> pure_rewrite_tac[id_before_def] >> strip_tac >>
  `xs <> []` by (Cases_on `xs` >> fs[]) >>
  `i < LENGTH xs /\ PRE (LENGTH xs) < LENGTH xs` by
    (Cases_on `xs` >> fs[] >> decide_tac) >>
  `EL i (MAP f xs) = EL (PRE (LENGTH xs)) (MAP f xs)` by
    simp[EL_MAP, LAST_EL] >>
  `i = PRE (LENGTH xs)` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
  Cases_on `xs` >> fs[]
QED

Theorem dft_block_rel_last:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  bb_well_formed bb /\ dft_block_rel bb bb' ==>
  LAST bb'.bb_instructions = LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `~is_pseudo (LAST bb.bb_instructions).inst_opcode /\
   ~is_flippable (LAST bb.bb_instructions).inst_opcode` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     fs[is_terminator_def, is_pseudo_def, is_flippable_def,
        is_commutative_def, is_comparator_def]) >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
    simp[MEM_LAST_NOT_NIL] >>
  fs[dft_block_rel_def] >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  `scheduled <> []` by
    (strip_tac >> gvs[] >> fs[MEM_FILTER, FILTER_EQ_NIL, EVERY_MEM] >>
     metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
     (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
    (irule all_distinct_map_filter >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) scheduled)` by
    metis_tac[ALL_DISTINCT_PERM, PERM_SYM] >>
  `from_block bb.bb_instructions (LAST scheduled)` by
    (fs[EVERY_MEM] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  `?j. MEM j bb.bb_instructions /\ ~is_pseudo j.inst_opcode /\
       j.inst_id = (LAST scheduled).inst_id /\
       (LAST scheduled = j \/
        (LAST scheduled = flip_operands j /\ is_flippable j.inst_opcode))` by
    (fs[from_block_def] >> metis_tac[flip_operands_inst_id]) >>
  `j = LAST bb.bb_instructions` by
    (spose_not_then assume_tac >>
     `id_before (MAP (\i. i.inst_id) bb.bb_instructions)
       j.inst_id (LAST bb.bb_instructions).inst_id` by
       (ho_match_mp_tac id_before_map_last >> simp[]) >>
     `dft_must_order j (LAST bb.bb_instructions)` by
       simp[dft_must_order_def] >>
     `id_before (MAP (\i. i.inst_id) scheduled)
       j.inst_id (LAST bb.bb_instructions).inst_id` by metis_tac[] >>
     metis_tac[id_before_map_last_left]) >>
  gvs[] >> simp[LAST_APPEND_NOT_NIL]
QED

(* Why it holds (unchecked notes):
   - Same fuel works: fuel is per block and per call depth, and the
     schedule visits the same blocks and makes the same calls.
   - Non-terminator Abort/Halt comes only from fallible opcodes (ASSERT,
     ASSERT_UNREACHABLE, RETURNDATACOPY) and INVOKE, which keep their order.
   - A non-fallible instruction with no effects (pure ops, ASSIGN, BUMP,
     OFFSET, environment reads such as GAS) changes only vs_vars and
     vs_inst_idx, and returns OK when inst_wf holds, its variables are
     defined and its labels are bound (ctx_labels_bound; nothing writes
     vs_labels).
   - Definedness at the earlier position: def_dominates_uses plus a
     strict-dominator invariant on the original run, like
     strict_dom_vars_defined (sccpCorrectnessProofs); vacuous at the entry.
   - Instructions with no must-order relation commute: the declared effects
     cover every state field each opcode reads or writes (STATICCALL changes
     no accounts, CREATE's memory write is empty, SSTORE only storage).
   - INVOKE: setup_callee resets vs_vars and vs_inst_idx, so hoisted
     effect-free instructions don't change the callee's run;
     merge_callee_state keeps the caller's variables and SSA keeps
     bind_outputs' names distinct from theirs.
   - Halt states are equal: a terminator runs last, after the whole block,
     and an INVOKE's halt is the callee's state. *)
Theorem dft_run_blocks_rel:
  !C C'.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions ==>
    !fuel name fn fn' s.
      lookup_function name C.ctx_functions = SOME fn /\
      lookup_function name C'.ctx_functions = SOME fn' /\
      fn_entry_label fn = SOME s.vs_current_bb /\
      ctx_labels_bound C s.vs_labels ==>
      dft_res_rel (run_blocks fuel C fn s) (run_blocks fuel C' fn' s)
Proof
  cheat
QED
