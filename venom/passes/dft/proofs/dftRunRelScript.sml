(* Structural and readiness interfaces for a function and its DFT schedule.
 * Finite block simulation uses a gas-variant input (dft_run_block_gas).
 * The old same-state permutation/run lift is not valid for consuming GAS;
 * conditional context transport below does not assert that lift.
 * Successful dft_res_rel results are exact, whereas abort states may differ.
 *)
Theory dftRunRel
Ancestors
  dftScheduleOrder dftStructural dftPermSim dftDefs passSharedDefs venomExecSemantics venomWf
  venomInst venomState venomEffects venomExecProps list finite_map sorting rich_list dftCorrectness
  dftAvailability dftWf dftIndexedExec
  unitLabelMapIdentity sccpCorrectnessProofs

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

Theorem dft_res_rel_trans:
  dft_res_rel r r' /\ dft_res_rel r' r'' ==> dft_res_rel r r''
Proof
  Cases_on `r` >> Cases_on `r'` >> Cases_on `r''` >>
  simp[dft_res_rel_def] >> metis_tac[]
QED

Theorem dft_res_rel_ok_continuation:
  dft_res_rel r r' ==>
  dft_res_rel
    (case r of OK s => k s | other => other)
    (case r' of OK s => k s | other => other)
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[dft_res_rel_def] >> rpt strip_tac >>
  Cases_on `k v` >> simp[dft_res_rel_def]
QED

Theorem dft_exec_prefix_continue:
  !pre s.
  EVERY (\i. ~is_terminator i.inst_opcode) pre ==>
  FOLDR (dft_exec_cons fuel C) k pre s =
    case FOLDR (dft_exec_cons fuel C) OK pre s of
      OK t => k t | other => other
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> simp[]
QED

Theorem dft_exec_prefix_rel:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  (!t. FOLDR (dft_exec_cons fuel C) OK pre s = OK t ==>
       dft_res_rel (k t) (k' t)) ==>
  dft_res_rel (FOLDR (dft_exec_cons fuel C) k pre s)
              (FOLDR (dft_exec_cons fuel C) k' pre s)
Proof
  strip_tac >> simp[Once dft_exec_prefix_continue] >>
  Cases_on `FOLDR (dft_exec_cons fuel C) OK pre s` >> gvs[] >>
  simp[Once dft_exec_prefix_continue] >> simp[dft_res_rel_def]
QED

Theorem dft_suffix_prefix_rel:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  (!t. FOLDR (dft_exec_cons fuel C) OK pre s = OK t ==>
       dft_res_rel (dft_exec_suffix fuel C xs t)
                   (dft_exec_suffix fuel C ys t)) ==>
  dft_res_rel (dft_exec_suffix fuel C (pre ++ xs) s)
              (dft_exec_suffix fuel C (pre ++ ys) s)
Proof
  strip_tac >> rewrite_tac[dft_exec_suffix_append] >>
  irule dft_exec_prefix_rel >> simp[]
QED

(* Only value label operands need to be bound; calls and terminators
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

Theorem id_before_asym:
  ALL_DISTINCT xs /\ id_before xs a b ==> ~id_before xs b a
Proof
  strip_tac >> pure_rewrite_tac[id_before_def] >> strip_tac >>
  qpat_x_assum `id_before _ _ _` mp_tac >>
  pure_rewrite_tac[id_before_def] >> strip_tac >>
  `i < LENGTH xs /\ i' < LENGTH xs` by simp[] >>
  `i = j' /\ j = i'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
QED

Theorem dft_reverse_dependency_disjoint:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo x.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
  DISJOINT (set (inst_defs y)) (set (inst_uses x))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  simp[inst_defs_def, inst_uses_def, pred_setTheory.DISJOINT_DEF,
       pred_setTheory.EXTENSION, MEM_operand_vars_iff] >>
  spose_not_then strip_assume_tac >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) y.inst_id x.inst_id` by
    metis_tac[dft_local_producer_before] >>
  metis_tac[id_before_asym]
QED

Theorem dft_inversion_compatible:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  (!x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
         ~abort_compatible x.inst_opcode y.inst_opcode /\
         id_before (MAP (\i. i.inst_id) bb.bb_instructions)
           x.inst_id y.inst_id ==>
         id_before (MAP (\i. i.inst_id) bb'.bb_instructions)
           x.inst_id y.inst_id) /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
  id_before (MAP (\i. i.inst_id) bb'.bb_instructions) y.inst_id x.inst_id ==>
  abort_compatible x.inst_opcode y.inst_opcode
Proof
  metis_tac[id_before_asym]
QED

Theorem dft_target_head_extract:
  PERM (MAP (\i. i.inst_id) src) (x.inst_id :: MAP (\i. i.inst_id) rest) ==>
  ?pre y post. src = pre ++ y :: post /\ y.inst_id = x.inst_id /\
    PERM (MAP (\i. i.inst_id) (pre ++ post))
         (MAP (\i. i.inst_id) rest)
Proof
  strip_tac >>
  `MEM x.inst_id (MAP (\i. i.inst_id) src)` by metis_tac[PERM_MEM_EQ, MEM] >>
  fs[MEM_MAP] >> rename1 `MEM y src` >>
  qpat_x_assum `MEM y src` mp_tac >>
  simp[MEM_SPLIT] >> strip_tac >> gvs[] >>
  qexistsl_tac [`l1`, `y`, `l2`] >> simp[] >>
  irule perm_cons_delete >>
  qexists_tac `x.inst_id` >> gvs[MAP_APPEND]
QED

Theorem dft_must_order_invokes:
  ~dft_must_order x y ==>
  ~(x.inst_opcode = INVOKE /\ y.inst_opcode = INVOKE)
Proof
  rpt strip_tac >>
  fs[dft_must_order_def, read_effects_def, write_effects_def,
     all_effects_def, pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED
Theorem id_before_append_right:
  id_before ys a b ==> id_before (xs ++ ys) a b
Proof
  simp[id_before_def] >> rpt strip_tac >>
  qexistsl_tac [`LENGTH xs + i`, `LENGTH xs + j`] >>
  simp[EL_APPEND2]
QED

Theorem dft_inversion_not_must_order:
  dft_block_rel bb bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
  id_before (MAP (\i. i.inst_id) bb'.bb_instructions) y.inst_id x.inst_id ==>
  ~dft_must_order x y
Proof
  strip_tac >> strip_tac >> fs[dft_block_rel_def] >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  `id_before (MAP (\i. i.inst_id) scheduled) x.inst_id y.inst_id` by metis_tac[] >>
  `id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id` by
    (gvs[MAP_APPEND] >> irule id_before_append_right >> simp[]) >>
  metis_tac[id_before_asym]
QED

Inductive dft_head_bubbles:
  dft_head_bubbles A [] [] /\
  (!pre y post rest.
    EVERY (\x. A x y) pre /\ dft_head_bubbles A (pre ++ post) rest ==>
    dft_head_bubbles A (pre ++ y::post) (y::rest))
End

Theorem dft_head_bubbles_refl:
  !xs. dft_head_bubbles A xs xs
Proof
  Induct >- simp[dft_head_bubbles_rules] >> gen_tac >>
  simp[Once dft_head_bubbles_cases] >>
  qexistsl_tac [`[]`,`xs`] >> simp[]
QED

Theorem dft_head_bubbles_cross:
  A x y ==> dft_head_bubbles A [x;y] [y;x]
Proof
  strip_tac >> simp[Once dft_head_bubbles_cases] >>
  qexistsl_tac [`[x]`,`[]`] >> simp[dft_head_bubbles_refl]
QED

Theorem dft_suffix_cons_rel:
  (~is_terminator y.inst_opcode ==>
    !t. step_inst fuel C y s = OK t ==>
      dft_res_rel
        (dft_exec_suffix fuel C xs (t with vs_inst_idx := SUC s.vs_inst_idx))
        (dft_exec_suffix fuel C ys (t with vs_inst_idx := SUC s.vs_inst_idx))) ==>
  dft_res_rel (dft_exec_suffix fuel C (y::xs) s)
              (dft_exec_suffix fuel C (y::ys) s)
Proof
  strip_tac >> simp[dft_exec_suffix_def] >>
  Cases_on `step_inst fuel C y s` >> simp[dft_res_rel_def] >>
  Cases_on `is_terminator y.inst_opcode`
  >- (Cases_on `v.vs_halted` >> simp[dft_res_rel_def]) >>
  fs[dft_res_rel_def]
QED

Theorem dft_id_before_cons[local]:
  id_before (h::xs) a b <=>
  (h = a /\ MEM b xs) \/ id_before xs a b
Proof
  simp[id_before_def, MEM_EL] >> eq_tac
  >- (rpt strip_tac >> Cases_on `i` >> Cases_on `j` >> gvs[] >>
      metis_tac[]) >>
  rpt strip_tac
  >- (qexistsl_tac [`0`,`SUC n`] >> simp[]) >>
  qexistsl_tac [`SUC i`,`SUC j`] >> simp[]
QED

Theorem dft_id_before_insert[local]:
  !pre. id_before (pre ++ post) a b ==>
        id_before (pre ++ y::post) a b
Proof
  Induct >> simp[dft_id_before_cons] >>
  metis_tac[MEM_APPEND, MEM]
QED

Theorem dft_id_before_prefix[local]:
  !pre. MEM x pre ==> id_before (pre ++ y::post) x y
Proof
  Induct >> simp[dft_id_before_cons] >> metis_tac[MEM_APPEND, MEM]
QED

Theorem dft_bubble_head_ready:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
  MEM y bb.bb_instructions /\ ~is_pseudo y.inst_opcode /\
  EVERY (\x. ~dft_must_order x y) pre /\
  (!d v. MEM d bb.bb_instructions /\ MEM v d.inst_outputs /\
         ~MEM d (pre ++ y::post) ==> v IN FDOM s.vs_vars) /\
  (!d. MEM d post ==>
       id_before (MAP (\i. i.inst_id) bb.bb_instructions) y.inst_id d.inst_id)
  ==> !v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars
Proof
  rpt strip_tac >> irule dft_ready_operand_defined >> simp[] >>
  qexistsl_tac [`bb`, `fn`, `y`] >> simp[] >>
  `y.inst_opcode <> PHI` by (strip_tac >> gvs[is_pseudo_def]) >>
  simp[] >> rpt strip_tac >>
  Cases_on `MEM d (pre ++ y::post)`
  >- (gvs[MEM_APPEND, MEM]
      >- (fs[EVERY_MEM] >>
          `~dft_must_order d y` by metis_tac[] >>
          gvs[dft_must_order_def, inst_defs_def, inst_uses_def,
              pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
              MEM_operand_vars_iff] >> metis_tac[])
      >- (`ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
            metis_tac[wf_fn_block_inst_ids_distinct] >>
          metis_tac[id_before_asym]) >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
        metis_tac[wf_fn_block_inst_ids_distinct] >>
      metis_tac[id_before_asym]) >>
  metis_tac[]
QED

Theorem dft_remaining_producers_step:
  (!d v. MEM d original /\ MEM v d.inst_outputs /\
         ~MEM d (pre ++ y::post) ==> v IN FDOM s.vs_vars) /\
  inst_wf y /\ ~is_pseudo y.inst_opcode /\ ~is_terminator y.inst_opcode /\
  step_inst fuel C y s = OK t ==>
  !d v. MEM d original /\ MEM v d.inst_outputs /\ ~MEM d (pre ++ post) ==>
    v IN FDOM (t with vs_inst_idx := SUC s.vs_inst_idx).vs_vars
Proof
  strip_tac >>
  `FOLDR (dft_exec_cons fuel C) OK [y] s =
     OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[dft_exec_cons_def] >>
  `EVERY (\i. inst_wf i /\ ~is_pseudo i.inst_opcode /\
               ~is_terminator i.inst_opcode) [y]` by simp[] >>
  drule_all dft_prefix_fdom >> simp[] >> rpt strip_tac >>
  Cases_on `d = y` >- gvs[] >>
  disj1_tac >> first_x_assum irule >> qexists_tac `d` >> simp[]
QED

Definition dft_remaining_inv_def:
  dft_remaining_inv fn bb todo s <=>
    EVERY (\i. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode) todo /\
    ALL_DISTINCT todo /\
    (!x y. id_before todo x y ==>
       id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id) /\
    bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
    (!d v. MEM d bb.bb_instructions /\ MEM v d.inst_outputs /\ ~MEM d todo ==>
       v IN FDOM s.vs_vars) /\
    (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
       ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
       MEM (Label l) i.inst_operands ==> l IN FDOM s.vs_labels)
End

Theorem dft_remaining_inv_head_order:
  dft_remaining_inv fn bb (pre ++ y::post) s ==>
    MEM y bb.bb_instructions /\ ~is_pseudo y.inst_opcode /\
    (!d. MEM d post ==>
       id_before (MAP (\i. i.inst_id) bb.bb_instructions) y.inst_id d.inst_id)
Proof
  simp[dft_remaining_inv_def] >> rpt strip_tac >>
  first_x_assum irule >> irule id_before_append_right >>
  simp[dft_id_before_cons]
QED

Theorem dft_remaining_inv_step:
  wf_function fn /\ EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ y::post) s /\
  ~is_terminator y.inst_opcode /\ step_inst fuel C y s = OK t ==>
  dft_remaining_inv fn bb (pre ++ post)
    (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `MEM y bb.bb_instructions /\ ~is_pseudo y.inst_opcode` by
    metis_tac[dft_remaining_inv_head_order] >>
  `inst_wf y` by fs[EVERY_MEM] >>
  `EVERY (\i. inst_wf i /\ ~is_pseudo i.inst_opcode /\
               ~is_terminator i.inst_opcode) [y]` by simp[] >>
  `FOLDR (dft_exec_cons fuel C) OK [y] s =
     OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[dft_exec_cons_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) [y]` by simp[] >>
  drule_all dft_prefix_frame >> simp[] >> strip_tac >>
  fs[dft_remaining_inv_def] >>
  `strict_dom_vars_defined fn (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule dft_prefix_dominators >> qexistsl_tac [`C`, `fuel`, `[y]`, `s`] >> simp[]) >>
  simp[dft_remaining_inv_def] >> rpt conj_tac
  >- (gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum irule >>
      irule dft_id_before_insert >> simp[])
  >- (drule_at (Pat `step_inst _ _ _ _ = OK _`) dft_remaining_producers_step >>
      disch_then (qspecl_then [`pre`, `post`, `bb.bb_instructions`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem dft_remaining_inv_ready:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  dft_remaining_inv fn bb (pre ++ y::post) s /\ pre <> [] /\
  EVERY (\x. ~dft_must_order x y) pre ==>
  (!v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars) /\
  (y.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels)
Proof
  strip_tac >> drule dft_remaining_inv_head_order >> strip_tac >>
  `~is_terminator y.inst_opcode` by
    (Cases_on `pre` >> fs[EVERY_DEF, dft_must_order_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule dft_bubble_head_ready >>
      qexistsl_tac [`bb`, `fn`, `post`, `pre`, `y`] >>
      fs[dft_remaining_inv_def] >> metis_tac[]) >>
  fs[dft_remaining_inv_def] >> metis_tac[]
QED

Theorem dft_wf_order_nonterminator:
  wf_function fn /\ MEM bb fn.fn_blocks /\ MEM x bb.bb_instructions /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
  ~is_terminator x.inst_opcode
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `x = LAST bb.bb_instructions` by
    (qpat_x_assum `MEM x _` mp_tac >> simp[MEM_EL] >> strip_tac >>
     `n = PRE (LENGTH bb.bb_instructions)` by
       (fs[bb_well_formed_def] >> metis_tac[]) >>
     fs[bb_well_formed_def, LAST_EL]) >>
  gvs[] >> metis_tac[id_before_map_last_left]
QED

Theorem dft_bubble_executed_ready:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
  MEM y bb.bb_instructions /\ ~is_pseudo y.inst_opcode /\
  EVERY (\x. ~dft_must_order x y) pre /\
  (!d. MEM d post ==>
       id_before (MAP (\i. i.inst_id) bb.bb_instructions) y.inst_id d.inst_id) /\
  PERM (done ++ (pre ++ y::post))
       (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) /\
  (!d v. MEM d bb.bb_instructions /\ is_pseudo d.inst_opcode /\
         MEM v d.inst_outputs ==> v IN FDOM s.vs_vars) /\
  EVERY (\i. inst_wf i /\ ~is_pseudo i.inst_opcode /\
             ~is_terminator i.inst_opcode) done /\
  FOLDR (dft_exec_cons fuel C) OK done s = OK t ==>
  !v. MEM (Var v) y.inst_operands ==> v IN FDOM t.vs_vars
Proof
  rpt strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (cj 1 dft_prefix_frame) >>
     qexistsl_tac [`C`, `fuel`, `done`] >> simp[EVERY_MEM] >> fs[EVERY_MEM]) >>
  `strict_dom_vars_defined fn t` by metis_tac[dft_prefix_dominators] >>
  `!d v. MEM d bb.bb_instructions /\ MEM v d.inst_outputs /\
         ~MEM d (pre ++ y::post) ==> v IN FDOM t.vs_vars` by
    (drule dft_executed_producers >>
     disch_then (qspecl_then [`t`, `s`, `fuel`, `C`] mp_tac) >>
     simp[] >> disch_tac >> rpt strip_tac >> first_x_assum irule >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `d` >> simp[]) >>
  irule dft_bubble_head_ready >>
  qexistsl_tac [`bb`, `fn`, `post`, `pre`, `y`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qexists_tac `d` >> simp[]
QED

Theorem dft_head_bubbles_complete:
  !dst src.
    PERM src dst /\ ALL_DISTINCT src /\
    (!x y. id_before src x y /\ id_before dst y x ==> A x y) ==>
    dft_head_bubbles A src dst
Proof
  Induct >- simp[dft_head_bubbles_refl] >> rpt strip_tac >>
  `MEM h src` by metis_tac[PERM_MEM_EQ, MEM] >>
  qpat_x_assum `MEM h src` mp_tac >> simp[MEM_SPLIT] >> strip_tac >> gvs[] >>
  `PERM (l1 ++ l2) dst` by
    (irule perm_cons_delete >> qexists_tac `h` >> simp[]) >>
  simp[Once dft_head_bubbles_cases] >>
  qexistsl_tac [`l1`,`l2`] >> simp[] >>
  conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      `id_before (l1 ++ [h] ++ l2) x h` by
        (rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> irule dft_id_before_prefix >> simp[]) >>
      `MEM x dst` by
        (gvs[ALL_DISTINCT_APPEND] >> metis_tac[PERM_MEM_EQ, MEM_APPEND, MEM]) >>
      first_x_assum irule >> simp[dft_id_before_cons]) >>
  first_x_assum irule >> simp[] >> reverse conj_tac
  >- (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  conj_tac
  >- (rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> irule dft_id_before_insert >> simp[]) >>
  simp[dft_id_before_cons]
QED

Theorem dft_perm_map_members[local]:
  !f xs ys. ALL_DISTINCT (MAP f xs) /\ EVERY (\x. MEM x xs) ys /\
  PERM (MAP f xs) (MAP f ys) ==> PERM xs ys
Proof
  rpt gen_tac >> strip_tac >> irule PERM_ALL_DISTINCT >>
  `ALL_DISTINCT (MAP f ys)` by metis_tac[ALL_DISTINCT_PERM] >>
  `ALL_DISTINCT xs /\ ALL_DISTINCT ys` by metis_tac[ALL_DISTINCT_MAP] >>
  simp[] >> gvs[EVERY_MEM] >> rpt strip_tac >> eq_tac
  >- (strip_tac >>
      `MEM (f x) (MAP f ys)` by metis_tac[PERM_MEM_EQ, MEM_MAP] >>
      gvs[MEM_MAP] >> metis_tac[all_distinct_map_mem_inj]) >>
  metis_tac[]
QED

Theorem dft_body_originals[local]:
  !body. EVERY (from_block bi) body ==>
  ?norm. EVERY (\j. MEM j bi /\ ~is_pseudo j.inst_opcode) norm /\
    MAP (\i. i.inst_id) norm = MAP (\i. i.inst_id) body /\
    LIST_REL (\j i. j.inst_id = i.inst_id /\
      (!fuel ctx s. step_inst fuel ctx j s = step_inst fuel ctx i s)) norm body
Proof
  Induct >- (strip_tac >> qexists_tac `[]` >> simp[]) >>
  rpt strip_tac >> fs[] >>
  qpat_x_assum `from_block bi h` mp_tac >> simp[from_block_def] >> strip_tac >> gvs[]
  >- (qexists_tac `h::norm` >> simp[]) >>
  qexists_tac `j::norm` >> simp[flip_operands_inst_id, flip_operands_step_inst]
QED

Theorem dft_body_normalize:
  !bb body.
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY (from_block bb.bb_instructions) body /\
  PERM (MAP (\i. i.inst_id) body)
       (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)) ==>
  ?norm.
    PERM (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) norm /\
    MAP (\i. i.inst_id) norm = MAP (\i. i.inst_id) body /\
    LIST_REL (\j i. j.inst_id = i.inst_id /\
      (!fuel ctx s. step_inst fuel ctx j s = step_inst fuel ctx i s)) norm body
Proof
  rpt gen_tac >> strip_tac >> drule dft_body_originals >> strip_tac >>
  qexists_tac `norm` >> simp[] >>
  irule (Q.ISPEC `\i. i.inst_id` dft_perm_map_members) >>
  conj_tac
  >- (irule all_distinct_map_filter >> simp[]) >>
  conj_tac
  >- gvs[EVERY_MEM, MEM_FILTER] >>
  metis_tac[PERM_SYM]
QED

Theorem dft_block_lookup_aligned[local]:
  !bs bs' name.
    LIST_REL dft_block_rel bs bs' /\ LIST_REL R bs bs' ==>
    OPTREL (\bb bb'. dft_block_rel bb bb' /\ R bb bb')
      (lookup_block name bs) (lookup_block name bs')
Proof
  Induct >> Cases_on `bs'` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.bb_label = h.bb_label` by fs[dft_block_rel_def] >>
  simp[] >> IF_CASES_TAC >> gvs[lookup_block_def]
QED

Theorem dft_fn_rel_lookup_order:
  dft_fn_rel fn fn' /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' ==>
  dft_block_rel bb bb' /\
  (!x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~abort_compatible x.inst_opcode y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id)
Proof
  strip_tac >> fs[dft_fn_rel_def, dft_fallible_order_kept_def] >>
  drule_all dft_block_lookup_aligned >>
  disch_then (qspec_then `name` mp_tac) >> simp[]
QED

Theorem dft_id_before_map[local]:
  id_before xs a b ==> id_before (MAP f xs) (f a) (f b)
Proof
  simp[id_before_def] >> rpt strip_tac >>
  qexistsl_tac [`i`,`j`] >> simp[EL_MAP]
QED

Theorem dft_id_before_filter[local]:
  !xs. id_before (FILTER P xs) a b ==> id_before xs a b
Proof
  Induct >> simp[dft_id_before_cons] >> gen_tac >>
  Cases_on `P h` >> simp[dft_id_before_cons, MEM_FILTER] >> metis_tac[]
QED

Theorem dft_schedule_ids_distinct[local]:
  !bi body.
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  PERM (MAP (\i. i.inst_id) body)
       (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (FILTER (\i. is_pseudo i.inst_opcode) bi ++ body))
Proof
  qx_gen_tac `bi` >> qx_gen_tac `scheduled` >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. is_pseudo i.inst_opcode) bi)) /\
   ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))` by
    (conj_tac >> irule all_distinct_map_filter >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) scheduled)` by metis_tac[ALL_DISTINCT_PERM] >>
  simp[MAP_APPEND, ALL_DISTINCT_APPEND] >>
  rpt strip_tac >>
  `MEM e (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))`
    by metis_tac[PERM_MEM_EQ] >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[all_distinct_map_mem_inj]
QED

Theorem dft_id_before_mem[local]:
  id_before xs a b ==> MEM a xs /\ MEM b xs
Proof
  simp[id_before_def] >> rpt strip_tac >>
  metis_tac[EL_MEM, arithmeticTheory.LESS_TRANS]
QED

Theorem dft_block_head_bubbles:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  dft_block_rel bb bb' /\
  (!x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~abort_compatible x.inst_opcode y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id) ==>
  ?body norm.
    bb'.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ body /\
    PERM (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) norm /\
    MAP (\i. i.inst_id) norm = MAP (\i. i.inst_id) body /\
    LIST_REL (\j i. j.inst_id = i.inst_id /\
      (!fuel ctx s. step_inst fuel ctx j s = step_inst fuel ctx i s)) norm body /\
    dft_head_bubbles
      (\x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
        ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
        id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
        ~dft_must_order x y /\ abort_compatible x.inst_opcode y.inst_opcode)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) norm
Proof
  strip_tac >> drule (iffLR dft_block_rel_def) >> strip_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  drule_all dft_body_normalize >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions)` by
    (drule_all dft_schedule_ids_distinct >> simp[]) >>
  `ALL_DISTINCT (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` by
    metis_tac[all_distinct_map_filter, ALL_DISTINCT_MAP] >>
  qexistsl_tac [`scheduled`,`norm`] >> simp[] >>
  irule dft_head_bubbles_complete >> simp[] >> rpt gen_tac >> strip_tac >>
  `MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
   ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode` by
    (qpat_x_assum `id_before (FILTER _ _) x y`
       (mp_tac o MATCH_MP dft_id_before_mem) >> simp[MEM_FILTER]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id` by
    (ho_match_mp_tac dft_id_before_map >> irule dft_id_before_filter >>
     qexists_tac `\i. ~is_pseudo i.inst_opcode` >> simp[]) >>
  `id_before (MAP (\i. i.inst_id) bb'.bb_instructions) y.inst_id x.inst_id` by
    (gvs[MAP_APPEND] >> irule id_before_append_right >>
     `id_before (MAP (\i. i.inst_id) norm) y.inst_id x.inst_id` by
       (ho_match_mp_tac dft_id_before_map >> simp[]) >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule dft_inversion_not_must_order >> simp[] >> metis_tac[]) >>
  irule dft_inversion_compatible >> simp[] >> metis_tac[]
QED

Theorem dft_remaining_inv_initial:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
  (!d v. MEM d bb.bb_instructions /\ is_pseudo d.inst_opcode /\
     MEM v d.inst_outputs ==> v IN FDOM s.vs_vars) /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     MEM (Label l) i.inst_operands ==> l IN FDOM s.vs_labels) ==>
  dft_remaining_inv fn bb
    (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) s
Proof
  strip_tac >> simp[dft_remaining_inv_def, EVERY_MEM, MEM_FILTER] >>
  rpt conj_tac
  >- (`ALL_DISTINCT (MAP (\i. i.inst_id)
         (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
        (irule all_distinct_map_filter >> simp[]) >>
      metis_tac[ALL_DISTINCT_MAP])
  >- (rpt strip_tac >> ho_match_mp_tac dft_id_before_map >>
      irule dft_id_before_filter >> qexists_tac `\i. ~is_pseudo i.inst_opcode` >> simp[]) >>
  metis_tac[]
QED

Theorem dft_exec_suffix_cong:
  !xs ys.
    LIST_REL (\x y. is_terminator x.inst_opcode = is_terminator y.inst_opcode /\
      (!fuel C s. step_inst fuel C x s = step_inst fuel C y s)) xs ys ==>
    !fuel C s. dft_exec_suffix fuel C xs s = dft_exec_suffix fuel C ys s
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  simp[dft_exec_suffix_def] >>
  qpat_x_assum `!fuel C s. _` (qspecl_then [`fuel`,`C`,`s`] assume_tac) >>
  gvs[] >> Cases_on `step_inst fuel C h s` >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem dft_from_block_terminator:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM j bi /\
  from_block bi i /\ j.inst_id = i.inst_id ==>
  is_terminator j.inst_opcode = is_terminator i.inst_opcode
Proof
  simp[from_block_def] >> rpt strip_tac >> gvs[]
  >- metis_tac[all_distinct_map_mem_inj] >>
  rename1 `is_terminator (flip_operands original).inst_opcode` >>
  `j = original` by metis_tac[all_distinct_map_mem_inj, flip_operands_inst_id] >>
  gvs[] >> rw[flip_operands_def] >>
  Cases_on `j.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `is_comparator j.inst_opcode` >> simp[] >>
  Cases_on `j.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def, is_terminator_def]
QED

Theorem dft_normalized_suffix_eq:
  !bi norm scheduled fuel C s.
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  EVERY (\j. MEM j bi) norm /\ EVERY (from_block bi) scheduled /\
  LIST_REL (\j i. j.inst_id = i.inst_id /\
    (!fuel C s. step_inst fuel C j s = step_inst fuel C i s)) norm scheduled ==>
  dft_exec_suffix fuel C norm s = dft_exec_suffix fuel C scheduled s
Proof
  rpt gen_tac >> strip_tac >> irule dft_exec_suffix_cong >>
  qpat_x_assum `LIST_REL _ norm scheduled` mp_tac >>
  qpat_x_assum `EVERY _ scheduled` mp_tac >>
  qpat_x_assum `EVERY _ norm` mp_tac >>
  qid_spec_tac `scheduled` >> qid_spec_tac `norm` >>
  Induct >> Cases_on `scheduled` >> simp[] >> rpt strip_tac >>
  fs[] >> irule dft_from_block_terminator >> simp[] >> qexists_tac `bi` >> simp[]
QED

Theorem dft_remaining_inv_initialized:
  !fn bb s u t fuel C.
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY inst_wf bb.bb_instructions /\
  bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     MEM (Label l) i.inst_operands ==> l IN FDOM s.vs_labels) /\
  eval_phis s (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) = OK u /\
  FOLDR (dft_exec_cons fuel C) OK
    (DROP (phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions))
      (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions))
    (u with vs_inst_idx :=
      phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)) = OK t ==>
  dft_remaining_inv fn bb
    (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) t
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. inst_wf i /\ ~is_terminator i.inst_opcode)
    (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by
    (simp[EVERY_MEM, MEM_FILTER] >> rpt gen_tac >> strip_tac >>
     conj_tac >- fs[EVERY_MEM] >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
  drule_all dft_pseudo_initialization >> strip_tac >>
  irule dft_remaining_inv_initial >> simp[] >>
  fs[sccpCorrectnessProofsTheory.strict_dom_vars_defined_def,
     pred_setTheory.SUBSET_DEF, MEM_FILTER] >> metis_tac[]
QED

(* One block, same context on both sides: DFT's block bb' simulates bb up to
   a reordering of the gas readings.  The original block runs from a state
   that differs from s' only in vs_gas_readings (gas_variant, o1PassContract,
   unfolded here).  Premises: variables the block reads are defined
   (strict_dom_vars_defined), value labels are bound, no ALLOCA, and pairs
   that are not abort_compatible keep their order (dft_fallible_order_kept).
   Without them an instruction hoisted above an aborting one can fail with
   an undefined operand where the original aborted. *)
Theorem dft_run_block_gas:
  !fn bb bb' s' fuel C.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  dft_block_rel bb bb' /\ pseudos_prefix bb /\
  bb.bb_label = s'.vs_current_bb /\ strict_dom_vars_defined fn s' /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     MEM (Label l) i.inst_operands ==> l IN FDOM s'.vs_labels) /\
  (!x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~abort_compatible x.inst_opcode y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id) ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
      dft_res_rel (run_block fuel C bb s) (run_block fuel C bb' s')
Proof
  cheat
QED

Theorem dft_fn_rel_setup_callee:
  dft_fn_rel fn fn' ==> setup_callee fn' args s = setup_callee fn args s
Proof
  strip_tac >> fs[dft_fn_rel_def] >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  gvs[setup_callee_def, dft_block_rel_def]
QED

Theorem dft_setup_callee_entry:
  setup_callee fn args s = SOME t ==>
  fn_entry_label fn = SOME t.vs_current_bb
Proof
  Cases_on `fn.fn_blocks` >>
  simp[setup_callee_def, fn_entry_label_def, entry_block_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dft_res_rel_refl[simp]:
  dft_res_rel r r
Proof
  Cases_on `r` >> simp[dft_res_rel_def]
QED

Theorem dft_step_context_rel:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  (!name fn fn' t.
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn = SOME t.vs_current_bb /\ ctx_labels_bound C t.vs_labels ==>
    dft_res_rel (run_blocks fuel C fn t) (run_blocks fuel C' fn' t)) /\
  ctx_labels_bound C s.vs_labels ==>
  dft_res_rel (step_inst fuel C i s) (step_inst fuel C' i s)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (simp[Ntimes step_inst_def 2] >>
      Cases_on `decode_invoke i` >- simp[dft_res_rel_def] >> simp[] >>
      rename1 `decode_invoke i = SOME pair` >> PairCases_on `pair` >> simp[] >>
      drule dft_fn_rel_lookup_function >>
      disch_then (qspec_then `pair0` mp_tac) >>
      Cases_on `lookup_function pair0 C.ctx_functions` >>
      Cases_on `lookup_function pair0 C'.ctx_functions` >>
      simp[optionTheory.OPTREL_def] >> strip_tac >>
      rename1 `dft_fn_rel callee callee'` >>
      `!args. setup_callee callee' args s = setup_callee callee args s` by
        metis_tac[dft_fn_rel_setup_callee] >>
      simp[] >> Cases_on `eval_operands pair1 s` >- simp[dft_res_rel_def] >>
      simp[] >> rename1 `eval_operands pair1 s = SOME args` >>
      Cases_on `setup_callee callee args s` >- simp[dft_res_rel_def] >>
      simp[] >> rename1 `setup_callee callee args s = SOME t` >>
      `fn_entry_label callee = SOME t.vs_current_bb` by
        metis_tac[dft_setup_callee_entry] >>
      `ctx_labels_bound C t.vs_labels` by
        metis_tac[ctx_labels_bound_setup_callee] >>
      first_x_assum (drule_all_then mp_tac) >>
      Cases_on `run_blocks fuel C callee t` >>
      Cases_on `run_blocks fuel C' callee' t` >>
      simp[dft_res_rel_def] >> rpt strip_tac >> gvs[] >>
      Cases_on `bind_outputs i.inst_outputs i'.iret_values
        (adopt_return_fmp i' (merge_callee_state s v))` >> simp[]) >>
  simp[step_inst_non_invoke]
QED

Theorem dft_suffix_context_rel:
  !xs fuel C C' s.
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  (!name fn fn' t.
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn = SOME t.vs_current_bb /\ ctx_labels_bound C t.vs_labels ==>
    dft_res_rel (run_blocks fuel C fn t) (run_blocks fuel C' fn' t)) /\
  ctx_labels_bound C s.vs_labels ==>
  dft_res_rel (dft_exec_suffix fuel C xs s) (dft_exec_suffix fuel C' xs s)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[dft_exec_suffix_def] >>
  `dft_res_rel (step_inst fuel C h s) (step_inst fuel C' h s)` by
    (irule dft_step_context_rel >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> Cases_on `step_inst fuel C' h s` >>
  qpat_x_assum `dft_res_rel _ _` mp_tac >>
  simp[dft_res_rel_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `is_terminator h.inst_opcode`
  >- (Cases_on `v.vs_halted` >> simp[]) >>
  simp[GSYM dft_res_rel_def] >> first_x_assum irule >>
  rpt conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> irule ctx_labels_bound_step >>
  metis_tac[]
QED

Theorem dft_exec_block_context_rel:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  (!name fn fn' t.
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn = SOME t.vs_current_bb /\ ctx_labels_bound C t.vs_labels ==>
    dft_res_rel (run_blocks fuel C fn t) (run_blocks fuel C' fn' t)) /\
  ctx_labels_bound C s.vs_labels ==>
  dft_res_rel (exec_block fuel C bb s) (exec_block fuel C' bb s)
Proof
  strip_tac >>
  `!D. exec_block fuel D bb s =
    dft_exec_suffix fuel D (DROP s.vs_inst_idx bb.bb_instructions) s` by
    (gen_tac >> irule dft_exec_suffix_boundary >> simp[]) >>
  simp[] >> irule dft_suffix_context_rel >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem dft_run_block_context_rel:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  (!name fn fn' t.
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn = SOME t.vs_current_bb /\ ctx_labels_bound C t.vs_labels ==>
    dft_res_rel (run_blocks fuel C fn t) (run_blocks fuel C' fn' t)) /\
  ctx_labels_bound C s.vs_labels ==>
  dft_res_rel (run_block fuel C bb s) (run_block fuel C' bb s)
Proof
  strip_tac >> simp[run_block_def] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  simp[] >> irule dft_exec_block_context_rel >>
  rpt conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> metis_tac[venomExecPropsTheory.eval_phis_preserves_labels]
QED

(* The obsolete same-state block/run lift is retired: GAS consumes an
   oracle entry. The replacement finite block obligation is dft_run_block_gas;
   cross-context uniform simulation requires a separate occurrence witness. *)

(* The TASK supplied the stronger all-fallible ordering premise. The
   owner's imported definition orders only abort-incompatible pairs.
   These independent predicates record the original contract verbatim;
   implication, not equivalence, transfers the proof to that contract. *)
Definition dft_task_fallible_order_kept_def:
  dft_task_fallible_order_kept fn fn' <=>
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

Definition dft_task_fn_rel_def:
  dft_task_fn_rel fn fn' <=>
    fn'.fn_name = fn.fn_name /\
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\
    LIST_REL dft_block_rel fn.fn_blocks fn'.fn_blocks /\
    dft_task_fallible_order_kept fn fn'
End

Theorem dft_task_order_implies_current:
  dft_task_fallible_order_kept fn fn' ==> dft_fallible_order_kept fn fn'
Proof
  simp[dft_task_fallible_order_kept_def, dft_fallible_order_kept_def] >>
  match_mp_tac LIST_REL_mono >>
  simp[abort_compatible_def, is_fallible_def] >> metis_tac[]
QED

Theorem dft_task_fn_rel_implies_current:
  dft_task_fn_rel fn fn' ==> dft_fn_rel fn fn'
Proof
  simp[dft_task_fn_rel_def, dft_fn_rel_def] >>
  metis_tac[dft_task_order_implies_current]
QED

Theorem dft_task_context_rel_implies_current:
  LIST_REL dft_task_fn_rel fs gs ==> LIST_REL dft_fn_rel fs gs
Proof
  match_mp_tac LIST_REL_mono >> metis_tac[dft_task_fn_rel_implies_current]
QED

