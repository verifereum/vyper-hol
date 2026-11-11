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
  dftAvailability dftWf dftIndexedExec dftSsaPreserve
  unitLabelMapIdentity sccpCorrectnessProofs gasOracleReplay stateEquiv opcodeClass
Libs
  stepInstBaseLib

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
      inst.inst_opcode <> CODECOPY /\
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
         ~dft_abort_compatible x.inst_opcode y.inst_opcode /\
         id_before (MAP (\i. i.inst_id) bb.bb_instructions)
           x.inst_id y.inst_id ==>
         id_before (MAP (\i. i.inst_id) bb'.bb_instructions)
           x.inst_id y.inst_id) /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
  id_before (MAP (\i. i.inst_id) bb'.bb_instructions) y.inst_id x.inst_id ==>
  dft_abort_compatible x.inst_opcode y.inst_opcode
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
       i.inst_opcode <> CODECOPY /\
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
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
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
    ~dft_abort_compatible x.inst_opcode y.inst_opcode /\
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
    ~dft_abort_compatible x.inst_opcode y.inst_opcode /\
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
        ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
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
       i.inst_opcode <> CODECOPY /\
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
       i.inst_opcode <> CODECOPY /\
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

Theorem dft_block_rel_strict_dom_vars_defined:
  wf_function fn /\ LIST_REL dft_block_rel fn.fn_blocks bbs ==>
  (strict_dom_vars_defined (fn with fn_blocks := bbs) s <=>
   strict_dom_vars_defined fn s)
Proof
  strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct, wf_function_def] >>
  simp[strict_dom_vars_defined_def, dft_block_rel_dominates] >>
  eq_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (drule_all dft_blocks_member_left >> strip_tac >>
      drule dft_block_rel_outputs_perm >>
      (impl_tac >- metis_tac[]) >>
      disch_then (mp_tac o MATCH_MP PERM_MEM_EQ) >>
      simp[MEM_MAP] >> metis_tac[dft_block_rel_label,
        bb_inst_ids_distinct, wf_function_def]) >>
  drule_all dft_blocks_member_right >> strip_tac >>
  drule dft_block_rel_outputs_perm >>
      (impl_tac >- metis_tac[]) >>
  disch_then (mp_tac o MATCH_MP PERM_MEM_EQ) >>
  simp[MEM_MAP] >> metis_tac[dft_block_rel_label,
    bb_inst_ids_distinct, wf_function_def]
QED

Theorem dft_fn_strict_dom_vars_defined:
  dft_fn_rel fn (dft_fn fn) ==>
  (strict_dom_vars_defined (dft_fn fn) s <=> strict_dom_vars_defined fn s)
Proof
  strip_tac >>
  `dft_fn fn = fn with fn_blocks := (dft_fn fn).fn_blocks` by
    (simp[dft_fn_def] >> pairarg_tac >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule dft_block_rel_strict_dom_vars_defined >> gvs[dft_fn_rel_def]
QED

Theorem dft_fn_reachable:
  dft_fn_rel fn (dft_fn fn) ==>
  (fn_reachable (dft_fn fn) lbl <=> fn_reachable fn lbl)
Proof
  strip_tac >>
  `dft_fn fn = fn with fn_blocks := (dft_fn fn).fn_blocks` by
    (simp[dft_fn_def] >> pairarg_tac >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule dft_block_rel_reachable >> gvs[dft_fn_rel_def]
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

Theorem dft_abort_kind_fallible:
  dft_abort_kind op <> NoFail ==> opcode_fail_class op <> NoFail
Proof
  Cases_on `op` >> simp[dft_abort_kind_def, opcode_fail_class_def]
QED

Theorem dft_task_order_implies_current:
  dft_task_fallible_order_kept fn fn' ==> dft_fallible_order_kept fn fn'
Proof
  simp[dft_task_fallible_order_kept_def, dft_fallible_order_kept_def] >>
  match_mp_tac LIST_REL_mono >>
  simp[dft_abort_compatible_def, is_fallible_def] >>
  metis_tac[dft_abort_kind_fallible]
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


(* A successful executed prefix can be replayed with any prescribed unread
   suffix. The earlier consumed values are fixed before choosing that suffix. *)
Theorem dft_prefix_replay_tail:
  !pre s t.
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t ==>
  ?gs. !tail.
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := gs ++ tail) =
    OK (t with vs_gas_readings := tail)
Proof
  Induct
  >- (simp[] >> rpt strip_tac >> qexists_tac `[]` >> simp[]) >>
  rpt gen_tac >> simp[dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  mp_tac (cj 1 gas_oracle_replay) >>
  disch_then (qspecl_then [`fuel`, `C`, `h`, `s`] strip_assume_tac) >>
  qexists_tac `gas_prefix n s.vs_gas_readings ++ gs` >>
  gen_tac >>
  qpat_x_assum `!tail. lift_result _ _ _ _ _`
    (qspec_then `gs ++ tail` mp_tac) >>
  simp[GSYM gas_prefix_def] >>
  Cases_on `step_inst fuel C h
    (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ (gs ++ tail))` >>
  simp[lift_result_def] >> strip_tac >> gvs[lift_result_def] >>
  simp[dft_exec_cons_def, APPEND_ASSOC]
QED

Theorem dft_prefix_replay_variant:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t /\
  t = (u with vs_gas_readings := t.vs_gas_readings) ==>
  ?s0. s = (s0 with vs_gas_readings := s.vs_gas_readings) /\
    FOLDR (dft_exec_cons fuel C) OK pre s0 = OK u
Proof
  strip_tac >> drule_all dft_prefix_replay_tail >> strip_tac >>
  qexists_tac `s with vs_gas_readings := gs ++ u.vs_gas_readings` >>
  simp[] >>
  `u = (t with vs_gas_readings := u.vs_gas_readings)` by
    (qpat_x_assum `t = _` SUBST1_TAC >> simp[]) >>
  metis_tac[]
QED

(* Lift a gas-variant suffix simulation through a prefix already executed on
   the scheduled side. The earlier prefix readings are replayed, not changed. *)
Theorem dft_suffix_prefix_variant:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  (!t. FOLDR (dft_exec_cons fuel C) OK pre s' = OK t ==>
    ?u. t = (u with vs_gas_readings := t.vs_gas_readings) /\
      dft_res_rel (dft_exec_suffix fuel C xs u)
                  (dft_exec_suffix fuel C ys t)) ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    dft_res_rel (dft_exec_suffix fuel C (pre ++ xs) s)
                (dft_exec_suffix fuel C (pre ++ ys) s')
Proof
  strip_tac >>
  Cases_on `FOLDR (dft_exec_cons fuel C) OK pre s'`
  >- (gvs[] >>
      drule_all dft_prefix_replay_variant >> strip_tac >>
      qexists_tac `s0` >> simp[dft_exec_suffix_append] >>
      simp[Once dft_exec_prefix_continue] >>
      simp[Once dft_exec_prefix_continue]) >>
  qexists_tac `s'` >> simp[dft_exec_suffix_append] >>
  simp[Once dft_exec_prefix_continue] >>
  simp[Once dft_exec_prefix_continue]
QED

(* Successful gas pairs have an exact endpoint, including the unread oracle.
   Convert only OK results across indices: stopping INVOKEs carry callee indices. *)
Theorem dft_indexed_gas_pair_ok:
  gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  DISJOINT (set (inst_defs x)) (set (inst_uses y)) /\
  DISJOINT (set (inst_defs y)) (set (inst_uses x)) /\
  DISJOINT (set (inst_defs x)) (set (inst_defs y)) /\
  step_inst fuel C y s' = OK sy /\
  step_inst fuel C x (sy with vs_inst_idx := SUC s'.vs_inst_idx) = OK syx ==>
  ?s sx sxy.
    s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    step_inst fuel C x s = OK sx /\
    step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
    (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (syx with vs_inst_idx := SUC (SUC s'.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst fuel C x sy = OK (syx with vs_inst_idx := sy.vs_inst_idx)` by
    (qpat_x_assum `step_inst _ _ y s' = _` kall_tac >>
     drule_all dft_step_ok_idx >>
     disch_then (qspec_then `sy.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all dftBlockSimTheory.gas_pair_commute >> strip_tac >>
  qexistsl_tac [`ss1`, `v1`,
    `syx with vs_inst_idx := SUC s'.vs_inst_idx`] >>
  `ss1.vs_inst_idx = s'.vs_inst_idx` by
    (qpat_x_assum `s' = _` SUBST1_TAC >> simp[]) >>
  simp[] >>
  drule_all dft_step_ok_idx >>
  disch_then (qspec_then `SUC s'.vs_inst_idx` mp_tac) >> simp[]
QED

Theorem dft_suffix_gas_pair_ok:
  gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  DISJOINT (set (inst_defs x)) (set (inst_uses y)) /\
  DISJOINT (set (inst_defs y)) (set (inst_uses x)) /\
  DISJOINT (set (inst_defs x)) (set (inst_defs y)) /\
  step_inst fuel C y s' = OK sy /\
  step_inst fuel C x (sy with vs_inst_idx := SUC s'.vs_inst_idx) = OK syx ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    dft_exec_suffix fuel C (x::y::tail) s =
    dft_exec_suffix fuel C (y::x::tail) s'
Proof
  strip_tac >> drule_all dft_indexed_gas_pair_ok >> strip_tac >>
  qexists_tac `s` >> simp[dft_exec_suffix_cons, dft_exec_cons_def] >>
  `s.vs_inst_idx = s'.vs_inst_idx` by
    (qpat_x_assum `s' = _` SUBST1_TAC >> simp[]) >>
  `sx.vs_inst_idx = s.vs_inst_idx /\ sy.vs_inst_idx = s'.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  simp[] >> metis_tac[]
QED

Definition dft_gas_swap_pair_def:
  dft_gas_swap_pair x y <=>
    DISJOINT (set (inst_defs x)) (set (inst_uses y)) /\
    DISJOINT (set (inst_defs y)) (set (inst_uses x)) /\
    DISJOINT (set (inst_defs x)) (set (inst_defs y)) /\
    effects_independent x.inst_opcode y.inst_opcode /\
    dft_abort_compatible x.inst_opcode y.inst_opcode /\
    ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
    ~is_alloca_op x.inst_opcode /\ ~is_alloca_op y.inst_opcode /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode
End

Theorem dft_gas_swap_pair_sym:
  dft_gas_swap_pair x y <=> dft_gas_swap_pair y x
Proof
  rw[dft_gas_swap_pair_def, effects_independent_def, dft_abort_compatible_def] >>
  metis_tac[pred_setTheory.DISJOINT_SYM]
QED


(* Zero-consumption replay gives an exact successful oracle frame, without
   requiring equality of error strings from lift_result. *)
Theorem dft_nonconsuming_ok_oracle:
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK t ==>
  step_inst fuel C i (s with vs_gas_readings := gs) =
    OK (t with vs_gas_readings := gs)
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  drule gas_base_non_gas >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `step_inst_base i (s with vs_gas_readings := gs)` >>
  simp[lift_result_def]
QED

Theorem dft_nonconsuming_oracle_frame:
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE ==>
  lift_result
    (\a b. b = (a with vs_gas_readings := gs))
    (\a b. b = (a with vs_gas_readings := gs))
    (\a b. b = (a with vs_gas_readings := gs))
    (step_inst fuel C i s)
    (step_inst fuel C i (s with vs_gas_readings := gs))
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  drule gas_base_non_gas >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `step_inst_base i s` >>
  Cases_on `step_inst_base i (s with vs_gas_readings := gs)` >>
  simp[lift_result_def]
QED

Theorem dft_nonconsuming_ok_readings:
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK t ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  drule gas_base_non_gas >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `[]` mp_tac) >>
  Cases_on `step_inst_base i (s with vs_gas_readings := [])` >>
  simp[lift_result_def]
QED

Theorem dft_gas_ok_shape:
  g.inst_opcode = GAS /\ inst_wf g ==>
  ?out. g.inst_outputs = [out] /\
    !fuel C s. step_inst fuel C g s =
      OK (update_var out (if s.vs_gas_readings = [] then 0w
                          else HD s.vs_gas_readings)
        (s with vs_gas_readings := TL s.vs_gas_readings))
Proof
  strip_tac >>
  `LENGTH g.inst_outputs = 1` by gvs[inst_wf_def] >>
  Cases_on `g.inst_outputs` >> gvs[] >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_gas_def] >>
  gen_tac >> Cases_on `s.vs_gas_readings` >> simp[] >>
  simp[update_var_def, venom_state_component_equality]
QED

Theorem dft_independent_gas_output:
  dft_gas_swap_pair g i /\ g.inst_outputs = [out] ==>
  (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
  ~MEM out i.inst_outputs
Proof
  strip_tac >>
  gvs[dft_gas_swap_pair_def, inst_defs_def, inst_uses_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[dftBlockSimTheory.mem_var_operand_vars]
QED

Theorem dft_gas_noninvoke_ok_diamond:
  dft_gas_swap_pair g i /\ g.inst_opcode = GAS /\ inst_wf g /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK t ==>
  ?sg st. step_inst fuel C g s = OK sg /\
    step_inst fuel C g t = OK st /\ step_inst fuel C i sg = OK st
Proof
  strip_tac >> drule_all dft_gas_ok_shape >> strip_tac >>
  drule_all dft_independent_gas_output >> strip_tac >>
  drule_all dft_nonconsuming_ok_readings >> strip_tac >>
  qexistsl_tac
    [`update_var out (if s.vs_gas_readings = [] then 0w else HD s.vs_gas_readings)
        (s with vs_gas_readings := TL s.vs_gas_readings)`,
     `update_var out (if t.vs_gas_readings = [] then 0w else HD t.vs_gas_readings)
        (t with vs_gas_readings := TL t.vs_gas_readings)`] >>
  simp[] >>
  drule_all dftCommutationTheory.step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s with vs_gas_readings := TL s.vs_gas_readings`,
    `if s.vs_gas_readings = [] then 0w else HD s.vs_gas_readings`] mp_tac) >>
  drule_all dft_nonconsuming_ok_oracle >>
  disch_then (qspec_then `TL s.vs_gas_readings` mp_tac) >>
  simp[dftCommutationTheory.map_result_state_def]
QED

Theorem dft_nonconsuming_updated_ok:
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
  ~MEM out i.inst_outputs /\
  step_inst fuel C i (update_var out value s with vs_gas_readings := gs) = OK u ==>
  ?t. step_inst fuel C i s = OK t
Proof
  strip_tac >>
  drule_all dftCommutationTheory.step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s with vs_gas_readings := gs`,
    `value`] mp_tac) >>
  Cases_on `step_inst fuel C i (s with vs_gas_readings := gs)` >>
  simp[dftCommutationTheory.map_result_state_def] >> strip_tac >>
  drule_all dft_nonconsuming_oracle_frame >>
  disch_then (qspecl_then [`s`, `gs`, `fuel`, `C`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[lift_result_def]
QED

Theorem dft_gas_noninvoke_success_first:
  dft_gas_swap_pair g i /\ g.inst_opcode = GAS /\ inst_wf g /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C g s = OK sg /\ step_inst fuel C i sg = OK st ==>
  ?t. step_inst fuel C i s = OK t /\ step_inst fuel C g t = OK st
Proof
  strip_tac >> drule_all dft_gas_ok_shape >> strip_tac >>
  drule_all dft_independent_gas_output >> strip_tac >>
  gvs[] >>
  `!v. MEM (Var v) i.inst_operands ==> out <> v` by metis_tac[] >>
  drule_all dft_nonconsuming_updated_ok >> strip_tac >>
  drule_all dft_gas_noninvoke_ok_diamond >> strip_tac >>
  qexists_tac `t` >> gvs[]
QED

Theorem dft_gas_noninvoke_success_second:
  dft_gas_swap_pair g i /\ g.inst_opcode = GAS /\ inst_wf g /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK t /\ step_inst fuel C g t = OK st ==>
  ?sg. step_inst fuel C g s = OK sg /\ step_inst fuel C i sg = OK st
Proof
  strip_tac >> drule_all dft_gas_noninvoke_ok_diamond >> strip_tac >>
  qexists_tac `sg` >> gvs[]
QED

Theorem dft_noninvoke_ok_update_iff[local]:
  i.inst_opcode <> INVOKE /\
  ~MEM (Var out) i.inst_operands /\ ~MEM out i.inst_outputs ==>
  (step_inst fuel C i (update_var out value s) = OK u <=>
   ?t. step_inst fuel C i s = OK t /\ u = update_var out value t)
Proof
  strip_tac >>
  `!v. MEM (Var v) i.inst_operands ==> out <> v` by metis_tac[] >>
  drule_all dftCommutationTheory.step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `value`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >>
  simp[dftCommutationTheory.map_result_state_def] >> metis_tac[]
QED

Theorem dft_noninvoke_ok_fold_iff:
  !us s u.
  i.inst_opcode <> INVOKE /\
  EVERY (\p. ~MEM (Var (FST p)) i.inst_operands /\
             ~MEM (FST p) i.inst_outputs) us ==>
  (step_inst fuel C i (FOLDL (\s p. update_var (FST p) (SND p) s) s us) = OK u <=>
   ?t. step_inst fuel C i s = OK t /\
       u = FOLDL (\s p. update_var (FST p) (SND p) s) t us)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[dft_noninvoke_ok_update_iff] >> metis_tac[]
QED

(* GAS-free external success replay boundaries. *)
Theorem dft_gas_extract_result_fmp[local]:
  extract_venom_result s value off sz result = SOME (v,t) ==>
  t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac `case res of INL _ => _ | INR NONE => _ | INR (SOME _) => _` >>
  Cases_on `res` >> gvs[AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `case opt of NONE => _ | SOME _ => _` >>
  Cases_on `opt` >> gvs[]
QED

Theorem dft_gas_external_ok_fmp_fields[local]:
  is_ext_call_op i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  fs[is_ext_call_op_def] >> fs[Once step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  with_opcode_clause simp >>
  simp[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
       AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  drule dft_gas_extract_result_fmp >> simp[update_var_def]
QED

Theorem dft_gas_all_read_empty_write[local]:
  read_effects y.inst_opcode = all_effects /\
  effects_independent x.inst_opcode y.inst_opcode ==>
  write_effects x.inst_opcode = empty_effects
Proof
  strip_tac >> gvs[effects_independent_def] >>
  Cases_on `x.inst_opcode` >>
  gvs[write_effects_def, all_effects_def, empty_effects_def]
QED

Theorem dft_gas_external_partner_empty_write[local]:
  dft_gas_swap_pair x y /\ is_ext_call_op y.inst_opcode ==>
  write_effects x.inst_opcode = empty_effects
Proof
  strip_tac >> irule dft_gas_all_read_empty_write >>
  qexists_tac `y` >> gvs[dft_gas_swap_pair_def] >>
  Cases_on `y.inst_opcode` >> gvs[is_ext_call_op_def, read_effects_def]
QED

Theorem dft_gas_external_partner_operand[local]:
  dft_gas_swap_pair x y /\ step_inst fuel C y s = OK t /\
  MEM op x.inst_operands ==> eval_operand op t = eval_operand op s
Proof
  strip_tac >> irule dftBlockSimTheory.eval_operand_step_pres >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_gas_swap_pair_def, inst_defs_def, inst_uses_def] >>
  rpt strip_tac >> gvs[] >>
  drule dftBlockSimTheory.mem_var_operand_vars >> strip_tac >>
  fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_gas_external_read_memory[local]:
  dft_gas_swap_pair x y /\ step_inst fuel C y s = OK t /\
  Eff_MEMORY IN read_effects x.inst_opcode ==> t.vs_memory = s.vs_memory
Proof
  strip_tac >> irule venomInstProofsTheory.write_effects_sound_memory >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_gas_swap_pair_def, effects_independent_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_gas_external_read_storage[local]:
  dft_gas_swap_pair x y /\ step_inst fuel C y s = OK t /\
  Eff_STORAGE IN read_effects x.inst_opcode ==>
  contract_storage t = contract_storage s
Proof
  strip_tac >> irule venomInstProofsTheory.write_effects_sound_storage >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_gas_swap_pair_def, effects_independent_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_gas_external_read_transient[local]:
  dft_gas_swap_pair x y /\ step_inst fuel C y s = OK t /\
  Eff_TRANSIENT IN read_effects x.inst_opcode ==> t.vs_transient = s.vs_transient
Proof
  strip_tac >> irule venomInstProofsTheory.write_effects_sound_transient >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_gas_swap_pair_def, effects_independent_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_gas_external_read_accounts[local]:
  dft_gas_swap_pair x y /\ is_ext_call_op y.inst_opcode /\
  step_inst fuel C y s = OK t /\
  (Eff_BALANCE IN read_effects x.inst_opcode \/
   Eff_EXTCODE IN read_effects x.inst_opcode) ==>
  t.vs_accounts = s.vs_accounts
Proof
  strip_tac >>
  `y.inst_opcode = STATICCALL` by
    (qpat_x_assum `is_ext_call_op _` mp_tac >>
     Cases_on `y.inst_opcode` >> simp[is_ext_call_op_def] >>
     gvs[dft_gas_swap_pair_def, effects_independent_def,
         write_effects_def, all_effects_def, empty_effects_def,
         pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  irule venomInstProofsTheory.write_effects_sound_accounts >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[is_alloca_op_def, is_terminator_def, write_effects_def]
QED

Theorem dft_gas_pure1_replay[local]:
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  exec_pure1 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_pure1 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `[(out,value)]` >> simp[] >> metis_tac[]
QED

Theorem dft_gas_pure2_replay[local]:
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  exec_pure2 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_pure2 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `[(out,value)]` >> simp[] >> metis_tac[]
QED

Theorem dft_gas_pure3_replay[local]:
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  exec_pure3 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_pure3 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_pure3_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `[(out,value)]` >> simp[] >> metis_tac[]
QED

Theorem dft_gas_read0_replay[local]:
  f t = f s /\ exec_read0 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_read0 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qexists_tac `[(out,f s)]` >> simp[]
QED

Theorem dft_gas_read1_replay[local]:
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  (!op v. MEM op x.inst_operands /\ eval_operand op s = SOME v ==>
           f v t = f v s) /\
  exec_read1 f x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       exec_read1 f x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `[(out,value)]` >> simp[] >> metis_tac[]
QED

Theorem dft_gas_free_empty_write_replay[local]:
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  write_effects x.inst_opcode = empty_effects /\
  (!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s) /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_code = s.vs_code /\
  t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\
  (Eff_MEMORY IN read_effects x.inst_opcode ==> t.vs_memory = s.vs_memory) /\
  (Eff_STORAGE IN read_effects x.inst_opcode ==>
     contract_storage t = contract_storage s) /\
  (Eff_TRANSIENT IN read_effects x.inst_opcode ==> t.vs_transient = s.vs_transient) /\
  ((Eff_BALANCE IN read_effects x.inst_opcode \/
    Eff_EXTCODE IN read_effects x.inst_opcode) ==> t.vs_accounts = s.vs_accounts) /\
  Eff_RETURNDATA NOTIN read_effects x.inst_opcode /\
  step_inst_base x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
       step_inst_base x t =
         OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)
Proof
  strip_tac >> Cases_on `x.inst_opcode` >>
  qpat_x_assum `write_effects _ = empty_effects` mp_tac >>
  simp[NoAsms, write_effects_def, empty_effects_def, all_effects_def] >>
  fs[is_pseudo_def, is_terminator_def, read_effects_def] >>
  with_opcode_clause (fn cs => gvs cs) >>
  all_tac
  >>~- ([`exec_pure1 f x t`], irule dft_gas_pure1_replay >> simp[])
  >>~- ([`exec_pure2 f x t`], irule dft_gas_pure2_replay >> simp[])
  >>~- ([`exec_pure3 f x t`], irule dft_gas_pure3_replay >> simp[])
  >>~- ([`exec_read0 _ _ _`], irule dft_gas_read0_replay >> simp[empty_effects_def])
  >>~- ([`exec_read1 _ _ _`], irule dft_gas_read1_replay >> simp[empty_effects_def, mload_def, sload_def, tload_def, contract_transient_def])
  >> gvs[AllCaseEqs(), empty_effects_def]
  >>~- ([`EVERY (\p. FST p = out) _`],
    qmatch_goalsub_abbrev_tac `update_var out value s` >>
    qexists_tac `[(out,value)]` >> simp[])
  >>~- ([`x.inst_opcode = BUMP`],
    qexists_tac `[(ptr_out,base_val); (next_out,base_val + sz)]` >> simp[])
  >> qexists_tac `[]` >> simp[]
QED

Theorem dft_gas_free_empty_write_ok_updates[local]:
  ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> GAS /\
  write_effects inst.inst_opcode = empty_effects /\
  step_inst fuel C inst s = OK t ==>
  ?updates. EVERY (\p. MEM (FST p) inst.inst_outputs) updates /\
    t = FOLDL (\u p. update_var (FST p) (SND p) u) s updates
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  fs[is_pseudo_def, is_terminator_def, write_effects_def,
     empty_effects_def, all_effects_def] >>
  fs[Once step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  with_opcode_clause simp >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
  >>~- ([`EVERY (\p. FST p = out) _`],
    qmatch_goalsub_abbrev_tac `update_var out value s` >>
    qexists_tac `[(out,value)]` >> simp[])
  >>~- ([`inst.inst_opcode = BUMP`],
    qexists_tac `[(ptr_out,base_val); (next_out,base_val + sz)]` >> simp[])
  >> qexists_tac `[]` >> simp[]
QED

Theorem dft_gas_free_external_replay_both[local]:
  dft_gas_swap_pair x y /\ x.inst_opcode <> GAS /\
  is_ext_call_op y.inst_opcode /\ step_inst fuel C y s = OK t ==>
  (!r. step_inst fuel C x s = OK r ==>
    ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
         r = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
         step_inst fuel C x t = OK (FOLDL (\u p. update_var (FST p) (SND p) u) t us)) /\
  (!r. step_inst fuel C x t = OK r ==>
    ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
         r = FOLDL (\u p. update_var (FST p) (SND p) u) t us /\
         step_inst fuel C x s = OK (FOLDL (\u p. update_var (FST p) (SND p) u) s us))
Proof
  strip_tac >>
  `write_effects x.inst_opcode = empty_effects` by
    metis_tac[dft_gas_external_partner_empty_write] >>
  `x.inst_opcode <> INVOKE` by
    (Cases_on `x.inst_opcode` >> gvs[write_effects_def, all_effects_def, empty_effects_def]) >>
  `Eff_RETURNDATA NOTIN read_effects x.inst_opcode` by
    (Cases_on `y.inst_opcode` >>
     gvs[dft_gas_swap_pair_def, effects_independent_def, is_ext_call_op_def,
         write_effects_def, all_effects_def, empty_effects_def,
         pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  drule_all venomInstProofsTheory.step_ext_call_preserves >> strip_tac >>
  drule_all dft_gas_external_ok_fmp_fields >> strip_tac >>
  `!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s` by
    metis_tac[dft_gas_external_partner_operand] >>
  `Eff_MEMORY IN read_effects x.inst_opcode ==> t.vs_memory = s.vs_memory` by
    metis_tac[dft_gas_external_read_memory] >>
  `Eff_STORAGE IN read_effects x.inst_opcode ==> contract_storage t = contract_storage s` by
    metis_tac[dft_gas_external_read_storage] >>
  `Eff_TRANSIENT IN read_effects x.inst_opcode ==> t.vs_transient = s.vs_transient` by
    metis_tac[dft_gas_external_read_transient] >>
  `(Eff_BALANCE IN read_effects x.inst_opcode \/ Eff_EXTCODE IN read_effects x.inst_opcode) ==>
    t.vs_accounts = s.vs_accounts` by metis_tac[dft_gas_external_read_accounts] >>
  fs[dft_gas_swap_pair_def, is_alloca_op_def] >>
  conj_tac >> rpt strip_tac >> fs[step_inst_non_invoke] >>
  irule dft_gas_free_empty_write_replay >> simp[] >>
  metis_tac[step_inst_non_invoke, is_alloca_op_def]
QED

Theorem dft_gas_swap_updates_disjoint[local]:
  dft_gas_swap_pair x y /\
  EVERY (\p. MEM (FST p) x.inst_outputs) us ==>
  EVERY (\p. ~MEM (Var (FST p)) y.inst_operands /\
              ~MEM (FST p) y.inst_outputs) us
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  fs[dft_gas_swap_pair_def, inst_defs_def, inst_uses_def,
     pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[dftBlockSimTheory.mem_var_operand_vars]
QED

Theorem dft_gas_free_external_success_first[local]:
  dft_gas_swap_pair a b /\ b.inst_opcode <> GAS /\
  is_ext_call_op a.inst_opcode /\
  step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
  ?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
Proof
  strip_tac >>
  `dft_gas_swap_pair b a` by metis_tac[dft_gas_swap_pair_sym] >>
  drule_all dft_gas_free_external_replay_both >> strip_tac >>
  first_x_assum (drule_at Any) >> strip_tac >>
  qexists_tac `FOLDL (\u p. update_var (FST p) (SND p) u) s us` >>
  simp[] >>
  `EVERY (\p. ~MEM (Var (FST p)) a.inst_operands /\
              ~MEM (FST p) a.inst_outputs) us` by
    metis_tac[dft_gas_swap_updates_disjoint] >>
  `a.inst_opcode <> INVOKE` by
    (Cases_on `a.inst_opcode` >> gvs[is_ext_call_op_def]) >>
  simp[dft_noninvoke_ok_fold_iff] >> metis_tac[]
QED

Theorem dft_gas_free_external_success_second[local]:
  dft_gas_swap_pair a b /\ a.inst_opcode <> GAS /\
  is_ext_call_op b.inst_opcode /\
  step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
  ?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
Proof
  strip_tac >>
  `write_effects a.inst_opcode = empty_effects` by
    metis_tac[dft_gas_external_partner_empty_write] >>
  `?us. EVERY (\p. MEM (FST p) a.inst_outputs) us /\
        sa = FOLDL (\u p. update_var (FST p) (SND p) u) s us` by
    (irule dft_gas_free_empty_write_ok_updates >>
     gvs[dft_gas_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
  `EVERY (\p. ~MEM (Var (FST p)) b.inst_operands /\
              ~MEM (FST p) b.inst_outputs) us` by
    metis_tac[dft_gas_swap_updates_disjoint] >>
  `b.inst_opcode <> INVOKE` by
    (Cases_on `b.inst_opcode` >> gvs[is_ext_call_op_def]) >>
  `?sb. step_inst fuel C b s = OK sb /\
        sab = FOLDL (\u p. update_var (FST p) (SND p) u) sb us` by
    metis_tac[dft_noninvoke_ok_fold_iff] >>
  qexists_tac `sb` >> simp[] >>
  drule_all dft_gas_free_external_replay_both >> strip_tac >>
  qpat_x_assum `!r. step_inst fuel C a s = OK r ==> _` drule >> strip_tac >>
  `EVERY (\p. ~MEM (Var (FST p)) b.inst_operands /\
              ~MEM (FST p) b.inst_outputs) us'` by
    metis_tac[dft_gas_swap_updates_disjoint] >>
  `step_inst fuel C b sa =
     OK (FOLDL (\u p. update_var (FST p) (SND p) u) sb us')` by
    metis_tac[dft_noninvoke_ok_fold_iff] >> gvs[]
QED

Theorem dft_gas_external_success:
  dft_gas_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  (is_ext_call_op a.inst_opcode \/ is_ext_call_op b.inst_opcode) /\
  step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
  ?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
Proof
  strip_tac >> (
  `dft_gas_swap_pair b a` by metis_tac[dft_gas_swap_pair_sym] >>
  Cases_on `a.inst_opcode = GAS`
  >- (`b.inst_opcode <> GAS /\ b.inst_opcode <> INVOKE` by
        (Cases_on `b.inst_opcode` >> gvs[is_ext_call_op_def]) >>
      metis_tac[dft_gas_noninvoke_success_first]) >>
  Cases_on `b.inst_opcode = GAS`
  >- (`a.inst_opcode <> INVOKE` by
        (Cases_on `a.inst_opcode` >> gvs[is_ext_call_op_def]) >>
      metis_tac[dft_gas_noninvoke_success_second]) >>
  metis_tac[dft_gas_free_external_success_first,
            dft_gas_free_external_success_second])
QED

Theorem dft_swap_output_frame:
  dft_gas_swap_pair x y ==>
  (!v. MEM v x.inst_outputs ==>
       ~MEM (Var v) y.inst_operands /\ ~MEM v y.inst_outputs)
Proof
  strip_tac >>
  gvs[dft_gas_swap_pair_def, inst_defs_def, inst_uses_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[dftBlockSimTheory.mem_var_operand_vars]
QED


(* The pairs dft_abort_compatible admits beyond abort_compatible, when
   neither is an external call: an ASSERT next to a state write, which
   venomEffects counts as CanExHalt for static frames. *)
Theorem dft_swap_fallible_noncall[local]:
  !op. opcode_fail_class op <> NoFail /\ ~is_ext_call_op op /\ ~is_terminator op ==>
  MEM op [ASSERT; ASSERT_UNREACHABLE; RETURNDATACOPY; SSTORE; TSTORE; LOG;
          INVOKE]
Proof
  Cases >> simp[opcode_fail_class_def, is_ext_call_op_def, is_terminator_def]
QED

Theorem dft_swap_not_abort_compatible_assert[local]:
  dft_gas_swap_pair a b /\
  ~is_ext_call_op a.inst_opcode /\ ~is_ext_call_op b.inst_opcode /\
  ~abort_compatible a.inst_opcode b.inst_opcode ==>
  a.inst_opcode = ASSERT \/ b.inst_opcode = ASSERT
Proof
  strip_tac >>
  `opcode_fail_class a.inst_opcode <> NoFail /\
   opcode_fail_class b.inst_opcode <> NoFail` by gvs[abort_compatible_def] >>
  `~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  qspec_then `a.inst_opcode` mp_tac dft_swap_fallible_noncall >>
  impl_tac >- simp[] >>
  qspec_then `b.inst_opcode` mp_tac dft_swap_fallible_noncall >>
  impl_tac >- simp[] >>
  simp[] >> rpt strip_tac >>
  gvs[dft_gas_swap_pair_def, abort_compatible_def, opcode_fail_class_def,
      dft_abort_compatible_def, dft_abort_kind_def, effects_independent_def,
      read_effects_def, write_effects_def, all_effects_def, empty_effects_def]
QED

(* A successful ASSERT leaves the state alone and succeeds again on any
   state that agrees on its operand. *)
Theorem dft_assert_ok_state[local]:
  i.inst_opcode = ASSERT /\ step_inst fuel C i s = OK t ==> t = s
Proof
  strip_tac >> gvs[step_inst_non_invoke] >> with_opcode_clause gvs >>
  gvs[AllCaseEqs()]
QED

Theorem dft_assert_ok_replay[local]:
  i.inst_opcode = ASSERT /\ step_inst fuel C i s = OK s /\
  (!op. MEM op i.inst_operands ==> eval_operand op t = eval_operand op s) ==>
  step_inst fuel C i t = OK t
Proof
  strip_tac >> gvs[step_inst_non_invoke] >> with_opcode_clause gvs >>
  gvs[AllCaseEqs()]
QED

Theorem dft_assert_swap_ok[local]:
  dft_gas_swap_pair a b /\ ~gas_pair a.inst_opcode b.inst_opcode /\
  (a.inst_opcode = ASSERT \/ b.inst_opcode = ASSERT) /\
  step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
  ?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
Proof
  strip_tac >>
  `~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `dft_gas_swap_pair b a` by metis_tac[dft_gas_swap_pair_sym]
  >- (`sa = s` by metis_tac[dft_assert_ok_state] >> pop_assum SUBST_ALL_TAC >>
      `!op. MEM op a.inst_operands ==> eval_operand op sab = eval_operand op s` by
        (rpt strip_tac >> irule dftBlockSimTheory.eval_operand_step_pres >>
         qexistsl_tac [`C`, `fuel`, `b`] >> simp[] >>
         metis_tac[dft_swap_output_frame]) >>
      metis_tac[dft_assert_ok_replay]) >>
  `sab = sa` by metis_tac[dft_assert_ok_state] >> pop_assum SUBST_ALL_TAC >>
  `!op. MEM op b.inst_operands ==> eval_operand op sa = eval_operand op s` by
    (rpt strip_tac >> irule dftBlockSimTheory.eval_operand_step_pres >>
     qexistsl_tac [`C`, `fuel`, `a`] >> simp[] >>
     metis_tac[dft_swap_output_frame]) >>
  `step_inst fuel C b s = OK s` by
    metis_tac[dft_assert_ok_replay] >>
  simp[]
QED

Theorem dft_nongas_pair_success:
  dft_gas_swap_pair a b /\ ~gas_pair a.inst_opcode b.inst_opcode /\
  inst_wf a /\ inst_wf b /\
  step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
  ?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
Proof
  strip_tac >>
  Cases_on `is_ext_call_op a.inst_opcode \/ is_ext_call_op b.inst_opcode`
  >- (drule_all dft_gas_external_success >> simp[]) >>
  Cases_on `abort_compatible a.inst_opcode b.inst_opcode`
  >- (`ext_bi_independent a b` by
        gvs[dft_gas_swap_pair_def, ext_bi_independent_def] >>
      drule_all step_swap_ok_ext >> simp[]) >>
  `a.inst_opcode = ASSERT \/ b.inst_opcode = ASSERT` by
    metis_tac[dft_swap_not_abort_compatible_assert] >>
  irule dft_assert_swap_ok >> metis_tac[]
QED

Theorem dft_indexed_nongas_pair_ok:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y /\
  step_inst fuel C y s = OK sy /\
  step_inst fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
  ?sx sxy.
    step_inst fuel C x s = OK sx /\
    step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
    (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (syx with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `step_inst fuel C x sy = OK (syx with vs_inst_idx := sy.vs_inst_idx)` by
    (qpat_x_assum `step_inst _ _ y s = _` kall_tac >>
     drule_all dft_step_ok_idx >>
     disch_then (qspec_then `sy.vs_inst_idx` mp_tac) >> simp[]) >>
  `dft_gas_swap_pair y x /\ ~gas_pair y.inst_opcode x.inst_opcode` by
    (gvs[dft_gas_swap_pair_sym, dftBlockSimTheory.gas_pair_def] >> metis_tac[]) >>
  drule_all dft_nongas_pair_success >> strip_tac >>
  qexistsl_tac [`sb`, `syx with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[] >>
  drule_all dft_step_ok_idx >>
  disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[]
QED

Theorem dft_suffix_nongas_pair_ok:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y /\
  step_inst fuel C y s = OK sy /\
  step_inst fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
  dft_exec_suffix fuel C (x::y::tail) s =
  dft_exec_suffix fuel C (y::x::tail) s
Proof
  strip_tac >> drule_all dft_indexed_nongas_pair_ok >> strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def]
QED

(* Stopping INVOKEs retain their callee state and callee instruction index. *)
Theorem dft_invoke_stopping_idx:
  i.inst_opcode = INVOKE /\ (!t. r <> OK t) ==>
  (step_inst fuel C i (s with vs_inst_idx := n) = r <=>
   step_inst fuel C i s = r)
Proof
  strip_tac >>
  simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
  Cases_on `step_inst fuel C i s` >> simp[] >> metis_tac[]
QED

Theorem dft_invoke_stopping_update:
  i.inst_opcode = INVOKE /\ (!t. r <> OK t) /\
  (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
  ~MEM out i.inst_outputs ==>
  (step_inst fuel C i (update_var out value s) = r <=>
   step_inst fuel C i s = r)
Proof
  strip_tac >> drule_all dftCommutationTheory.step_inst_invoke_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `value`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[] >> metis_tac[]
QED

Theorem dft_gas_invoke_stopping_first:
  dft_gas_swap_pair g c /\ g.inst_opcode = GAS /\ inst_wf g /\
  c.inst_opcode = INVOKE /\ (!t. r <> OK t) /\
  step_inst fuel C c s' = r ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    dft_exec_suffix fuel C (g::c::tail) s = r /\
    dft_exec_suffix fuel C (c::g::tail) s' = r
Proof
  strip_tac >> drule_all dft_gas_ok_shape >> strip_tac >>
  drule_all dft_independent_gas_output >> strip_tac >>
  qexists_tac `s' with vs_gas_readings := 0w::s'.vs_gas_readings` >>
  simp[] >>
  `step_inst fuel C c (update_var out 0w s' with vs_inst_idx := SUC s'.vs_inst_idx) = r` by
    (simp[dft_invoke_stopping_idx] >>
     metis_tac[dft_invoke_stopping_update]) >>
  Cases_on `r` >> gvs[dft_exec_suffix_cons, dft_exec_cons_def,
    is_terminator_def, update_var_def]
QED

Theorem dft_gas_invoke_stopping_second:
  dft_gas_swap_pair g c /\ g.inst_opcode = GAS /\ inst_wf g /\
  c.inst_opcode = INVOKE /\ (!t. r <> OK t) /\
  step_inst fuel C g s' = OK sg /\
  step_inst fuel C c (sg with vs_inst_idx := SUC s'.vs_inst_idx) = r ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    dft_exec_suffix fuel C (c::g::tail) s = r /\
    dft_exec_suffix fuel C (g::c::tail) s' = r
Proof
  strip_tac >> drule_all dft_gas_ok_shape >> strip_tac >>
  drule_all dft_independent_gas_output >> strip_tac >>
  qexists_tac `s' with vs_gas_readings := TL s'.vs_gas_readings` >>
  simp[] >>
  `step_inst fuel C c (s' with vs_gas_readings := TL s'.vs_gas_readings) = r` by
    (`step_inst fuel C c sg = r` by
       metis_tac[dft_invoke_stopping_idx, exec_result_distinct] >>
     `sg = update_var out
        (if s'.vs_gas_readings = [] then 0w else HD s'.vs_gas_readings)
        (s' with vs_gas_readings := TL s'.vs_gas_readings)` by gvs[] >>
     qpat_x_assum `sg = _` SUBST_ALL_TAC >>
     metis_tac[dft_invoke_stopping_update]) >>
  Cases_on `r` >> gvs[dft_exec_suffix_cons, dft_exec_cons_def,
    is_terminator_def]
QED

(* Constructor observations for the remaining nongas stopping swaps. *)
Theorem dft_swap_abort_update_iff[local]:
  ~MEM (Var v) i.inst_operands /\ ~MEM v i.inst_outputs ==>
  ((?t. step_inst fuel C i (update_var v w s) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  strip_tac >>
  `!z. MEM (Var z) i.inst_operands ==> v <> z` by metis_tac[] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (drule_all dftCommutationTheory.step_inst_invoke_frame >>
      disch_then (qspecl_then [`fuel`, `C`, `s`, `w`] mp_tac) >>
      Cases_on `step_inst fuel C i s` >> simp[] >> metis_tac[]) >>
  drule_all dftCommutationTheory.step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `w`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >>
  simp[dftCommutationTheory.map_result_state_def] >> metis_tac[]
QED

Theorem dft_swap_abort_fold_iff:
  !us s.
  EVERY (\p. ~MEM (Var (FST p)) i.inst_operands /\
              ~MEM (FST p) i.inst_outputs) us ==>
  ((?t. step_inst fuel C i
     (FOLDL (\u p. update_var (FST p) (SND p) u) s us) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[dft_swap_abort_update_iff]
QED

Theorem dft_swap_invoke_stopping_fold:
  !us s.
  i.inst_opcode = INVOKE /\ (!t. r <> OK t) /\
  EVERY (\p. ~MEM (Var (FST p)) i.inst_operands /\
              ~MEM (FST p) i.inst_outputs) us ==>
  (step_inst fuel C i
     (FOLDL (\u p. update_var (FST p) (SND p) u) s us) = r <=>
   step_inst fuel C i s = r)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!s. _ ==> (_ <=> _)`
    (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  irule dft_invoke_stopping_update >> simp[] >> metis_tac[]
QED

Theorem dft_swap_error_idx_iff:
  ~is_terminator i.inst_opcode ==>
  (step_inst fuel C i (s with vs_inst_idx := n) = Error e <=>
   step_inst fuel C i s = Error e)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE` >>
  simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only,
       analysisSimProofsBaseTheory.step_inst_idx_indep] >>
  Cases_on `step_inst fuel C i s` >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem dft_swap_abort_idx_iff:
  ~is_terminator i.inst_opcode ==>
  ((?t. step_inst fuel C i (s with vs_inst_idx := n) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE` >>
  simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only,
       analysisSimProofsBaseTheory.step_inst_idx_indep] >>
  Cases_on `step_inst fuel C i s` >> simp[instIdxIndepTheory.exec_result_map_def] >> metis_tac[]
QED

Theorem dft_swap_nonterminator_no_intret:
  ~is_terminator i.inst_opcode ==> step_inst fuel C i s <> IntRet vs t
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (simp[step_inst_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >>
  simp[step_inst_non_invoke] >> strip_tac >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[is_terminator_def]
QED

Theorem dft_swap_nonterminator_halt_invoke:
  ~is_terminator i.inst_opcode /\ step_inst fuel C i s = Halt t ==>
  i.inst_opcode = INVOKE
Proof
  strip_tac >> spose_not_then assume_tac >>
  gvs[step_inst_non_invoke] >> drule step_inst_base_halt_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem dft_gas_free_empty_write_abort_iff:
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  write_effects x.inst_opcode = empty_effects /\
  step_inst fuel C x s = OK t /\
  (!v. MEM v x.inst_outputs ==>
       ~MEM (Var v) y.inst_operands /\ ~MEM v y.inst_outputs) ==>
  ((?u. step_inst fuel C y t = Abort a u) <=>
   (?u. step_inst fuel C y s = Abort a u))
Proof
  strip_tac >> drule_all dft_gas_free_empty_write_ok_updates >> strip_tac >>
  gvs[] >> irule dft_swap_abort_fold_iff >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem dft_gas_free_empty_write_invoke_stopping:
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  write_effects x.inst_opcode = empty_effects /\
  step_inst fuel C x s = OK t /\ y.inst_opcode = INVOKE /\
  (!u. r <> OK u) /\
  (!v. MEM v x.inst_outputs ==>
       ~MEM (Var v) y.inst_operands /\ ~MEM v y.inst_outputs) ==>
  (step_inst fuel C y t = r <=> step_inst fuel C y s = r)
Proof
  strip_tac >> drule_all dft_gas_free_empty_write_ok_updates >> strip_tac >>
  gvs[] >> irule dft_swap_invoke_stopping_fold >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem dft_swap_operand_defined:
  (!v. MEM (Var v) ops ==> v IN FDOM s.vs_vars) /\
  (!l. MEM (Label l) ops ==> l IN FDOM s.vs_labels) ==>
  !op. MEM op ops ==> ?w. eval_operand op s = SOME w
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def] >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem dft_swap_pure1_total[local]:
  LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure1 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  gvs[exec_pure1_def]
QED

Theorem dft_swap_pure2_total[local]:
  LENGTH inst.inst_operands = 2 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure2 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  simp[exec_pure2_def]
QED

Theorem dft_swap_pure3_total[local]:
  LENGTH inst.inst_operands = 3 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_pure3 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2; op3]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  `?v3. eval_operand op3 s = SOME v3` by metis_tac[] >>
  simp[exec_pure3_def]
QED

Theorem dft_swap_read0_total[local]:
  LENGTH inst.inst_outputs = 1 ==> ?t. exec_read0 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> simp[exec_read0_def]
QED

Theorem dft_swap_read1_total[local]:
  LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_read1 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[exec_read1_def]
QED

Theorem dft_swap_write2_total[local]:
  LENGTH inst.inst_operands = 2 /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. exec_write2 f inst s = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [op1; op2]` >>
  `?v1. eval_operand op1 s = SOME v1` by metis_tac[] >>
  `?v2. eval_operand op2 s = SOME v2` by metis_tac[] >>
  simp[exec_write2_def]
QED

Definition dft_swap_runtime_error_opcode_def:
  dft_swap_runtime_error_opcode op <=> MEM op [DELEGATECALL; CREATE; CREATE2]
End

Theorem dft_swap_ext_call_total[local]:
  LENGTH inst.inst_outputs = 1 ==>
  ?t. exec_ext_call inst s gas addr value ao az ro rz static = OK t
Proof
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >>
  simp[exec_ext_call_def] >> pairarg_tac >> simp[]
QED

Theorem dft_swap_eval_operands_defined[local]:
  !ops. (!op. MEM op ops ==> ?v. eval_operand op s = SOME v) ==>
        ?vs. eval_operands ops s = SOME vs
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem dft_swap_guarded_nofail_total:
  inst_wf inst /\ ~is_pseudo inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> ALLOCA /\
  opcode_fail_class inst.inst_opcode = NoFail /\
  ~dft_swap_runtime_error_opcode inst.inst_opcode /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v)
  ==> ?t. step_inst fuel C inst s = OK t
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  fs[is_pseudo_def, is_terminator_def, opcode_fail_class_def,
     dft_swap_runtime_error_opcode_def] >> fs[inst_wf_def] >>
  simp[Once step_inst_non_invoke] >>
  with_opcode_clause simp >>
  all_tac
  >>~- ([`exec_pure1 _ _ _`], irule dft_swap_pure1_total >> simp[])
  >>~- ([`exec_pure2 _ _ _`], irule dft_swap_pure2_total >> simp[])
  >>~- ([`exec_pure3 _ _ _`], irule dft_swap_pure3_total >> simp[])
  >>~- ([`exec_read0 _ _ _`], irule dft_swap_read0_total >> simp[])
  >>~- ([`exec_read1 _ _ _`], irule dft_swap_read1_total >> simp[])
  >>~- ([`exec_write2 _ _ _`], irule dft_swap_write2_total >> simp[])
  >>~- ([`eval_operands _ _`], suspend "log_total") >>
  gvs[LENGTH_EQ_NUM_compute, DISJ_IMP_THM, FORALL_AND_THM]
  >>~- ([`exec_ext_call _ _ _ _ _ _ _ _ _ _`],
         irule dft_swap_ext_call_total >> simp[])
  >>~- ([`exec_gas _ _`], simp[exec_gas_def] >> CASE_TAC >> simp[])
QED

Resume dft_swap_guarded_nofail_total[log_total]:
  `MEM (EL 0 (REVERSE rest)) rest /\ MEM (EL 1 (REVERSE rest)) rest` by
    (conj_tac >> once_rewrite_tac[GSYM MEM_REVERSE] >>
     irule EL_MEM >> simp[]) >>
  `?off. eval_operand (EL 0 (REVERSE rest)) s = SOME off` by metis_tac[MEM] >>
  `?sz. eval_operand (EL 1 (REVERSE rest)) s = SOME sz` by metis_tac[MEM] >>
  `?topics. eval_operands (DROP 2 (REVERSE rest)) s = SOME topics` by
    (irule dft_swap_eval_operands_defined >> rpt strip_tac >>
     drule rich_listTheory.MEM_DROP_IMP >> simp[] >> strip_tac >> metis_tac[MEM]) >> fs[]
QED

Finalise dft_swap_guarded_nofail_total

(* An instruction of the static-frame class CanExHalt, other than CREATE
   and CREATE2, either succeeds or halts exceptionally once its operands
   are defined. *)
Theorem dft_swap_canexhalt_operand_defined:
  inst_wf i /\ opcode_fail_class i.inst_opcode = CanExHalt /\
  ~is_terminator i.inst_opcode /\
  ~dft_swap_runtime_error_opcode i.inst_opcode /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  (?t. step_inst fuel C i s = OK t) \/
  (?t. step_inst fuel C i s = Abort ExHalt_abort t)
Proof
  strip_tac >>
  `?vs. eval_operands i.inst_operands s = SOME vs` by
    metis_tac[dft_swap_eval_operands_defined] >>
  Cases_on `i.inst_opcode` >>
  gvs[opcode_fail_class_def, is_terminator_def,
      dft_swap_runtime_error_opcode_def] >>
  gvs[inst_wf_def] >> simp[step_inst_non_invoke] >>
  with_opcode_clause simp >>
  all_tac
  >>~- ([`exec_write2 _ _ _`],
        IF_CASES_TAC >> simp[] >>
        disj1_tac >> irule dft_swap_write2_total >> simp[])
  >>~- ([`exec_ext_call _ _ _ _ _ _ _ _ _ _`],
        gvs[LENGTH_EQ_NUM_compute, DISJ_IMP_THM, FORALL_AND_THM] >>
        rpt IF_CASES_TAC >> simp[] >>
        disj1_tac >> irule dft_swap_ext_call_total >> simp[])
  >>~- ([`_ with vs_logs := _`],
        IF_CASES_TAC >> simp[] >>
        `MEM (EL 0 (REVERSE rest)) rest /\ MEM (EL 1 (REVERSE rest)) rest` by
          (conj_tac >> once_rewrite_tac[GSYM MEM_REVERSE] >>
           irule EL_MEM >> simp[]) >>
        `?off. eval_operand (EL 0 (REVERSE rest)) s = SOME off` by metis_tac[MEM] >>
        `?sz. eval_operand (EL 1 (REVERSE rest)) s = SOME sz` by metis_tac[MEM] >>
        `?topics. eval_operands (DROP 2 (REVERSE rest)) s = SOME topics` by
          (irule dft_swap_eval_operands_defined >> rpt strip_tac >>
           drule rich_listTheory.MEM_DROP_IMP >> simp[] >> strip_tac >>
           metis_tac[MEM]) >>
        fs[])
  >> gvs[LENGTH_EQ_NUM_compute, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem dft_swap_invoke_partner_class:
  dft_gas_swap_pair x y /\ x.inst_opcode = INVOKE ==>
  write_effects y.inst_opcode = empty_effects /\
  opcode_fail_class y.inst_opcode = NoFail /\
  ~dft_swap_runtime_error_opcode y.inst_opcode
Proof
  strip_tac >> Cases_on `y.inst_opcode` >>
  simp[write_effects_def, opcode_fail_class_def, dft_swap_runtime_error_opcode_def] >>
  gvs[dft_gas_swap_pair_def, effects_independent_def, dft_abort_compatible_def,
      dft_abort_kind_def, is_terminator_def,
      opcode_fail_class_def, read_effects_def, write_effects_def,
      dft_swap_runtime_error_opcode_def, all_effects_def, empty_effects_def]
QED

Theorem dft_swap_noninvoke_abort_replay:
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  (!op. MEM op i.inst_operands ==> eval_operand op s' = eval_operand op s) /\
  (i.inst_opcode = RETURNDATACOPY ==> s'.vs_returndata = s.vs_returndata) /\
  s'.vs_call_ctx = s.vs_call_ctx /\
  step_inst fuel C i s = Abort a t ==>
  ?t'. step_inst fuel C i s' = Abort a t'
Proof
  strip_tac >>
  `eval_operands i.inst_operands s' = eval_operands i.inst_operands s` by
    (qpat_x_assum `!op. _` mp_tac >> qspec_tac (`i.inst_operands`, `ops`) >>
     Induct >> simp[eval_operands_def]) >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_terminator_def] >> with_opcode_clause gvs >>
  gvs[AllCaseEqs(), exec_create_abort_iff] >>
  gvs[exec_ext_call_def, exec_write2_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[EXISTS_OR_THM]
QED

Theorem dft_nongas_pair_abort_iff:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  step_inst fuel C x s = OK t ==>
  ((?u. step_inst fuel C y t = Abort a u) <=>
   (?u. step_inst fuel C y s = Abort a u))
Proof
  strip_tac >> drule dft_swap_output_frame >> strip_tac >>
  `~is_terminator y.inst_opcode /\ ~is_terminator x.inst_opcode /\
   ~is_alloca_op x.inst_opcode /\
   effects_independent x.inst_opcode y.inst_opcode` by gvs[dft_gas_swap_pair_def] >>
  Cases_on `y.inst_opcode = INVOKE`
  >- (`dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
      `write_effects x.inst_opcode = empty_effects` by
        metis_tac[dft_swap_invoke_partner_class] >>
      irule dft_gas_free_empty_write_abort_iff >>
      gvs[dft_gas_swap_pair_def, dftBlockSimTheory.gas_pair_def] >>
      metis_tac[is_alloca_op_def]) >>
  `!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> irule dftBlockSimTheory.eval_operand_step_pres >>
     qexistsl_tac [`C`, `fuel`, `x`] >> simp[] >> metis_tac[]) >>
  `(y.inst_opcode = RETURNDATACOPY ==> t.vs_returndata = s.vs_returndata)` by
    (strip_tac >> irule venomInstProofsTheory.write_effects_sound_returndata >>
     qexistsl_tac [`C`, `fuel`, `x`] >> simp[] >>
     gvs[effects_independent_def, read_effects_def, empty_effects_def,
         pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by metis_tac[venomInstProofsTheory.step_preserves_call_ctx] >>
  eq_tac >> strip_tac >> irule dft_swap_noninvoke_abort_replay >> metis_tac[]
QED

Theorem dft_swap_nonroot_abort_class:
  inst_wf x /\ ~is_terminator x.inst_opcode /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  step_inst fuel C x s = Abort a t ==>
  x.inst_opcode = INVOKE \/
  (opcode_fail_class x.inst_opcode = CanExHalt /\ a = ExHalt_abort)
Proof
  strip_tac >> Cases_on `x.inst_opcode = INVOKE` >- simp[] >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_terminator_def, inst_wf_def, read_effects_def, write_effects_def] >>
  with_opcode_clause gvs >>
  gvs[AllCaseEqs(), opcode_fail_class_def, exec_create_abort_iff,
      exec_write2_def] >>
  (* a static CALL without value: the external call itself never aborts *)
  gvs[LENGTH_EQ_NUM_compute, exec_ext_call_def] >> pairarg_tac >> gvs[]
QED

Theorem dft_swap_returndatacopy_partner_class:
  dft_gas_swap_pair x y /\ x.inst_opcode = RETURNDATACOPY ==>
  (opcode_fail_class y.inst_opcode = NoFail /\
   ~dft_swap_runtime_error_opcode y.inst_opcode) \/
  opcode_fail_class y.inst_opcode = CanExHalt
Proof
  strip_tac >> Cases_on `y.inst_opcode` >>
  simp[write_effects_def, opcode_fail_class_def, dft_swap_runtime_error_opcode_def] >>
  gvs[dft_gas_swap_pair_def, effects_independent_def, dft_abort_compatible_def,
      dft_abort_kind_def, is_terminator_def,
      opcode_fail_class_def, read_effects_def, write_effects_def,
      dft_swap_runtime_error_opcode_def, all_effects_def, empty_effects_def]
QED

Theorem dft_nongas_pair_sym[local]:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode ==>
  dft_gas_swap_pair y x /\ ~gas_pair y.inst_opcode x.inst_opcode
Proof
  gvs[dft_gas_swap_pair_sym, dftBlockSimTheory.gas_pair_def] >> metis_tac[]
QED

Theorem dft_nongas_suffix_second_invoke_halt[local]:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  write_effects x.inst_opcode = empty_effects /\ y.inst_opcode = INVOKE /\
  step_inst fuel C x s = OK sx /\
  step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Halt t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Halt t /\
  dft_exec_suffix fuel C (y::x::tail) s = Halt t
Proof
  strip_tac >> drule dft_swap_output_frame >> strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo x.inst_opcode /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS` by
    (gvs[dft_gas_swap_pair_def, dftBlockSimTheory.gas_pair_def] >>
     metis_tac[is_alloca_op_def]) >>
  `step_inst fuel C y sx = Halt t` by
    metis_tac[dft_invoke_stopping_idx, exec_result_distinct] >>
  `step_inst fuel C y s = Halt t` by
    metis_tac[dft_gas_free_empty_write_invoke_stopping, exec_result_distinct] >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def]
QED

Theorem dft_nongas_suffix_first_invoke_halt[local]:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  x.inst_opcode = INVOKE /\ write_effects y.inst_opcode = empty_effects /\
  step_inst fuel C y s = OK sy /\ step_inst fuel C x s = Halt t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Halt t /\
  dft_exec_suffix fuel C (y::x::tail) s = Halt t
Proof
  strip_tac >> drule_all dft_nongas_pair_sym >> strip_tac >>
  `!v. MEM v y.inst_outputs ==>
       ~MEM (Var v) x.inst_operands /\ ~MEM v x.inst_outputs` by
    metis_tac[dft_swap_output_frame] >>
  `~is_terminator y.inst_opcode /\ ~is_pseudo y.inst_opcode /\
   y.inst_opcode <> ALLOCA /\ y.inst_opcode <> GAS` by
    (gvs[dft_gas_swap_pair_def, dftBlockSimTheory.gas_pair_def] >>
     metis_tac[is_alloca_op_def]) >>
  `step_inst fuel C x sy = Halt t` by
    metis_tac[dft_gas_free_empty_write_invoke_stopping, exec_result_distinct] >>
  `step_inst fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx) = Halt t` by
    metis_tac[dft_invoke_stopping_idx, exec_result_distinct] >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def, is_terminator_def]
QED

Theorem dft_nongas_suffix_swap_halt:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\ inst_wf y /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  (step_inst fuel C x s = Halt t \/
   (?sx. step_inst fuel C x s = OK sx /\
     step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Halt t)) ==>
  dft_exec_suffix fuel C (x::y::tail) s = Halt t /\
  dft_exec_suffix fuel C (y::x::tail) s = Halt t
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo y.inst_opcode /\ y.inst_opcode <> ALLOCA` by
    (gvs[dft_gas_swap_pair_def] >> metis_tac[is_alloca_op_def])
  >- (`x.inst_opcode = INVOKE` by metis_tac[dft_swap_nonterminator_halt_invoke] >>
      drule_all dft_swap_invoke_partner_class >> strip_tac >>
      `y.inst_opcode <> INVOKE` by (strip_tac >> gvs[opcode_fail_class_def]) >>
      `y.inst_opcode <> CODECOPY` by
        (strip_tac >> gvs[write_effects_def, empty_effects_def]) >>
      `?sy. step_inst fuel C y s = OK sy` by metis_tac[dft_swap_guarded_nofail_total] >>
      irule dft_nongas_suffix_first_invoke_halt >> metis_tac[]) >>
  `y.inst_opcode = INVOKE` by metis_tac[dft_swap_nonterminator_halt_invoke] >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  `write_effects x.inst_opcode = empty_effects` by metis_tac[dft_swap_invoke_partner_class] >>
  irule dft_nongas_suffix_second_invoke_halt >> metis_tac[]
QED

Theorem dft_nongas_suffix_swap_error:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y /\
  (step_inst fuel C x s = Error e \/
   (?sx. step_inst fuel C x s = OK sx /\
     step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Error e)) ==>
  (!t. dft_exec_suffix fuel C (y::x::tail) s <> OK t) /\
  (!v t. dft_exec_suffix fuel C (y::x::tail) s <> IntRet v t)
Proof
  strip_tac >> (
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  drule_all dft_nongas_pair_sym >> strip_tac >>
  `(!v t. step_inst fuel C y s <> IntRet v t) /\
   (!u v t. step_inst fuel C x u <> IntRet v t)` by
    metis_tac[dft_swap_nonterminator_no_intret] >>
  Cases_on `step_inst fuel C y s` >>
  gvs[dft_exec_suffix_cons, dft_exec_cons_def] >>
  rename1 `step_inst fuel C y s = OK sy` >>
  Cases_on `step_inst fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx)` >>
  gvs[] >> drule_all dft_indexed_nongas_pair_ok >> strip_tac >> gvs[])
QED

Theorem dft_nongas_suffix_second_abort:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  step_inst fuel C x s = OK sx /\
  step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Abort a t /\
  ?u. dft_exec_suffix fuel C (y::x::tail) s = Abort a u
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `?u. step_inst fuel C y sx = Abort a u` by metis_tac[dft_swap_abort_idx_iff] >>
  `?u. step_inst fuel C y s = Abort a u` by metis_tac[dft_nongas_pair_abort_iff] >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def]
QED

(* Nothing in a block run writes the call context: PHIs and successful
   non-terminator steps keep it, an INVOKE's callee included, and so does a
   change of the gas oracle. *)
Theorem dft_eval_phis_call_ctx:
  !insts s u. eval_phis s insts = OK u ==> u.vs_call_ctx = s.vs_call_ctx
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  rw[AllCaseEqs()] >> gvs[update_var_def] >> metis_tac[]
QED

Theorem dft_prefix_call_ctx:
  !pre s t. EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[dft_exec_cons_def, AllCaseEqs()] >>
  res_tac >> fs[] >> metis_tac[venomInstProofsTheory.step_preserves_call_ctx]
QED

Theorem dft_gas_variant_call_ctx:
  s' = (s with vs_gas_readings := g) ==> s'.vs_call_ctx = s.vs_call_ctx
Proof
  simp[]
QED

(* Outside a static frame, an instruction that isn't a pure root aborts
   only as an INVOKE, or by an exceptional halt of RETURNDATACOPY, CREATE
   or CREATE2. *)
Theorem dft_swap_nonstatic_abort_class[local]:
  ~s.vs_call_ctx.cc_static /\
  inst_wf x /\ ~is_terminator x.inst_opcode /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  step_inst fuel C x s = Abort a t ==>
  x.inst_opcode = INVOKE \/
  (MEM x.inst_opcode [RETURNDATACOPY; CREATE; CREATE2] /\ a = ExHalt_abort)
Proof
  strip_tac >> Cases_on `x.inst_opcode = INVOKE` >- simp[] >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_terminator_def, inst_wf_def, read_effects_def, write_effects_def] >>
  with_opcode_clause gvs >>
  gvs[AllCaseEqs(), exec_create_abort_iff]
QED

Theorem dft_swap_fail_class_revert_any[local]:
  !op. (opcode_fail_class op = CanRevert ==> op = ASSERT) /\
       (opcode_fail_class op = AnyFail ==> op = INVOKE)
Proof
  Cases >> simp[opcode_fail_class_def]
QED

(* A swap partner of an exceptionally halting RETURNDATACOPY, CREATE or
   CREATE2 neither reverts nor invokes, and writes nothing they touch. *)
Theorem dft_swap_exhalt_partner_class[local]:
  dft_gas_swap_pair x y /\
  MEM x.inst_opcode [RETURNDATACOPY; CREATE; CREATE2] ==>
  y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY /\
  ~dft_swap_runtime_error_opcode y.inst_opcode /\
  (opcode_fail_class y.inst_opcode = NoFail \/
   opcode_fail_class y.inst_opcode = CanExHalt)
Proof
  strip_tac >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o SIMP_RULE list_ss []) >>
  `effects_independent x.inst_opcode y.inst_opcode /\
   dft_abort_compatible x.inst_opcode y.inst_opcode` by
    fs[dft_gas_swap_pair_def] >>
  `y.inst_opcode <> INVOKE /\ y.inst_opcode <> ASSERT` by
    (rpt strip_tac >>
     gvs[dft_abort_compatible_def, dft_abort_kind_def]) >>
  `y.inst_opcode <> CODECOPY /\ ~dft_swap_runtime_error_opcode y.inst_opcode` by
    (simp[dft_swap_runtime_error_opcode_def] >> rpt strip_tac >>
     gvs[effects_independent_def, read_effects_def, write_effects_def,
         all_effects_def]) >>
  simp[] >> Cases_on `opcode_fail_class y.inst_opcode` >> simp[] >>
  metis_tac[dft_swap_fail_class_revert_any]
QED

Theorem dft_nongas_suffix_first_abort:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y /\ ~s.vs_call_ctx.cc_static /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  step_inst fuel C x s = Abort a t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Abort a t /\
  ?u. dft_exec_suffix fuel C (y::x::tail) s = Abort a u
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `~is_pseudo y.inst_opcode /\ y.inst_opcode <> ALLOCA` by
    (gvs[dft_gas_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
  `(?sy. step_inst fuel C y s = OK sy) \/
   (?u. step_inst fuel C y s = Abort a u)` by
    (drule_all dft_swap_nonstatic_abort_class >> strip_tac
     >- (drule_all dft_swap_invoke_partner_class >> strip_tac >>
         `y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY` by
           (rpt strip_tac >> gvs[opcode_fail_class_def, write_effects_def,
                                 empty_effects_def]) >>
         metis_tac[dft_swap_guarded_nofail_total]) >>
     drule_all dft_swap_exhalt_partner_class >> strip_tac
     >- metis_tac[dft_swap_guarded_nofail_total] >>
     metis_tac[dft_swap_canexhalt_operand_defined])
  >- (drule_all dft_nongas_pair_sym >> strip_tac >>
      `?u. step_inst fuel C x sy = Abort a u` by metis_tac[dft_nongas_pair_abort_iff] >>
      `?u. step_inst fuel C x
          (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort a u` by
        metis_tac[dft_swap_abort_idx_iff] >>
      simp[dft_exec_suffix_cons, dft_exec_cons_def]) >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def]
QED

Theorem dft_nongas_suffix_swap:
  dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y /\ ~s.vs_call_ctx.cc_static /\
  (!v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars) /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
    !l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels) /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) ==>
  dft_res_rel (dft_exec_suffix fuel C (x::y::tail) s)
              (dft_exec_suffix fuel C (y::x::tail) s)
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `(y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
    !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v)` by
    metis_tac[dft_swap_operand_defined] >>
  reverse (Cases_on `step_inst fuel C x s`)
  >- (`dft_exec_suffix fuel C (x::y::tail) s = Error s''` by
        simp[dft_exec_suffix_cons, dft_exec_cons_def] >>
      simp[Once dft_res_rel_def] >>
      irule dft_nongas_suffix_swap_error >> metis_tac[])
  >- metis_tac[dft_swap_nonterminator_no_intret]
  >- (`?u. dft_exec_suffix fuel C (y::x::tail) s = Abort a u` by
        metis_tac[dft_nongas_suffix_first_abort] >>
      simp[dft_exec_suffix_cons, dft_exec_cons_def, dft_res_rel_def] >> metis_tac[])
  >- (`dft_exec_suffix fuel C (y::x::tail) s = Halt v` by
        metis_tac[dft_nongas_suffix_swap_halt] >>
      simp[dft_exec_suffix_cons, dft_exec_cons_def, dft_res_rel_def]) >>
  rename1 `step_inst fuel C x s = OK sx` >>
  reverse (Cases_on `step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx)`)
  >- (`dft_exec_suffix fuel C (x::y::tail) s = Error s''` by
        simp[dft_exec_suffix_cons, dft_exec_cons_def] >>
      simp[Once dft_res_rel_def] >>
      irule dft_nongas_suffix_swap_error >> metis_tac[])
  >- metis_tac[dft_swap_nonterminator_no_intret]
  >- (`?u. dft_exec_suffix fuel C (y::x::tail) s = Abort a u` by
        metis_tac[dft_nongas_suffix_second_abort] >>
      simp[dft_exec_suffix_cons, dft_exec_cons_def, dft_res_rel_def] >> metis_tac[])
  >- (`dft_exec_suffix fuel C (x::y::tail) s = Halt v /\
       dft_exec_suffix fuel C (y::x::tail) s = Halt v` by
        (irule dft_nongas_suffix_swap_halt >> simp[] >> metis_tac[]) >>
      simp[dft_exec_suffix_cons, dft_exec_cons_def, dft_res_rel_def]) >>
  `dft_exec_suffix fuel C (x::y::tail) s = dft_exec_suffix fuel C (y::x::tail) s` by
    (drule_all dft_nongas_pair_sym >> strip_tac >> metis_tac[dft_suffix_nongas_pair_ok]) >>
  pop_assum SUBST1_TAC >> Cases_on `dft_exec_suffix fuel C (y::x::tail) s` >>
  simp[dft_res_rel_def] >> metis_tac[]
QED

Theorem dft_gas_suffix_swap:
  dft_gas_swap_pair x y /\ gas_pair x.inst_opcode y.inst_opcode /\
  inst_wf x /\ inst_wf y ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    dft_res_rel (dft_exec_suffix fuel C (x::y::tail) s)
                (dft_exec_suffix fuel C (y::x::tail) s')
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   DISJOINT (set (inst_defs x)) (set (inst_uses y)) /\
   DISJOINT (set (inst_defs y)) (set (inst_uses x)) /\
   DISJOINT (set (inst_defs x)) (set (inst_defs y))` by
    gvs[dft_gas_swap_pair_def] >>
  Cases_on `?sy syx. step_inst fuel C y s' = OK sy /\
    step_inst fuel C x (sy with vs_inst_idx := SUC s'.vs_inst_idx) = OK syx`
  >- (qpat_x_assum `?sy syx. _` strip_assume_tac >>
      drule_all dft_suffix_gas_pair_ok >>
      disch_then (qspec_then `tail` strip_assume_tac) >>
      qexists_tac `s` >> simp[]) >>
  `!r. (!t. r <> OK t) ==> dft_res_rel r r` by simp[] >>
  Cases_on `y.inst_opcode = GAS`
  >- (`?sy. step_inst fuel C y s' = OK sy` by metis_tac[dft_gas_ok_shape] >>
      `x.inst_opcode = INVOKE` by
        (gvs[dftBlockSimTheory.gas_pair_def] >>
         metis_tac[dft_gas_ok_shape]) >>
      `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
      `!t. step_inst fuel C x (sy with vs_inst_idx := SUC s'.vs_inst_idx) <> OK t` by
        metis_tac[] >>
      qmatch_asmsub_abbrev_tac `!t. r <> OK t` >>
      `step_inst fuel C x (sy with vs_inst_idx := SUC s'.vs_inst_idx) = r` by
        simp[Abbr `r`] >>
      drule_all dft_gas_invoke_stopping_second >>
      disch_then (qspec_then `tail` strip_assume_tac) >>
      qexists_tac `s` >> simp[]) >>
  `x.inst_opcode = GAS /\ y.inst_opcode = INVOKE` by
    gvs[dftBlockSimTheory.gas_pair_def] >>
  `!t. step_inst fuel C y s' <> OK t` by metis_tac[dft_gas_ok_shape] >>
  qmatch_asmsub_abbrev_tac `!t. r <> OK t` >>
  `step_inst fuel C y s' = r` by simp[Abbr `r`] >>
  drule_all dft_gas_invoke_stopping_first >>
  disch_then (qspec_then `tail` strip_assume_tac) >>
  qexists_tac `s` >> simp[]
QED

Theorem dft_suffix_swap_variant:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\ ~s'.vs_call_ctx.cc_static /\
  (!v. MEM (Var v) y.inst_operands ==> v IN FDOM s'.vs_vars) /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
    !l. MEM (Label l) y.inst_operands ==> l IN FDOM s'.vs_labels) /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    dft_res_rel (dft_exec_suffix fuel C (x::y::tail) s)
                (dft_exec_suffix fuel C (y::x::tail) s')
Proof
  strip_tac >> Cases_on `gas_pair x.inst_opcode y.inst_opcode`
  >- (irule dft_gas_suffix_swap >> simp[]) >>
  qexists_tac `s'` >> simp[] >> irule dft_nongas_suffix_swap >> metis_tac[]
QED

Theorem dft_prefix_swap_variant:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\ ~s'.vs_call_ctx.cc_static /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (!t. FOLDR (dft_exec_cons fuel C) OK pre s' = OK t ==>
    (!v. MEM (Var v) y.inst_operands ==> v IN FDOM t.vs_vars) /\
    (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
      !l. MEM (Label l) y.inst_operands ==> l IN FDOM t.vs_labels)) ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    dft_res_rel (dft_exec_suffix fuel C (pre ++ x::y::tail) s)
                (dft_exec_suffix fuel C (pre ++ y::x::tail) s')
Proof
  strip_tac >> irule dft_suffix_prefix_variant >> simp[] >>
  rpt strip_tac >>
  `t.vs_call_ctx = s'.vs_call_ctx` by metis_tac[dft_prefix_call_ctx] >>
  irule dft_suffix_swap_variant >> fs[] >> metis_tac[]
QED

Theorem dft_remaining_inv_gas_variant:
  s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
  dft_remaining_inv fn bb todo s' ==> dft_remaining_inv fn bb todo s
Proof
  strip_tac >> qpat_x_assum `s' = _` SUBST_ALL_TAC >>
  gvs[dft_remaining_inv_def,
    sccpCorrectnessProofsTheory.strict_dom_vars_defined_def] >> metis_tac[]
QED

Theorem dft_remaining_inv_terminal:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  dft_remaining_inv fn bb (y::post) s /\ is_terminator y.inst_opcode ==>
  post = []
Proof
  strip_tac >> Cases_on `post` >> simp[] >>
  `MEM y bb.bb_instructions /\
   id_before (MAP (\i. i.inst_id) bb.bb_instructions) y.inst_id h.inst_id` by
    (gvs[dft_remaining_inv_def] >>
     first_x_assum irule >> simp[dft_id_before_cons]) >>
  metis_tac[dft_wf_order_nonterminator]
QED

Theorem dft_crossing_swap_pair:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
  ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode ==>
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects)
Proof
  strip_tac >>
  `DISJOINT (set (inst_defs y)) (set (inst_uses x))` by
    metis_tac[dft_reverse_dependency_disjoint] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `x <> y` by metis_tac[id_before_asym] >>
  `DISJOINT (set (inst_defs x)) (set (inst_defs y))` by
    metis_tac[ssa_disjoint_defs, wf_ssa_def] >>
  `~is_terminator x.inst_opcode` by metis_tac[dft_wf_order_nonterminator] >>
  gvs[dft_must_order_def, dft_gas_swap_pair_def,
      effects_independent_def, EVERY_MEM] >> metis_tac[pred_setTheory.DISJOINT_SYM]
QED

Theorem dft_extract_head_variant:
  !pre s'.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ y::post) s' /\ ~s'.vs_call_ctx.cc_static /\
  EVERY (\x. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode) pre ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
    dft_res_rel (dft_exec_suffix fuel C (pre ++ y::post) s)
                (dft_exec_suffix fuel C (y::(pre ++ post)) s')
Proof
  Induct >- (rpt strip_tac >> qexists_tac `s'` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `dft_gas_swap_pair h y /\ inst_wf h /\ inst_wf y /\
   ~(h.inst_outputs = [] /\ read_effects h.inst_opcode = empty_effects /\
     write_effects h.inst_opcode = empty_effects)` by
    (irule dft_crossing_swap_pair >> fs[] >> metis_tac[]) >>
  `(!v. MEM (Var v) y.inst_operands ==> v IN FDOM s'.vs_vars) /\
   (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
    !l. MEM (Label l) y.inst_operands ==> l IN FDOM s'.vs_labels)` by
    (irule dft_remaining_inv_ready >> qexistsl_tac [`bb`, `fn`, `post`, `h::pre`] >>
     simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all dft_suffix_swap_variant >>
  disch_then (qspecl_then [`pre ++ post`, `fuel`, `C`] strip_assume_tac) >>
  rename1 `s' = u with vs_gas_readings := s'.vs_gas_readings` >>
  `dft_remaining_inv fn bb ((h::pre) ++ y::post) u` by
    metis_tac[dft_remaining_inv_gas_variant] >>
  `~u.vs_call_ctx.cc_static` by metis_tac[dft_gas_variant_call_ctx] >>
  `?s. u = (s with vs_gas_readings := u.vs_gas_readings) /\
    dft_res_rel (dft_exec_suffix fuel C ([h] ++ (pre ++ y::post)) s)
                (dft_exec_suffix fuel C ([h] ++ (y::(pre ++ post))) u)` by
    (irule dft_suffix_prefix_variant >>
     `~is_terminator h.inst_opcode` by gvs[dft_gas_swap_pair_def] >>
     simp[] >> rpt gen_tac >>
     simp[dft_exec_cons_def] >> strip_tac >>
     gvs[AllCaseEqs()] >>
     rename1 `step_inst fuel C h u = OK t` >>
     `~t.vs_call_ctx.cc_static` by metis_tac[venomInstProofsTheory.step_preserves_call_ctx] >>
     `dft_remaining_inv fn bb (pre ++ y::post)
       (t with vs_inst_idx := SUC u.vs_inst_idx)` by
       (drule_at (Pat `step_inst _ _ _ _ = OK _`) dft_remaining_inv_step >>
        disch_then (qspecl_then [`[]`, `pre ++ y::post`] mp_tac) >> simp[]) >>
     qpat_x_assum `!s. dft_remaining_inv _ _ _ s /\ _ ==> _`
       (qspec_then `t with vs_inst_idx := SUC u.vs_inst_idx` mp_tac) >> simp[]) >>
  qexists_tac `s` >> conj_tac
  >- (qpat_x_assum `s' = _` SUBST_ALL_TAC >>
      qpat_x_assum `u = _` SUBST_ALL_TAC >> simp[]) >>
  gvs[] >> metis_tac[dft_res_rel_trans]
QED

Theorem dft_head_bubbles_variant:
  !todo scheduled.
  dft_head_bubbles
    (\x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
      ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
      id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
      ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled ==>
  !s'. wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
    dft_remaining_inv fn bb todo s' /\ ~s'.vs_call_ctx.cc_static ==>
    ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
      dft_res_rel (dft_exec_suffix fuel C todo s)
                  (dft_exec_suffix fuel C scheduled s')
Proof
  ho_match_mp_tac dft_head_bubbles_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `s'` >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `dft_exec_suffix fuel C (y::rest) s'` >>
  Cases_on `is_terminator y.inst_opcode`
  >- (`pre = []` by
        (Cases_on `pre` >> fs[dft_must_order_def]) >> gvs[] >>
      `post = []` by metis_tac[dft_remaining_inv_terminal] >> gvs[] >>
      qexists_tac `s'` >>
      simp[dft_exec_suffix_cons, dft_exec_cons_def]) >>
  `?u. s' = (u with vs_gas_readings := s'.vs_gas_readings) /\
    dft_res_rel (dft_exec_suffix fuel C ([y] ++ (pre ++ post)) u)
                (dft_exec_suffix fuel C ([y] ++ rest) s')` by
    (irule dft_suffix_prefix_variant >> simp[] >> rpt gen_tac >>
     simp[dft_exec_cons_def] >> strip_tac >> gvs[AllCaseEqs()] >>
     rename1 `step_inst fuel C y s' = OK t` >>
     `~t.vs_call_ctx.cc_static` by metis_tac[venomInstProofsTheory.step_preserves_call_ctx] >>
     `dft_remaining_inv fn bb (pre ++ post)
       (t with vs_inst_idx := SUC s'.vs_inst_idx)` by
       (drule_at (Pat `step_inst _ _ _ _ = OK _`) dft_remaining_inv_step >>
        disch_then (qspecl_then [`pre`, `post`] mp_tac) >> simp[]) >>
     qpat_x_assum `!s. _ ==> ?u. _`
       (qspec_then `t with vs_inst_idx := SUC s'.vs_inst_idx` mp_tac) >> simp[]) >>
  `dft_remaining_inv fn bb (pre ++ y::post) u` by
    metis_tac[dft_remaining_inv_gas_variant] >>
  `~u.vs_call_ctx.cc_static` by metis_tac[dft_gas_variant_call_ctx] >>
  drule_all dft_extract_head_variant >>
  disch_then (qspecl_then [`fuel`, `C`] strip_assume_tac) >>
  qexists_tac `s` >> conj_tac
  >- (qpat_x_assum `s' = _` SUBST_ALL_TAC >>
      qpat_x_assum `u = _` SUBST_ALL_TAC >> simp[]) >>
  gvs[] >> metis_tac[dft_res_rel_trans]
QED

Theorem dft_eval_phis_gas_OK[local]:
  eval_phis s pre = OK u ==>
  u.vs_gas_readings = s.vs_gas_readings /\
  !gs. eval_phis (s with vs_gas_readings := gs) pre =
       OK (u with vs_gas_readings := gs)
Proof
  strip_tac >> qspecl_then [`pre`, `s`] mp_tac gas_eval_phis >>
  simp[gas_replay_at_def, lift_result_def] >> strip_tac >>
  conj_tac
  >- (first_x_assum (qspec_then `[]` mp_tac) >>
      Cases_on `eval_phis (s with vs_gas_readings := []) pre` >> simp[lift_result_def]) >>
  gen_tac >> first_x_assum (qspec_then `gs` mp_tac) >>
  Cases_on `eval_phis (s with vs_gas_readings := gs) pre` >> simp[lift_result_def]
QED

Theorem dft_pseudo_partition[local]:
  !xs. (!i j. i < j /\ j < LENGTH xs /\ is_pseudo (EL j xs).inst_opcode ==>
    is_pseudo (EL i xs).inst_opcode) ==>
  xs = FILTER (\i. is_pseudo i.inst_opcode) xs ++
       FILTER (\i. ~is_pseudo i.inst_opcode) xs
Proof
  Induct >- simp[] >> rpt strip_tac >>
  Cases_on `is_pseudo h.inst_opcode` >> simp[]
  >- (first_x_assum irule >> rpt strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  `FILTER (\i. is_pseudo i.inst_opcode) xs = []` by
    simp[FILTER_EQ_NIL] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs` by
    simp[FILTER_EQ_ID] >> simp[]
QED

Theorem dft_run_block_gas:
  !fn bb bb' s' fuel C.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  dft_block_rel bb bb' /\ pseudos_prefix bb /\
  bb.bb_label = s'.vs_current_bb /\ strict_dom_vars_defined fn s' /\
  ~s'.vs_call_ctx.cc_static /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
       i.inst_opcode <> CODECOPY /\
     MEM (Label l) i.inst_operands ==> l IN FDOM s'.vs_labels) /\
  (!x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~dft_abort_compatible x.inst_opcode y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id) ==>
  ?s. s' = (s with vs_gas_readings := s'.vs_gas_readings) /\
      dft_res_rel (run_block fuel C bb s) (run_block fuel C bb' s')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_block_head_bubbles >> strip_tac >>
  rename1 `bb'.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ scheduled_body` >>
  `bb.bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
    FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions` by
    (irule dft_pseudo_partition >> metis_tac[pseudos_prefix_def]) >>
  qmatch_asmsub_abbrev_tac `bb'.bb_instructions = pre ++ scheduled_body` >>
  qabbrev_tac `xs = FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions` >>
  `EVERY (from_block bb.bb_instructions) scheduled_body` by
    fs[dft_block_rel_def] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) scheduled_body` by
    (fs[EVERY_MEM, from_block_def] >> metis_tac[flip_operands_is_pseudo]) >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
    simp[Abbr `xs`, EVERY_MEM, MEM_FILTER] >>
  `EVERY (\i. MEM i bb.bb_instructions) norm` by
    (qpat_x_assum `PERM _ norm` (mp_tac o MATCH_MP PERM_MEM_EQ) >>
     simp[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  `!t. dft_exec_suffix fuel C norm t = dft_exec_suffix fuel C scheduled_body t` by
    (gen_tac >> irule dft_normalized_suffix_eq >> metis_tac[]) >>
  `!s. run_block fuel C bb s =
    case eval_phis s pre of
      OK u => dft_exec_suffix fuel C
        (DROP (phi_prefix_length pre) pre ++ xs)
        (u with vs_inst_idx := phi_prefix_length pre)
    | Error e => Error e` by
    (gen_tac >> drule_all dft_run_block_prefix >>
     disch_then (qspecl_then [`fuel`, `C`, `s`] mp_tac) >>
     simp[dft_exec_suffix_append]) >>
  `run_block fuel C bb' s' =
    case eval_phis s' pre of
      OK u => dft_exec_suffix fuel C
        (DROP (phi_prefix_length pre) pre ++ scheduled_body)
        (u with vs_inst_idx := phi_prefix_length pre)
    | Error e => Error e` by
    (simp[dft_exec_suffix_append] >> irule dft_run_block_prefix >> simp[]) >>
  qspecl_then [`s'`, `pre`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s' pre = OK u` >>
      drule dft_eval_phis_gas_OK >> strip_tac >>
      `?v. (u with vs_inst_idx := phi_prefix_length pre) =
             (v with vs_gas_readings :=
               (u with vs_inst_idx := phi_prefix_length pre).vs_gas_readings) /\
        dft_res_rel
          (dft_exec_suffix fuel C (DROP (phi_prefix_length pre) pre ++ xs) v)
          (dft_exec_suffix fuel C (DROP (phi_prefix_length pre) pre ++ norm)
            (u with vs_inst_idx := phi_prefix_length pre))` by
        (`EVERY (\i. ~is_terminator i.inst_opcode)
            (DROP (phi_prefix_length pre) pre)` by
           (irule EVERY_DROP >> simp[Abbr `pre`, EVERY_MEM, MEM_FILTER] >>
            rpt strip_tac >> Cases_on `i.inst_opcode` >>
            gvs[is_pseudo_def, is_terminator_def]) >>
         irule dft_suffix_prefix_variant >> reverse conj_tac >- simp[] >>
         rpt strip_tac >>
         `~t.vs_call_ctx.cc_static` by
           (drule_all dft_prefix_call_ctx >> drule dft_eval_phis_call_ctx >>
            simp[]) >>
         `dft_remaining_inv fn bb xs t` by
           (simp[Abbr `xs`] >> irule dft_remaining_inv_initialized >>
            conj_tac >- simp[] >> conj_tac >- simp[] >>
            qexistsl_tac [`C`, `fuel`, `s'`, `u`] >>
            fs[Abbr `pre`] >> first_assum MATCH_ACCEPT_TAC) >>
         drule dft_head_bubbles_variant >>
         disch_then (qspecl_then [`fuel`, `fn`, `C`, `t`] mp_tac) >> simp[]) >>
      `((u with vs_inst_idx := phi_prefix_length pre) with
         vs_gas_readings := v.vs_gas_readings) = v` by
        (qpat_assum `(u with vs_inst_idx := _) = _`
           (pure_once_rewrite_tac o single) >> simp[]) >>
      `u with <|vs_inst_idx := phi_prefix_length pre;
                  vs_gas_readings := v.vs_gas_readings|> = v` by
        (qpat_x_assum `_ = v` (SUBST1_TAC o SYM) >>
         simp[venom_state_component_equality]) >>
      `dft_exec_suffix fuel C norm = dft_exec_suffix fuel C scheduled_body` by
        simp[FUN_EQ_THM] >>
      qexists_tac `s' with vs_gas_readings := v.vs_gas_readings` >>
      simp[] >>
      qpat_x_assum `dft_res_rel _ _` mp_tac >>
      simp[dft_exec_suffix_append]) >>
  qexists_tac `s'` >> simp[]

QED
