(* Small interfaces for block-prefix static reasoning. *)
Theory fnBlockPlanStaticFacts
Ancestors
  fnPlanPrefix stackPlanGen stackPlanOps stackPlanTypes

(* A unique available PHI source, once known to be on the join stack,
   excludes every PHI source from the spill map. *)
Theorem phi_unique_source_not_spilled:
  generated_plan_state_wf_marked spill_base ps /\
  (?!v. MEM (Var v) phi.inst_operands /\
         (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)) /\
  (?v. MEM (Var v) phi.inst_operands /\ MEM (Var v) ps.ps_stack) ==>
  !v. MEM (Var v) phi.inst_operands ==> Var v NOTIN FDOM ps.ps_spilled
Proof
  rw[EXISTS_UNIQUE_THM, generated_plan_state_wf_marked_def] >>
  fs[pred_setTheory.IN_DISJOINT] >> metis_tac[]
QED

(* Without a path-local promise, cleanup on a non-must-halt path really
   removes its dead variables.  A RET consumer must establish the promise
   hypothesis as well as exclusion from must_halt_labels. *)
Theorem clean_stack_plan_non_halting_path:
  ~ps.ps_cleanup_promised /\
  ~MEM bb.bb_label (must_halt_labels cfg fn) /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb ==>
  clean_stack_plan liveness cfg fn bb ps =
  popmany_plan
    (MAP Var (FILTER (\v. ~MEM v
      (input_vars_from pred bb.bb_instructions
        (live_vars_at liveness bb.bb_label 0)))
      (live_vars_at liveness pred (LENGTH pred_bb.bb_instructions)))) ps
Proof
  strip_tac >>
  simp[clean_stack_plan_def, cleanup_elision_safe_def,
       cleanup_height_safe_def]
QED

Theorem popmany_individual_fold_empty[local]:
  !xs acc ps.
    FST (FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
          let (swap_ops, ps') =
            if dist = 0 then ([], ps) else do_swap dist ps in
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
      (acc, ps) xs) = [] ==>
    acc = [] /\
    SND (FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
          let (swap_ops, ps') =
            if dist = 0 then ([], ps) else do_swap dist ps in
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
      (acc, ps) xs) = ps /\
    EVERY (\op. stack_get_depth op ps.ps_stack = NONE) xs
Proof
  Induct >- simp[] >> pop_assum (mk_asm "ih") >> rpt gen_tac >>
  simp_tac bool_ss [listTheory.FOLDL, listTheory.EVERY_DEF] >>
  Cases_on `stack_get_depth h ps.ps_stack` >>
  asm_simp_tac std_ss [LET_THM, pairTheory.UNCURRY_DEF]
  >- (strip_tac >> asm "ih" (drule o SIMP_RULE std_ss [LET_THM, pairTheory.UNCURRY_DEF]) >> simp[]) >>
  rename1 `SOME dist` >>
  Cases_on `dist = 0` >> asm_simp_tac std_ss [LET_THM, pairTheory.UNCURRY_DEF]
  >- (strip_tac >> asm "ih" (drule o SIMP_RULE std_ss [LET_THM, pairTheory.UNCURRY_DEF]) >> simp[]) >>
  Cases_on `do_swap dist ps` >> asm_simp_tac std_ss [LET_THM, pairTheory.UNCURRY_DEF] >>
  strip_tac >> asm "ih" (drule o SIMP_RULE std_ss [LET_THM, pairTheory.UNCURRY_DEF]) >> simp[]
QED

Theorem popmany_individual_empty:
  FST (popmany_individual xs ps) = [] ==>
  SND (popmany_individual xs ps) = ps /\
  !op. MEM op xs ==> stack_get_depth op ps.ps_stack = NONE
Proof
  simp_tac std_ss [popmany_individual_def, LET_THM,
                    pairTheory.UNCURRY_DEF] >>
  strip_tac >>
  drule (SIMP_RULE std_ss [LET_THM, pairTheory.UNCURRY_DEF]
    popmany_individual_fold_empty) >>
  simp_tac std_ss [listTheory.EVERY_MEM] >>
  strip_tac >>
  qpat_x_assum `FST _ = []` kall_tac >>
  qpat_x_assum `SND _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `QSORT cmp xs` >>
  metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]
QED

Theorem popmany_plan_empty:
  FST (popmany_plan xs ps) = [] ==>
  SND (popmany_plan xs ps) = ps /\
  !op. MEM op xs ==> stack_get_depth op ps.ps_stack = NONE
Proof
  Cases_on `xs` >- simp[popmany_plan_def] >>
  simp_tac std_ss [popmany_plan_def, LET_THM] >>
  Cases_on `EVERY IS_SOME
    (MAP (\v. stack_get_depth v ps.ps_stack) (h::t))` >>
  asm_simp_tac std_ss []
  >- (Cases_on `is_contiguous_top
        (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) (h::t)))` >>
      asm_simp_tac std_ss []
      >- (Cases_on `do_swap (LENGTH (h::t)) ps` >> simp[]) >>
      metis_tac[popmany_individual_empty]) >>
  metis_tac[popmany_individual_empty]
QED

Theorem stack_find_none_absent[local]:
  !xs p. stack_find p xs = NONE ==> !op. MEM op xs ==> ~p op
Proof
  Induct >> simp[stackModelTheory.stack_find_def] >> rpt gen_tac >>
  Cases_on `p h` >> simp[] >>
  Cases_on `stack_find p xs` >> simp[] >> metis_tac[]
QED

Theorem popmany_plan_empty_not_mem:
  FST (popmany_plan xs ps) = [] ==>
  !op. MEM op xs ==> ~MEM op ps.ps_stack
Proof
  strip_tac >> drule popmany_plan_empty >> strip_tac >>
  rpt strip_tac >> first_x_assum drule >>
  simp_tac std_ss [stackModelTheory.stack_get_depth_def] >>
  disch_then (mp_tac o MATCH_MP stack_find_none_absent) >>
  simp[listTheory.MEM_REVERSE]
QED

Theorem popmany_individual_fold_absent[local]:
  !xs acc ps.
    EVERY (\op. stack_get_depth op ps.ps_stack = NONE) xs ==>
    FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
          let (swap_ops, ps') =
            if dist = 0 then ([], ps) else do_swap dist ps in
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
      (acc, ps) xs = (acc, ps)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp_tac std_ss [listTheory.EVERY_DEF, listTheory.FOLDL] >>
  strip_tac >> asm_simp_tac std_ss [LET_THM, pairTheory.UNCURRY_DEF] >>
  first_x_assum (irule o SIMP_RULE std_ss [LET_THM, pairTheory.UNCURRY_DEF]) >>
  first_assum ACCEPT_TAC
QED

Theorem popmany_individual_absent:
  EVERY (\op. stack_get_depth op ps.ps_stack = NONE) xs ==>
  popmany_individual xs ps = ([], ps)
Proof
  strip_tac >>
  simp_tac std_ss [popmany_individual_def, LET_THM, pairTheory.UNCURRY_DEF] >>
  irule (SIMP_RULE std_ss [LET_THM, pairTheory.UNCURRY_DEF]
    popmany_individual_fold_absent) >>
  fs[listTheory.EVERY_MEM] >>
  metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]
QED

Theorem popmany_plan_absent:
  EVERY (\op. stack_get_depth op ps.ps_stack = NONE) xs ==>
  popmany_plan xs ps = ([], ps)
Proof
  Cases_on `xs` >- simp[popmany_plan_def] >>
  simp_tac std_ss [listTheory.EVERY_DEF] >> strip_tac >>
  simp[popmany_plan_def, popmany_individual_absent,
       listTheory.EVERY_DEF]
QED

Theorem clean_stack_plan_silent_inputs:
  ~ps.ps_cleanup_promised /\
  ~MEM bb.bb_label (must_halt_labels cfg fn) /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  EVERY (\op. MEM op (MAP Var (live_vars_at liveness pred
    (LENGTH pred_bb.bb_instructions)))) ps.ps_stack /\
  FST (clean_stack_plan liveness cfg fn bb ps) = [] ==>
  EVERY (\op. MEM op (MAP Var (input_vars_from pred bb.bb_instructions
    (live_vars_at liveness bb.bb_label 0)))) ps.ps_stack
Proof
  strip_tac >> drule_all clean_stack_plan_non_halting_path >>
  disch_then (fn th => fs[th]) >>
  drule popmany_plan_empty_not_mem >>
  fs[listTheory.EVERY_MEM, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

Theorem clean_stack_plan_inputs_only[local]:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  EVERY (\op. MEM op (MAP Var (input_vars_from pred bb.bb_instructions
    (live_vars_at liveness bb.bb_label 0)))) ps.ps_stack ==>
  ((SND (clean_stack_plan liveness cfg fn bb ps)).ps_stack,
   (SND (clean_stack_plan liveness cfg fn bb ps)).ps_spilled) =
  (ps.ps_stack, ps.ps_spilled)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `MAP Var inputs` >>
  `!v. ~MEM v inputs ==> stack_get_depth (Var v) ps.ps_stack = NONE` by
    (rpt strip_tac >> Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[] >>
     drule stackModelTheory.stack_get_depth_props >> strip_tac >>
     drule reorderSimTheory.stack_peek_mem >>
     fs[listTheory.EVERY_MEM, listTheory.MEM_MAP] >> strip_tac >>
     qpat_x_assum `!op. MEM op ps.ps_stack ==> _` drule >> simp[]) >>
  `!layout. popmany_plan (MAP Var (FILTER (\v. ~MEM v inputs) layout)) ps =
      ([], ps)` by
    (gen_tac >> irule popmany_plan_absent >>
     simp[listTheory.EVERY_MEM, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
     metis_tac[]) >>
  `!layout. FILTER (\op. IS_SOME (stack_get_depth op ps.ps_stack))
      (MAP Var (FILTER (\v. ~MEM v inputs) layout)) = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM,
          listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
     metis_tac[]) >>
  Cases_on `inputs = []`
  >- (fs[Abbr `inputs`] >>
      simp[clean_stack_plan_def, popmany_plan_def] >>
      IF_CASES_TAC >> simp[]) >>
  fs[Abbr `inputs`] >>
  simp[clean_stack_plan_def, mark_dead_stack_def, popmany_plan_def,
       listTheory.NULL_EQ]
QED

Theorem clean_stack_plan_silent_replay_stack:
  ~ps.ps_cleanup_promised /\
  ~MEM bb.bb_label (must_halt_labels cfg fn) /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  EVERY (\op. MEM op (MAP Var (live_vars_at liveness pred
    (LENGTH pred_bb.bb_instructions)))) ps.ps_stack /\
  FST (clean_stack_plan liveness cfg fn bb ps) = [] ==>
  (SND (clean_stack_plan liveness cfg fn bb
    (ps with <| ps_cleanup_height := h;
                ps_cleanup_promised := promised |>))).ps_stack = ps.ps_stack
Proof
  strip_tac >> drule_all clean_stack_plan_silent_inputs >> strip_tac >>
  qspec_then `ps with <| ps_cleanup_height := h;
    ps_cleanup_promised := promised |>` mp_tac
    (GEN_ALL clean_stack_plan_inputs_only) >>
  simp[]
QED

Theorem clean_stack_plan_silent_replay_spilled:
  ~ps.ps_cleanup_promised /\
  ~MEM bb.bb_label (must_halt_labels cfg fn) /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  EVERY (\op. MEM op (MAP Var (live_vars_at liveness pred
    (LENGTH pred_bb.bb_instructions)))) ps.ps_stack /\
  FST (clean_stack_plan liveness cfg fn bb ps) = [] ==>
  (SND (clean_stack_plan liveness cfg fn bb
    (ps with <| ps_cleanup_height := h;
                ps_cleanup_promised := promised |>))).ps_spilled = ps.ps_spilled
Proof
  strip_tac >> drule_all clean_stack_plan_silent_inputs >> strip_tac >>
  qspec_then `ps with <| ps_cleanup_height := h;
    ps_cleanup_promised := promised |>` mp_tac
    (GEN_ALL clean_stack_plan_inputs_only) >>
  simp[]
QED
