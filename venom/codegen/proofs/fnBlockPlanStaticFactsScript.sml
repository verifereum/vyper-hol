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
