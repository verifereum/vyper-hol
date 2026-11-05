Theory fnBlockPlanStaticInventory
Ancestors
  stackModel stackPlanOps planWf doSwapSim reorderSim sorting list rich_list pred_set
  fnFrameStepsRevertForward stackPlanGen livenessDefs cfgDefs venomInst
  fnBlockPlanStaticRetRegion

Theorem inventory_do_swap_promised:
  !d ps. (SND (do_swap d ps)).ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[do_swap_def, LET_THM] >> rpt IF_CASES_TAC >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem inventory_pop_fold_promised[local]:
  !items ops ps.
  (SND (FOLDL (\(ops,ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops,ps)
    | SOME dist =>
        let (swap_ops,ps') =
          if dist = 0 then ([],ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack))
    (ops,ps) items)).ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  Induct >> simp[LET_THM] >> rpt gen_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [LET_THM]) >>
  Cases_on `stack_get_depth h ps.ps_stack` >> simp[] >>
  rename1 `stack_get_depth h ps.ps_stack = SOME dist` >>
  Cases_on `dist = 0` >> simp[] >>
  Cases_on `do_swap dist ps` >> simp[] >>
  qspecl_then [`dist`, `ps`] mp_tac inventory_do_swap_promised >> simp[]
QED

Theorem inventory_popmany_promised:
  (SND (popmany_plan items ps)).ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  Cases_on `items` >> simp[popmany_plan_def] >>
  rpt IF_CASES_TAC >>
  simp[popmany_individual_def, LET_THM,
       SRULE [LET_THM] inventory_pop_fold_promised] >>
  pairarg_tac >> simp[] >>
  qspec_then `SUC (LENGTH t)` (qspec_then `ps` mp_tac)
    inventory_do_swap_promised >> simp[]
QED

Theorem inventory_swap_top[local]:
  d < LENGTH stk ==> stack_peek 0 (stack_swap d stk) = stack_peek d stk
Proof
  strip_tac >> simp[stack_peek_def, stack_swap_def, EL_LUPDATE] >>
  Cases_on `d = 0` >> simp[] >>
  `LENGTH stk - 1 <> LENGTH stk - 1 - d` by decide_tac >> simp[]
QED

Theorem inventory_pop_top[local]:
  ALL_DISTINCT stk /\ stk <> [] /\ stack_peek 0 stk = v ==>
  ALL_DISTINCT (stack_pop 1 stk) /\
  (!op. MEM op (stack_pop 1 stk) <=> MEM op stk /\ op <> v)
Proof
  Cases_on `stk` using SNOC_CASES >>
  simp[stack_peek_def, stack_pop_def, ALL_DISTINCT_SNOC, TAKE_SNOC,
       EL_LENGTH_SNOC, MEM_SNOC] >> metis_tac[]
QED

Theorem inventory_swap_pop[local]:
  ALL_DISTINCT ps.ps_stack /\ stack_get_depth v ps.ps_stack = SOME d ==>
  ALL_DISTINCT (stack_pop 1 (SND (do_swap d ps)).ps_stack) /\
  (!op. MEM op (stack_pop 1 (SND (do_swap d ps)).ps_stack) <=>
        MEM op ps.ps_stack /\ op <> v)
Proof
  strip_tac >> drule stack_get_depth_props >> strip_tac >>
  drule_all do_swap_stack_permutation >> strip_tac >>
  `stack_peek 0 (SND (do_swap d ps)).ps_stack = v` by
    (simp[do_swap_stack_result] >> metis_tac[inventory_swap_top]) >>
  `(SND (do_swap d ps)).ps_stack <> []` by
    (mp_tac (Q.SPECL [`d`, `ps`] do_swap_length) >>
     simp[] >> metis_tac[LENGTH_NIL, prim_recTheory.NOT_LESS_0]) >>
  drule_all inventory_pop_top >> simp[EXTENSION]
QED

Theorem inventory_depth_none[local]:
  stack_get_depth v stk = NONE <=> ~MEM v stk
Proof
  simp[stack_get_depth_NONE, stack_peek_def, MEM_EL] >>
  eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `LENGTH stk - 1 - n` mp_tac) >>
      `LENGTH stk - 1 - (LENGTH stk - 1 - n) = n /\
       LENGTH stk - 1 - n < LENGTH stk` by decide_tac >> simp[]) >>
  qpat_x_assum `!n. _` (qspec_then `LENGTH stk - (d + 1)` mp_tac) >>
  simp[]
QED

Theorem inventory_pop_fold[local]:
  !items ops ps. ALL_DISTINCT ps.ps_stack ==>
    let qs = SND (FOLDL (\(ops,ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops,ps)
      | SOME dist =>
          let (swap_ops,ps') =
            if dist = 0 then ([],ps) else do_swap dist ps in
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
      (ops,ps) items) in
    ALL_DISTINCT qs.ps_stack /\
    (!op. MEM op qs.ps_stack <=> MEM op ps.ps_stack /\ ~MEM op items)
Proof
  Induct >> simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [LET_THM]) >>
  Cases_on `stack_get_depth h ps.ps_stack`
  >- (simp[] >> first_x_assum drule >>
      gvs[inventory_depth_none] >> metis_tac[]) >>
  rename1 `stack_get_depth h ps.ps_stack = SOME dist` >>
  drule_all inventory_swap_pop >> strip_tac >>
  Cases_on `dist = 0`
  >- (gvs[do_swap_def] >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  Cases_on `do_swap dist ps` >>
  rename1 `do_swap dist ps = (swap_ops, next)` >> gvs[] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem inventory_popmany_individual:
  ALL_DISTINCT ps.ps_stack ==>
  ALL_DISTINCT (SND (popmany_individual items ps)).ps_stack /\
  (!op. MEM op (SND (popmany_individual items ps)).ps_stack <=>
        MEM op ps.ps_stack /\ ~MEM op items)
Proof
  strip_tac >> simp[popmany_individual_def, LET_THM] >>
  drule inventory_pop_fold >>
  disch_then (qspec_then `QSORT (\a b.
    case (stack_get_depth a ps.ps_stack, stack_get_depth b ps.ps_stack) of
      (SOME da,SOME db) => da <= db | _ => T) items` mp_tac) >>
  simp[LET_THM] >>
  metis_tac[QSORT_PERM, PERM_MEM_EQ]
QED

Theorem inventory_swap_ends[local]:
  !stem mid a b.
  stack_swap (LENGTH mid + 1) (stem ++ [a] ++ mid ++ [b]) =
    stem ++ [b] ++ mid ++ [a]
Proof
  rpt gen_tac >>
  simp[stack_swap_def, LET_THM, EL_APPEND_EQN, LUPDATE_APPEND2,
       LUPDATE_APPEND1, APPEND_ASSOC, LUPDATE_def]
QED

Theorem inventory_bulk_result[local]:
  stack_pop (LENGTH mid + 1)
    (stack_swap (LENGTH mid + 1) (stem ++ [a] ++ mid ++ [b])) =
  stem ++ [b]
Proof
  simp[inventory_swap_ends, stack_pop_def, TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

Theorem inventory_bulk_inventory[local]:
  ALL_DISTINCT (stem ++ [a] ++ mid ++ [b]) ==>
  ALL_DISTINCT (stack_pop (LENGTH mid + 1)
    (stack_swap (LENGTH mid + 1) (stem ++ [a] ++ mid ++ [b]))) /\
  (!op. MEM op (stack_pop (LENGTH mid + 1)
    (stack_swap (LENGTH mid + 1) (stem ++ [a] ++ mid ++ [b]))) <=>
    MEM op (stem ++ [a] ++ mid ++ [b]) /\ ~MEM op (a::mid))
Proof
  simp[inventory_bulk_result, ALL_DISTINCT_APPEND, MEM_APPEND] >>
  metis_tac[]
QED

Theorem inventory_bulk_split[local]:
  !n stk. 0 < n /\ n < LENGTH stk ==>
  ?stem a mid b. stk = stem ++ [a] ++ mid ++ [b] /\ n = LENGTH mid + 1
Proof
  rpt gen_tac >> strip_tac >>
  `?front b. stk = SNOC b front` by
    (Cases_on `stk` using SNOC_CASES >> gvs[] >> metis_tac[]) >>
  gvs[] >>
  qexists `TAKE (LENGTH front - n) front` >>
  `LENGTH (DROP (LENGTH front - n) front) = n` by simp[LENGTH_DROP] >>
  Cases_on `DROP (LENGTH front - n) front` >- gvs[] >>
  rename1 `DROP (LENGTH front - n) front = a::mid` >>
  qexistsl [`a`, `mid`] >>
  `n = LENGTH mid + 1` by gvs[arithmeticTheory.ADD1] >> simp[] >>
  mp_tac (Q.SPECL [`LENGTH front - n`, `front`] TAKE_DROP) >>
  pure_asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[]
QED

Theorem inventory_contiguous_depths[local]:
  EVERY IS_SOME (MAP (\v. stack_get_depth v stk) items) /\
  is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v stk) items)) ==>
  LENGTH items <= 16 /\
  (!d. MEM d (MAP THE (MAP (\v. stack_get_depth v stk) items)) <=>
       0 < d /\ d <= LENGTH items)
Proof
  simp[is_contiguous_top_def, LET_THM] >> strip_tac >> simp[] >>
  `!d. MEM d (MAP THE (MAP (\v. stack_get_depth v stk) items)) <=>
       MEM d (GENLIST SUC (LENGTH items))` by
    metis_tac[QSORT_PERM, PERM_MEM_EQ] >>
  simp[MEM_GENLIST] >> gen_tac >> eq_tac >> rpt strip_tac
  >- simp[]
  >- simp[] >>
  qexists `d - 1` >> simp[]
QED

Theorem inventory_depth_image[local]:
  EVERY IS_SOME (MAP (\v. stack_get_depth v stk) items) ==>
  (MEM op items <=>
   ?d. MEM d (MAP THE (MAP (\v. stack_get_depth v stk) items)) /\
       stack_peek d stk = op)
Proof
  simp[EVERY_MAP, EVERY_MEM, MEM_MAP] >> strip_tac >> eq_tac
  >- (strip_tac >> `IS_SOME (stack_get_depth op stk)` by metis_tac[] >>
      Cases_on `stack_get_depth op stk` >> gvs[] >>
      rename1 `stack_get_depth op stk = SOME d` >>
      qexists `d` >> conj_tac
      >- (qexists `SOME d` >> simp[] >> metis_tac[]) >>
      metis_tac[stack_get_depth_props]) >>
  strip_tac >> rename1 `MEM v items` >>
  `IS_SOME (stack_get_depth v stk)` by metis_tac[] >>
  Cases_on `stack_get_depth v stk` >> gvs[] >>
  metis_tac[stack_get_depth_props]
QED

Theorem inventory_contiguous_bound[local]:
  items <> [] /\
  EVERY IS_SOME (MAP (\v. stack_get_depth v stk) items) /\
  is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v stk) items)) ==>
  LENGTH items < LENGTH stk
Proof
  strip_tac >> `0 < LENGTH items` by (Cases_on `items` >> gvs[]) >>
  drule_all inventory_contiguous_depths >> strip_tac >>
  `MEM (LENGTH items) (MAP THE (MAP (\v. stack_get_depth v stk) items))` by
    (first_x_assum (qspec_then `LENGTH items` mp_tac) >> simp[]) >>
  qpat_x_assum `!d. _` kall_tac >>
  gvs[MEM_MAP] >> rename1 `MEM v items` >>
  `IS_SOME (stack_get_depth v stk)` by
    (gvs[EVERY_MAP, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `stack_get_depth v stk` >> gvs[] >>
  metis_tac[stack_get_depth_props]
QED

Theorem inventory_suffix_depths[local]:
  !stem xs b op. (?d. 0 < d /\ d <= LENGTH xs /\
       stack_peek d (stem ++ xs ++ [b]) = op) <=> MEM op xs
Proof
  rpt gen_tac >> simp[stack_peek_def, MEM_EL] >> eq_tac >> rpt strip_tac
  >- (`LENGTH stem <= LENGTH stem + LENGTH xs + 1 - (d + 1) /\
        LENGTH stem + LENGTH xs + 1 - (d + 1) < LENGTH stem + LENGTH xs` by
        decide_tac >>
      qexists `LENGTH xs - d` >> simp[] >>
      gvs[EL_APPEND_EQN] >>
      `LENGTH stem + LENGTH xs + 1 - (d + 1) - LENGTH stem =
       LENGTH xs - d` by decide_tac >> metis_tac[]) >>
  qexists `LENGTH xs - n` >> simp[] >>
  `LENGTH stem + LENGTH xs + 1 - (LENGTH xs - n + 1) =
   LENGTH stem + n` by decide_tac >>
  simp[EL_APPEND_EQN]
QED

Theorem inventory_contiguous_delete[local]:
  !stk items. ALL_DISTINCT stk /\ items <> [] /\
  EVERY IS_SOME (MAP (\v. stack_get_depth v stk) items) /\
  is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v stk) items)) ==>
  ALL_DISTINCT (stack_pop (LENGTH items) (stack_swap (LENGTH items) stk)) /\
  (!op. MEM op (stack_pop (LENGTH items) (stack_swap (LENGTH items) stk)) <=>
    MEM op stk /\ ~MEM op items)
Proof
  rpt gen_tac >> strip_tac >> drule_all inventory_contiguous_bound >> strip_tac >>
  `0 < LENGTH items` by (Cases_on `items` >> gvs[]) >>
  qspecl_then [`LENGTH items`, `stk`] mp_tac inventory_bulk_split >>
  simp[] >> strip_tac >>
  drule_all inventory_contiguous_depths >> strip_tac >>
  `!op. MEM op items <=> MEM op (a::mid)` by
    (gen_tac >> drule inventory_depth_image >>
     disch_then (qspec_then `op` mp_tac) >>
     simp[] >>
     qspecl_then [`stem`, `a::mid`, `b`, `op`] mp_tac inventory_suffix_depths >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[arithmeticTheory.ADD1] >> metis_tac[]) >>
  gvs[] >> drule inventory_bulk_inventory >> simp[]
QED

Theorem inventory_popmany:
  ALL_DISTINCT ps.ps_stack ==>
  ALL_DISTINCT (SND (popmany_plan items ps)).ps_stack /\
  (!op. MEM op (SND (popmany_plan items ps)).ps_stack <=>
        MEM op ps.ps_stack /\ ~MEM op items)
Proof
  strip_tac >> Cases_on `items` >- simp[popmany_plan_def] >>
  simp[popmany_plan_def, LET_THM] >>
  IF_CASES_TAC >- (
    IF_CASES_TAC
    >- (qspecl_then [`ps.ps_stack`, `h::t`] mp_tac inventory_contiguous_delete >>
        simp[] >> strip_tac >>
        `LENGTH (h::t) < LENGTH ps.ps_stack` by
          (irule inventory_contiguous_bound >> simp[] >> metis_tac[]) >>
        pairarg_tac >> gvs[] >>
        qspecl_then [`SUC (LENGTH t)`, `ps`] mp_tac do_swap_stack_result >>
        simp[] >> metis_tac[]) >>
    drule inventory_popmany_individual >>
    disch_then (qspec_then `h::t` mp_tac) >> simp[]) >>
  drule inventory_popmany_individual >>
  disch_then (qspec_then `h::t` mp_tac) >> simp[]
QED

Theorem inventory_popmany_distinct:
  ALL_DISTINCT ps.ps_stack /\ popmany_plan items ps = (ops, qs) ==>
  ALL_DISTINCT qs.ps_stack
Proof
  strip_tac >> drule inventory_popmany >>
  disch_then (qspec_then `items` mp_tac) >> simp[]
QED

Theorem inventory_popmany_mem:
  ALL_DISTINCT ps.ps_stack /\ popmany_plan items ps = (ops, qs) ==>
  (MEM op qs.ps_stack <=> MEM op ps.ps_stack /\ ~MEM op items)
Proof
  strip_tac >> drule inventory_popmany >>
  disch_then (qspec_then `items` mp_tac) >> simp[]
QED

(* Spill preservation is the existing exported rf_popmany_spilled. *)

Theorem inventory_cleanup_branch:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\
  (!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb n) ==>
  clean_stack_plan lv cfg fn bb ps =
  popmany_plan (MAP Var (FILTER (\v. ~MEM v
    (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
    (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)))) ps
Proof
  strip_tac >> simp[clean_stack_plan_def, LET_THM]
QED

Theorem inventory_cleanup_mem:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\
  (!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb n) /\
  ALL_DISTINCT ps.ps_stack /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions))) ps.ps_stack /\
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  (MEM (Var v) qs.ps_stack <=> MEM (Var v) ps.ps_stack /\
    MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
Proof
  strip_tac >> drule_all inventory_cleanup_branch >> strip_tac >>
  `popmany_plan (MAP Var (FILTER (\v. ~MEM v
    (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
    (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)))) ps = (ops, qs)` by
    metis_tac[] >>
  drule_all inventory_popmany_mem >>
  disch_then (qspec_then `Var v` mp_tac) >> simp[MEM_MAP, MEM_FILTER] >>
  Cases_on `MEM (Var v) ps.ps_stack` >> simp[] >>
  qpat_x_assum `EVERY _ ps.ps_stack` mp_tac >>
  simp[EVERY_MEM] >>
  disch_then (qspec_then `Var v` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem inventory_cleanup_distinct:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\
  (!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb n) /\
  ALL_DISTINCT ps.ps_stack /\ clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  ALL_DISTINCT qs.ps_stack
Proof
  strip_tac >> drule_all inventory_cleanup_branch >>
  disch_then (qspec_then `lv` assume_tac) >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = (ops, qs)` mp_tac >>
  simp[] >> metis_tac[inventory_popmany_distinct]
QED

Theorem inventory_cleanup_spilled:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\
  (!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb n) /\
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  qs.ps_spilled = ps.ps_spilled
Proof
  strip_tac >> drule_all inventory_cleanup_branch >>
  disch_then (qspec_then `lv` assume_tac) >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = (ops, qs)` mp_tac >>
  simp[] >> metis_tac[rf_popmany_spilled, pairTheory.SND]
QED

Theorem inventory_cleanup_promised:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\
  (!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb n) /\
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  ~qs.ps_cleanup_promised
Proof
  strip_tac >> drule_all inventory_cleanup_branch >>
  disch_then (qspec_then `lv` assume_tac) >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = (ops, qs)` mp_tac >>
  simp[] >> metis_tac[inventory_popmany_promised, pairTheory.SND]
QED

Theorem inventory_cleanup_support:
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\
  (!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb n) /\
  ALL_DISTINCT ps.ps_stack /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions))) ps.ps_stack /\
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  EVERY (\op. ?v. op = Var v /\
    MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
    qs.ps_stack
Proof
  strip_tac >> drule_all inventory_cleanup_mem >> strip_tac >>
  drule_all inventory_cleanup_branch >>
  disch_then (qspec_then `lv` assume_tac) >>
  `!op. MEM op qs.ps_stack ==> MEM op ps.ps_stack` by
    (drule inventory_popmany >>
     disch_then (qspec_then `MAP Var (FILTER (\v. ~MEM v
       (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
       (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)))` mp_tac) >>
     gvs[] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem inventory_ret_cleanup_not_safe:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target ==>
  !n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb n
Proof
  rpt strip_tac >> gvs[] >> drule_all ret_reaching_cleanup_not_safe >> metis_tac[]
QED

Theorem inventory_ret_cleanup_mem:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\ ALL_DISTINCT ps.ps_stack /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions))) ps.ps_stack /\
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  (MEM (Var v) qs.ps_stack <=> MEM (Var v) ps.ps_stack /\
    MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
Proof
  strip_tac >> irule inventory_cleanup_mem >>
  drule_all inventory_ret_cleanup_not_safe >> metis_tac[]
QED

Theorem inventory_ret_cleanup_distinct:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\ ALL_DISTINCT ps.ps_stack /\
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  ALL_DISTINCT qs.ps_stack
Proof
  strip_tac >> drule_all inventory_ret_cleanup_not_safe >>
  disch_then (qspec_then `ps` assume_tac) >>
  irule inventory_cleanup_distinct >> metis_tac[]
QED

Theorem inventory_ret_cleanup_spilled:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\ clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  qs.ps_spilled = ps.ps_spilled
Proof
  strip_tac >> drule_all inventory_ret_cleanup_not_safe >>
  disch_then (qspec_then `ps` assume_tac) >>
  irule inventory_cleanup_spilled >> metis_tac[]
QED

Theorem inventory_ret_cleanup_promised:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\ clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  ~qs.ps_cleanup_promised
Proof
  strip_tac >> drule_all inventory_ret_cleanup_not_safe >>
  disch_then (qspec_then `ps` assume_tac) >>
  irule inventory_cleanup_promised >> metis_tac[]
QED

Theorem inventory_ret_cleanup_support:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\ ALL_DISTINCT ps.ps_stack /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at lv pred (LENGTH pred_bb.bb_instructions))) ps.ps_stack /\
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  EVERY (\op. ?v. op = Var v /\
    MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
    qs.ps_stack
Proof
  strip_tac >> drule_all inventory_ret_cleanup_not_safe >>
  disch_then (qspec_then `ps` assume_tac) >>
  irule inventory_cleanup_support >> metis_tac[]
QED

Theorem inventory_ret_cleanup_marker:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  ~ps.ps_cleanup_promised /\ ALL_DISTINCT ps.ps_stack /\
  ~MEM dead_stack_marker ps.ps_stack /\
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  ~MEM dead_stack_marker qs.ps_stack
Proof
  strip_tac >> drule_all inventory_ret_cleanup_not_safe >>
  disch_then (qspec_then `ps` assume_tac) >>
  drule_all inventory_cleanup_branch >>
  disch_then (qspec_then `lv` assume_tac) >>
  drule inventory_popmany >>
  disch_then (qspec_then `MAP Var (FILTER (\v. ~MEM v
    (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
    (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)))` mp_tac) >>
  gvs[] >> metis_tac[]
QED

Theorem inventory_lupdate_mem[local]:
  !stk i dst x. i < LENGTH stk /\ ALL_DISTINCT stk ==>
    (MEM x (LUPDATE dst i stk) <=>
     x = dst \/ (MEM x stk /\ x <> EL i stk))
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `i`
  >- (simp[LUPDATE_def] >> metis_tac[]) >>
  simp[LUPDATE_def] >> strip_tac >> first_x_assum drule_all >>
  strip_tac >> drule EL_MEM >> metis_tac[]
QED

Theorem inventory_poke_mem:
  d < LENGTH stk /\ ALL_DISTINCT stk /\ stack_peek d stk = src ==>
  !x. MEM x (stack_poke d dst stk) <=>
      x = dst \/ (MEM x stk /\ x <> src)
Proof
  simp[stack_peek_def, stack_poke_def] >> rpt strip_tac >>
  qpat_x_assum `_ = src` (SUBST1_TAC o SYM) >>
  irule inventory_lupdate_mem >> simp[]
QED

Theorem inventory_poke_distinct:
  ALL_DISTINCT stk /\ ~MEM dst stk ==>
  ALL_DISTINCT (stack_poke d dst stk)
Proof
  rpt strip_tac >>
  rw[EL_ALL_DISTINCT_EL_EQ, stack_poke_def, EL_LUPDATE] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  metis_tac[ALL_DISTINCT_EL_IMP, MEM_EL]
QED


Theorem inventory_phi_transition[local]:
  inst.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ ALL_DISTINCT ps.ps_stack /\ ~MEM (Var out) ps.ps_stack ==>
  ALL_DISTINCT (SND (generate_phi_plan inst nl F ps)).ps_stack /\
  (SND (generate_phi_plan inst nl F ps)).ps_spilled = ps.ps_spilled /\
  (!x. MEM x (SND (generate_phi_plan inst nl F ps)).ps_stack <=>
       (MEM x ps.ps_stack /\ x <> Var src) \/ (x = Var out /\ MEM out nl))
Proof
  strip_tac >>
  `ALL_DISTINCT (stack_poke d (Var out) ps.ps_stack)` by
    (irule inventory_poke_distinct >> simp[]) >>
  drule_all inventory_poke_mem >> disch_then (qspec_then `Var out` assume_tac) >>
  simp[generate_phi_plan_def, LET_THM, stackPlanTypesTheory.operand_to_string_def] >>
  Cases_on `MEM out nl` >> simp[]
  >- metis_tac[] >>
  qmatch_goalsub_abbrev_tac `popmany_plan [Var out] poked` >>
  `ALL_DISTINCT poked.ps_stack` by simp[Abbr `poked`] >>
  drule inventory_popmany >> disch_then (qspec_then `[Var out]` assume_tac) >>
  mp_tac (Q.SPECL [`[Var out]`, `poked`] rf_popmany_spilled) >>
  pairarg_tac >> simp[] >> strip_tac >>
  gvs[Abbr `poked`] >> metis_tac[]
QED
Theorem inventory_phi_mem:
  generate_phi_plan inst nl F ps = (ops, qs) /\
  inst.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ ALL_DISTINCT ps.ps_stack /\ ~MEM (Var out) ps.ps_stack ==>
  !x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var src) \/ (x = Var out /\ MEM out nl)
Proof
  strip_tac >> drule_all inventory_phi_transition >> gvs[]
QED

Theorem inventory_phi_spilled:
  generate_phi_plan inst nl F ps = (ops, qs) /\
  inst.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ ALL_DISTINCT ps.ps_stack /\ ~MEM (Var out) ps.ps_stack ==>
  qs.ps_spilled = ps.ps_spilled
Proof
  strip_tac >> drule_all inventory_phi_transition >> gvs[]
QED

Theorem inventory_phi_distinct:
  generate_phi_plan inst nl F ps = (ops, qs) /\
  inst.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ ALL_DISTINCT ps.ps_stack /\ ~MEM (Var out) ps.ps_stack ==>
  ALL_DISTINCT qs.ps_stack
Proof
  strip_tac >> drule_all inventory_phi_transition >> gvs[]
QED

Theorem inventory_phi_disjoint:
  generate_phi_plan inst nl F ps = (ops, qs) /\
  inst.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ ALL_DISTINCT ps.ps_stack /\ ~MEM (Var out) ps.ps_stack /\
  Var out NOTIN FDOM ps.ps_spilled /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
  DISJOINT (set qs.ps_stack) (FDOM qs.ps_spilled)
Proof
  strip_tac >> drule_all inventory_phi_transition >>
  gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem inventory_emit_one_spilled:
  emit_one_input opc nl op ps = (ops, qs) ==>
  FLOOKUP qs.ps_spilled (Var v) =
    (if op = Var v then NONE else FLOOKUP ps.ps_spilled (Var v))
Proof
  Cases_on `op` >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  gvs[do_restore_def, AllCaseEqs(), LET_THM] >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  rpt (IF_CASES_TAC >> gvs[AllCaseEqs()]) >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  qmatch_asmsub_abbrev_tac `do_dup dist before` >>
  mp_tac (Q.INST [`dist` |-> `dist`, `ps` |-> `before`] rf_do_dup_spilled) >>
  simp[Abbr `before`, finite_mapTheory.DOMSUB_FLOOKUP_THM]
QED

Theorem inventory_dup_count[local]:
  do_dup d ps = (ops, qs) /\ stack_get_depth op ps.ps_stack = SOME d ==>
  LENGTH (FILTER (\a. a = Var v) qs.ps_stack) =
  LENGTH (FILTER (\a. a = Var v) ps.ps_stack) + (if op = Var v then 1 else 0)
Proof
  strip_tac >> drule stack_get_depth_props >> strip_tac >>
  drule do_dup_stack_exact >> simp[] >>
  disch_then SUBST1_TAC >> simp[FILTER_APPEND] >>
  Cases_on `op = Var v` >> simp[]
QED

Theorem inventory_emit_one_count:
  emit_one_input opc nl op ps = (ops, qs) /\
  (op = Var v ==> MEM (Var v) ps.ps_stack \/ IS_SOME (FLOOKUP ps.ps_spilled (Var v))) ==>
  LENGTH (FILTER (\a. a = Var v) qs.ps_stack) =
  LENGTH (FILTER (\a. a = Var v) ps.ps_stack) +
    (if op = Var v /\ IS_SOME (FLOOKUP ps.ps_spilled (Var v)) then 1 else 0) +
    (if op = Var v /\ MEM v nl then 1 else 0)
Proof
  Cases_on `op` >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  gvs[do_restore_def, AllCaseEqs(), LET_THM] >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >> rpt (IF_CASES_TAC >> gvs[AllCaseEqs()]) >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[stack_push_def, FILTER_SNOC, inventory_depth_none] >>
  Cases_on `s = v` >> gvs[] >>
  qmatch_asmsub_abbrev_tac `do_dup dist before` >>
  `stack_get_depth (Var s) before.ps_stack = SOME dist` by simp[Abbr `before`] >>
  qmatch_goalsub_rename_tac `FILTER (\a. a = Var wanted) ps2.ps_stack` >>
  drule_all inventory_dup_count >>
  disch_then (qspec_then `wanted` mp_tac) >>
  simp[Abbr `before`, FILTER_SNOC]
QED

Theorem inventory_emit_spilled:
  !operands ps ops qs.
  emit_input_plan opc operands nl ps = (ops, qs) ==>
  FLOOKUP qs.ps_spilled (Var v) =
    (if MEM (Var v) operands then NONE else FLOOKUP ps.ps_spilled (Var v))
Proof
  Induct >> simp[emit_input_plan_def, LET_THM] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >>
  drule inventory_emit_one_spilled >>
  disch_then (qspec_then `v` assume_tac) >>
  Cases_on `h = Var v` >> simp[]
QED

Theorem inventory_count_pos[local]:
  !xs x. 0 < LENGTH (FILTER (\a. a = x) xs) <=> MEM x xs
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h = x` >> simp[]
QED

Theorem inventory_operand_vars_mem[local]:
  !operands v. MEM v (dfgDefs$operand_vars operands) <=> MEM (Var v) operands
Proof
  Induct >> simp[dfgDefsTheory.operand_vars_def] >> gen_tac >>
  Cases_on `h` >> simp[dfgDefsTheory.operand_var_def]
QED

Theorem inventory_emit_count:
  !operands ps ops qs.
  emit_input_plan opc operands nl ps = (ops, qs) /\
  (MEM (Var v) operands ==> MEM (Var v) ps.ps_stack \/ IS_SOME (FLOOKUP ps.ps_spilled (Var v))) ==>
  LENGTH (FILTER (\a. a = Var v) qs.ps_stack) +
    (if MEM (Var v) operands /\ ~MEM v nl then 1 else 0) =
  LENGTH (FILTER (\a. a = Var v) ps.ps_stack) +
    (if MEM (Var v) operands /\ IS_SOME (FLOOKUP ps.ps_spilled (Var v)) then 1 else 0) +
  LENGTH (FILTER (\a. a = Var v) operands)
Proof
  Induct >> simp[emit_input_plan_def, LET_THM] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_one_input opc _ h ps = (step_ops, mid)` >>
  `h = Var v ==> MEM (Var v) ps.ps_stack \/ IS_SOME (FLOOKUP ps.ps_spilled (Var v))` by metis_tac[] >>
  drule_all inventory_emit_one_count >> strip_tac >>
  drule inventory_emit_one_spilled >> disch_then (qspec_then `v` assume_tac) >>
  `MEM (Var v) operands ==> MEM (Var v) mid.ps_stack \/ IS_SOME (FLOOKUP mid.ps_spilled (Var v))` by
    (gvs[MEM_APPEND, inventory_operand_vars_mem] >>
     Cases_on `h = Var v` >> gvs[] >>
     Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var v))` >> gvs[] >>
     gvs[GSYM inventory_count_pos] >> decide_tac) >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `h = Var v` >>
  Cases_on `MEM (Var v) operands` >> Cases_on `MEM v nl` >>
  Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var v))` >>
  gvs[MEM_APPEND, inventory_operand_vars_mem] >> decide_tac
QED

Theorem inventory_distinct_count[local]:
  !xs x. ALL_DISTINCT xs ==>
  LENGTH (FILTER (\a. a = x) xs) = (if MEM x xs then 1 else 0)
Proof
  Induct >> simp[] >> rpt strip_tac >> Cases_on `h = x` >>
  gvs[] >> simp[FILTER_EQ_NIL, EVERY_MEM]
QED

Theorem inventory_emit_dead_count:
  emit_input_plan opc operands nl ps = (ops, qs) /\
  ~MEM v nl /\ MEM (Var v) operands /\ ALL_DISTINCT ps.ps_stack /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  (MEM (Var v) ps.ps_stack \/ IS_SOME (FLOOKUP ps.ps_spilled (Var v))) ==>
  LENGTH (FILTER (\a. a = Var v) qs.ps_stack) =
    LENGTH (FILTER (\a. a = Var v) operands) /\
  FLOOKUP qs.ps_spilled (Var v) = NONE
Proof
  strip_tac >>
  `MEM (Var v) operands ==> MEM (Var v) ps.ps_stack \/ IS_SOME (FLOOKUP ps.ps_spilled (Var v))` by simp[] >>
  drule_all inventory_emit_count >>
  drule inventory_emit_spilled >> disch_then (qspec_then `v` assume_tac) >>
  drule inventory_distinct_count >> disch_then (qspec_then `Var v` assume_tac) >>
  `~(MEM (Var v) ps.ps_stack /\ IS_SOME (FLOOKUP ps.ps_spilled (Var v)))` by
    (gvs[DISJOINT_DEF, EXTENSION, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  Cases_on `MEM (Var v) ps.ps_stack` >>
  Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var v))` >> gvs[] >> decide_tac
QED

(* Bounded contract checks: PHIs replace their unique incoming source,
   and discard a dead output on a non-halting path. *)
Theorem regional_phi_live_probe:
  !ps phi.
    phi.inst_operands = [Var "source"; Var "other"] /\
    phi.inst_outputs = ["result"] ==>
    (SND (generate_phi_plan phi ["result"] F
      (ps with ps_stack := [Var "source"]))).ps_stack = [Var "result"]
Proof
  rpt strip_tac >> simp[generate_phi_plan_def, LET_THM] >> EVAL_TAC
QED

Theorem regional_phi_dead_probe:
  !ps phi.
    phi.inst_operands = [Var "source"; Var "other"] /\
    phi.inst_outputs = ["result"] ==>
    (SND (generate_phi_plan phi [] F
      (ps with ps_stack := [Var "source"]))).ps_stack = []
Proof
  rpt strip_tac >> simp[generate_phi_plan_def, LET_THM] >> EVAL_TAC
QED

Theorem regional_offset_support_probe:
  inst.inst_operands = [Lit n; Label lbl] /\ inst.inst_outputs = [out] /\
  EVERY (\op. ?v. op = Var v /\ MEM v live) ps.ps_stack /\ MEM out live ==>
  EVERY (\op. ?v. op = Var v /\ MEM v live)
    (SND (generate_offset_plan inst ps)).ps_stack
Proof
  strip_tac >> simp[generate_offset_plan_def, LET_THM, stack_push_def,
                    EVERY_SNOC]
QED

Theorem regional_ready_nop_probe:
  codegen_ready_inst inst /\ inst.inst_opcode = NOP ==>
  inst.inst_operands = [] /\
  generate_inst_plan lv dfg cfg fn inst live halting next_term lbl ps =
    SOME ([],ps)
Proof
  simp[codegen_ready_inst_def, generate_inst_plan_def]
QED

Theorem regional_offset_dead_probe:
  inst.inst_operands = [Lit n; Label lbl] /\ inst.inst_outputs = [out] ==>
  (SND (generate_offset_plan inst (ps with ps_stack := []))).ps_stack = [Var out]
Proof
  simp[generate_offset_plan_def, LET_THM, stack_push_def]
QED

(* Ownership of a set does not determine its physical/spilled partition.
   This is a countermodel to that local inference, not to the frozen goal. *)
Theorem regional_ownership_height_probe:
  (!op. (MEM op [Var "x"] \/ op IN FDOM (FEMPTY : operand |-> num)) <=>
        (MEM op [] \/ op IN FDOM (FEMPTY |+ (Var "x",0n)))) /\
  ~(LENGTH [Var "x"] <= LENGTH ([] : operand list))
Proof
  simp[]
QED

(* Contract-validation checkpoint (C1.1.r.validate).

   PROPOSED, NOT PROVED, regional boundary invariant:
   For a predecessor edge pred -> bb and source index i after parameter
   preparation/cleanup, put
     A_i = input_vars_from pred (DROP i bb.bb_instructions)
             (live_vars_at (liveness_analyze fn) bb.bb_label i).
   Require separately:
   - EVERY (\op. ?v. op = Var v /\ MEM v A_i) ps.ps_stack;
   - ALL_DISTINCT ps.ps_stack;
   - DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled);
   - every spill key is Var v for some v in fn_all_vars fn;
   - !v. MEM v A_i ==> MEM (Var v) ps.ps_stack \/
                            Var v IN FDOM ps.ps_spilled;
   - future-output freshness, with the unprocessed PHI-source exception,
     as required by lineage_state_static; generated marked wf separately.
   This is only an instruction-boundary invariant: input emission intentionally
   duplicates values. A_i reduces to ordinary live_vars_at past the PHI prefix.
   For the initial block use the state after prepare_params_plan, not ps0.

   IMPORTANT: do NOT require every spill key to belong to A_i immediately
   after cleanup. inventory_ret_cleanup_spilled proves that cleanup leaves
   all spills unchanged, including variables needed only by another successor.
   PHI planning also does not release dead spills. The weak spill-universe
   clause above is deliberate; restore only loads requested operands. After
   a regular instruction release_dead_spills supplies the stronger live-spill
   restriction. Coverage and physical upper support are different clauses.

   Checked probes above cover unique-source PHI overwrite, PHI dead output
   deletion, OFFSET support with a live output, and ready NOP identity.
   regional_offset_dead_probe explains why OFFSET needs offset_outputs_used:
   it pushes its result even when no variable is live. The two PHI probes
   test the nonduplicating branch; regional_phi_live_source_probe below
   tests live-source duplication. Full preservation still needs arbitrary
   depths and phi_uses_disjoint/phi_operands_ready.

   MISSING LOCAL PRESERVATION CONTRACTS (not axioms):
   1. PHI: boundary inventory for A_i implies inventory for A_(i+1), with
      exactly one available source and fresh output. The source is retained
      precisely when live afterwards; a dead output is deleted.
   2. Regular: boundary support/coverage/freshness, readiness, liveness transfer,
      non-halting, and successful planning imply support/coverage for next_live.
      emit_input_plan's pending operand list explains temporary duplication;
      a last-use variable is consumed by the core pop. reorder/optimistic swap
      must preserve the residual physical support despite possible spills.
   3. JMP: after restoring/reordering all join inputs, boundary physical support
      plus distinctness must exclude a variable prefix below the target suffix.
      join_reached alone proves only the suffix, not the exclusion.
   4. Parameters: prepare_params_plan establishes the entry body's invariant
      from the initial empty stack, including dead-parameter deletion.

   ENTRY HEIGHT CONTRACT (still UNPROVED): under the analyzed, ready,
   successful whole-function plan, lookup, lineage_state and dfs_block_state
   premises of block_plan_state_static, with a RET in bb.bb_instructions,
     LENGTH ps_l.ps_stack <= LENGTH ps_dfs.ps_stack.
   The cleanup override changes neither side's initial stack. Equality is
   preferable if the eventual invariant gives it, but is not needed for the
   signed whole-trace argument. regional_ownership_height_probe falsifies
   deriving even this inequality from equal owned-variable sets alone.
   lineage_entry_join_stack allows an arbitrary marker prefix, hence is not
   a whole-stack height theorem. Required additional certificates are:
   - actual regional DFS JMP finals have no extra prefix and contain all
     edge inputs physically (no spill partition ambiguity);
   - input_vars_from has the same length across predecessors of a ready join,
     using PHI source disjointness and separation from non-PHI live inputs;
   - lineage trace transport preserves height along a single-predecessor
     edge, and at a join its height equals the canonical input cardinality.
   These are global missing proofs, NOT consequences of the local probes.

   DEPENDENCY MAP:
   Existing: inventory_popmany_mem/distinct, inventory_ret_cleanup_support,
   inventory_ret_cleanup_marker, ret_region_dfs_block_unpromised;
   ready_block_ret_last and RET successor emptiness in RetRegion;
   trace_weight / regular_correction / silent-core and reflection lemmas
   in the existing accounting theory; lineage_entry_join_stack (admitted).
   Missing: local contracts 1--4, endpoint liveness=[] for ready RET, actual
   regional DFS support/marker origins, canonical join cardinality/partition,
   the entry comparison, and full physical-fragment non-underflow/balance.
   Only after these are proved can equal block_ops transport DFS exhaustion
   to the arbitrary replay promise, then identify the RET final prefix state.
*)

Theorem regional_phi_live_source_probe:
  !ps phi.
    phi.inst_operands = [Var "source"; Var "other"] /\
    phi.inst_outputs = ["result"] ==>
    (SND (generate_phi_plan phi ["source"; "result"] F
      (ps with ps_stack := [Var "source"]))).ps_stack =
    [Var "source"; Var "result"]
Proof
  rpt strip_tac >> simp[generate_phi_plan_def, LET_THM] >> EVAL_TAC
QED
