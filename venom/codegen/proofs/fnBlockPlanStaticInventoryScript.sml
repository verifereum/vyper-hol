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
