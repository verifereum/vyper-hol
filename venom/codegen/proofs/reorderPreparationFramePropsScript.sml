Theory reorderPreparationFrameProps
Ancestors
  operandInventory fnPlanLineageSort
  fnPlanLineageReplay fnPlanLineageReduction fnPlanLineageSuffix
  reorderPreparationProps reorderPreparationInventoryProps stackPlanGen stackPlanOps stackPlanTypes stackModel planWf
  list rich_list arithmetic sorting finite_map

Theorem FIND_member_cong[local]:
  !xs P Q. (!x. MEM x xs ==> (P x <=> Q x)) ==>
    FIND P xs = FIND Q xs
Proof
  Induct >> simp[listTheory.FIND_thm] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[]
QED

Theorem stack_get_unfixed_depth_suffix_hit:
  !op f n core d prefix.
    stack_get_unfixed_depth op f n core = SOME d ==>
    stack_get_unfixed_depth op f n (prefix ++ core) = SOME d
Proof
  rpt gen_tac >> Cases_on `n <= f + 1`
  >- simp[stack_get_unfixed_depth_def, stack_get_depth_suffix_hit] >>
  asm_rewrite_tac[stack_get_unfixed_depth_def, LENGTH_APPEND] >>
  strip_tac >>
  `GENLIST I (LENGTH prefix + LENGTH core) =
    GENLIST I (LENGTH core) ++
    GENLIST (\t. t + LENGTH core) (LENGTH prefix)` by
      simp[Once arithmeticTheory.ADD_COMM, GENLIST_APPEND] >>
  asm_rewrite_tac[callLayoutDefsTheory.FIND_APPEND_CASE] >>
  `FIND (\d. ~(f < d /\ d < n) /\ stack_peek d (prefix ++ core) = op)
      (GENLIST I (LENGTH core)) =
    FIND (\d. ~(f < d /\ d < n) /\ stack_peek d core = op)
      (GENLIST I (LENGTH core))` by
    (irule FIND_member_cong >> simp[MEM_GENLIST] >> rpt strip_tac >>
     simp[stack_peek_def, EL_APPEND2]) >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem stack_get_unfixed_depth_bottom_excluded:
  !op prefix core f n. ~MEM op prefix ==>
    stack_get_unfixed_depth op f n (prefix ++ core) =
    stack_get_unfixed_depth op f n core
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `n <= f + 1`
  >- simp[stack_get_unfixed_depth_def, stack_get_depth_bottom_excluded] >>
  asm_rewrite_tac[stack_get_unfixed_depth_def, LENGTH_APPEND] >>
  `GENLIST I (LENGTH prefix + LENGTH core) =
    GENLIST I (LENGTH core) ++
    GENLIST (\t. t + LENGTH core) (LENGTH prefix)` by
      simp[Once arithmeticTheory.ADD_COMM, GENLIST_APPEND] >>
  asm_rewrite_tac[callLayoutDefsTheory.FIND_APPEND_CASE] >>
  `FIND (\d. ~(f < d /\ d < n) /\ stack_peek d (prefix ++ core) = op)
      (GENLIST I (LENGTH core)) =
    FIND (\d. ~(f < d /\ d < n) /\ stack_peek d core = op)
      (GENLIST I (LENGTH core))` by
    (irule FIND_member_cong >> simp[MEM_GENLIST] >> rpt strip_tac >>
     simp[stack_peek_def, EL_APPEND2]) >>
  asm_rewrite_tac[] >>
  Cases_on `FIND (\d. ~(f < d /\ d < n) /\ stack_peek d core = op)
    (GENLIST I (LENGTH core))` >> simp[] >>
  Cases_on `FIND (\d. ~(f < d /\ d < n) /\
    stack_peek d (prefix ++ core) = op)
    (GENLIST (\t. t + LENGTH core) (LENGTH prefix))` >> gvs[] >>
  drule stackPlanGenTheory.FIND_SOME_MEM >> disch_then strip_assume_tac >>
  qpat_x_assum `MEM _ (GENLIST _ _)` mp_tac >>
  rewrite_tac[MEM_GENLIST] >> strip_tac >>
  `x < LENGTH core + LENGTH prefix /\ LENGTH core <= x` by (fs[] >> decide_tac) >>
  `LENGTH (prefix ++ core) - (x + 1) < LENGTH prefix` by simp[] >>
  `MEM (stack_peek x (prefix ++ core)) prefix` by
    (simp[stack_peek_def, EL_APPEND1] >> irule EL_MEM >> decide_tac) >>
  metis_tac[]
QED

Theorem stack_get_unfixed_depth_shielded:
  !op f n core prefix.
    (~MEM op prefix \/ IS_SOME (stack_get_unfixed_depth op f n core)) ==>
    stack_get_unfixed_depth op f n (prefix ++ core) =
      stack_get_unfixed_depth op f n core
Proof
  rpt strip_tac >- simp[stack_get_unfixed_depth_bottom_excluded] >>
  Cases_on `stack_get_unfixed_depth op f n core` >> gvs[] >>
  metis_tac[stack_get_unfixed_depth_suffix_hit]
QED

Theorem select_spill_candidate_bottom_frame:
  !prefix core targets dist n. dist < LENGTH core ==>
    select_spill_candidate (prefix ++ core) targets dist n =
    select_spill_candidate core targets dist n
Proof
  rpt gen_tac >> strip_tac >>
  `MIN (dist - 1) (LENGTH (prefix ++ core) - 1) = dist - 1 /\
   MIN (dist - 1) (LENGTH core - 1) = dist - 1` by simp[arithmeticTheory.MIN_DEF] >>
  asm_rewrite_tac[select_spill_candidate_def, LET_THM] >> BETA_TAC >>
  irule FIND_member_cong >> simp[MEM_GENLIST] >> rpt strip_tac >>
  `x < LENGTH core` by (fs[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  simp[stack_peek_def, EL_APPEND2]
QED

Theorem do_restore_bottom_frame:
  !op ps prefix ops qs. do_restore op ps = (ops,qs) ==>
    do_restore op (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[stack_push_def, SNOC_APPEND, APPEND_ASSOC] >> strip_tac >> gvs[]
QED

Theorem restore_spilled_plan_bottom_frame:
  !targets ps prefix ops qs.
    restore_spilled_plan targets ps = (ops,qs) ==>
    restore_spilled_plan targets (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct >> rpt gen_tac
  >- (simp[restore_spilled_plan_def] >> strip_tac >> gvs[]) >>
  simp[restore_spilled_plan_def] >>
  Cases_on `do_restore h ps` >>
  Cases_on `restore_spilled_plan targets r` >> simp[] >> strip_tac >> gvs[] >>
  drule do_restore_bottom_frame >> disch_then (qspec_then `prefix` assume_tac) >>
  first_x_assum drule >> disch_then (qspec_then `prefix` assume_tac) >>
  simp[]
QED

Theorem do_spill_at_bottom_frame:
  !d ps prefix ops qs.
    d < LENGTH ps.ps_stack /\ d <= 16 /\ do_spill_at d ps = (ops,qs) ==>
    do_spill_at d (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  Cases_on `d = 0` >> gvs[do_spill_at_def, do_spill_tos_def] >>
  simp[stack_swap_bottom_extension, stack_peek_def, EL_APPEND2,
       stack_pop_def, TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
       stackPlanTypesTheory.plan_state_component_equality] >>
  pairarg_tac >> gvs[stack_pop_def, stack_peek_def]
QED

Theorem reduce_depth_plan_shielded_bottom_frame:
  !fuel targets op f n ps prefix ops qs.
    (~MEM op prefix \/
      (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op f n ps.ps_stack))) /\
    reduce_depth_plan fuel targets op f n ps = (ops,qs) ==>
    reduce_depth_plan fuel targets op f n
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct_on `fuel` >- simp[reduce_depth_plan_def] >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `f + 1 < n` >- gvs[reduce_depth_plan_def] >>
  `stack_get_unfixed_depth op f n (prefix ++ ps.ps_stack) =
    stack_get_unfixed_depth op f n ps.ps_stack` by
      (irule stack_get_unfixed_depth_shielded >> metis_tac[]) >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack`
  >- gvs[reduce_depth_plan_def] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >- gvs[reduce_depth_plan_def] >>
  `dist < LENGTH ps.ps_stack` by
    metis_tac[stack_get_unfixed_depth_bound] >>
  `select_spill_candidate (prefix ++ ps.ps_stack) targets dist n =
    select_spill_candidate ps.ps_stack targets dist n` by
      simp[select_spill_candidate_bottom_frame] >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist n`
  >- gvs[reduce_depth_plan_def] >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    (drule_at (Pat `select_spill_candidate _ _ _ _ = SOME _`)
       planWfTheory.select_spill_candidate_bound >>
     simp[]) >>
  Cases_on `do_spill_at cand ps` >>
  rename1 `do_spill_at cand ps = (spill_ops, mid)` >>
  drule_all do_spill_at_bottom_frame >>
  disch_then (qspec_then `prefix` assume_tac) >>
  `~MEM op prefix \/
    (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op f n mid.ps_stack))` by
    (Cases_on `MEM op prefix` >> gvs[] >>
     `reduce_depth_plan (SUC 0) targets op f n ps = (spill_ops,mid)` by
       simp[reduce_depth_plan_def] >>
     irule reduce_depth_plan_unfixed_hit >>
     qexistsl [`SUC 0`, `spill_ops`, `ps`, `targets`] >> simp[]) >>
  Cases_on `reduce_depth_plan fuel targets op f n mid` >>
  `reduce_depth_plan fuel targets op f n
     (mid with ps_stack := prefix ++ mid.ps_stack) =
   (q,r with ps_stack := prefix ++ r.ps_stack)` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!targets op f n ps prefix ops qs. _` kall_tac >>
  qpat_x_assum `reduce_depth_plan (SUC fuel) _ _ _ _ _ = _` mp_tac >>
  simp[Once reduce_depth_plan_def] >> strip_tac >>
  simp[Once reduce_depth_plan_def] >> gvs[]
QED

Theorem reduce_depth_plan_bottom_frame:
  !fuel targets op f n ps prefix ops qs.
    ~MEM op prefix /\ reduce_depth_plan fuel targets op f n ps = (ops,qs) ==>
    reduce_depth_plan fuel targets op f n
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule reduce_depth_plan_shielded_bottom_frame >> simp[]
QED

Theorem reduce_depth_plan_height_shielded_bottom_frame:
  !targets op f n ps prefix ops qs.
    (~MEM op prefix \/
      (MEM op targets /\ IS_SOME (stack_get_unfixed_depth op f n ps.ps_stack))) /\
    reduce_depth_plan (LENGTH ps.ps_stack) targets op f n ps = (ops,qs) ==>
    reduce_depth_plan (LENGTH (prefix ++ ps.ps_stack)) targets op f n
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `reduce_depth_plan (LENGTH (prefix ++ ps.ps_stack)) targets op f n ps =
   reduce_depth_plan (LENGTH ps.ps_stack) targets op f n ps` by
    (irule reduce_depth_plan_adequate_fuel >> simp[]) >>
  irule reduce_depth_plan_shielded_bottom_frame >> simp[]
QED

Theorem reduce_depth_plan_height_bottom_frame:
  !targets op f n ps prefix ops qs.
    ~MEM op prefix /\
    reduce_depth_plan (LENGTH ps.ps_stack) targets op f n ps = (ops,qs) ==>
    reduce_depth_plan (LENGTH (prefix ++ ps.ps_stack)) targets op f n
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule reduce_depth_plan_height_shielded_bottom_frame >> simp[]
QED

Theorem list_elem_count_dom_extra[local]:
  !stk targets extra.
    MEM extra stk /\ ~MEM extra targets /\
    (!x. MEM x targets ==> LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x stk) ==>
    LENGTH targets < LENGTH stk
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM extra stk` (strip_assume_tac o SRULE [MEM_SPLIT]) >>
  gvs[] >>
  `!x. LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x (l1 ++ l2)` by
    (gen_tac >> Cases_on `MEM x targets`
     >- (`extra <> x` by metis_tac[] >>
         `LIST_ELEM_COUNT x (l1 ++ [extra] ++ l2) =
           LIST_ELEM_COUNT x (l1 ++ l2)` by simp[LIST_ELEM_COUNT_DEF, FILTER_APPEND] >>
         metis_tac[]) >>
     fs[GSYM LIST_ELEM_COUNT_MEM] >>
     `LIST_ELEM_COUNT x targets = 0` by decide_tac >> simp[]) >>
  drule list_elem_count_dom_length >> simp[]
QED

(* The excess-height fuel cannot expire while there is another eligible spill. *)
Theorem reduce_depth_plan_excess_fuel[local]:
  !ps k m targets op.
    LENGTH ps.ps_stack - LENGTH targets <= k /\
    LENGTH ps.ps_stack - LENGTH targets <= m /\
    (LENGTH targets <= 17 \/
     !at. MEM at targets ==>
       LIST_ELEM_COUNT at targets <= LIST_ELEM_COUNT at ps.ps_stack) ==>
    reduce_depth_plan k targets op 0 0 ps =
    reduce_depth_plan m targets op 0 0 ps
Proof
  measureInduct_on `LENGTH ps.ps_stack` >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `stack_get_unfixed_depth op 0 0 ps.ps_stack`
  >- (Cases_on `k` >> Cases_on `m` >> simp[reduce_depth_plan_def]) >>
  rename1 `stack_get_unfixed_depth op 0 0 ps.ps_stack = SOME dist` >>
  Cases_on `dist <= 16`
  >- (Cases_on `k` >> Cases_on `m` >> simp[reduce_depth_plan_def]) >>
  Cases_on `select_spill_candidate ps.ps_stack targets dist 0`
  >- (Cases_on `k` >> Cases_on `m` >> simp[reduce_depth_plan_def]) >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_unfixed_depth_bound] >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  `~MEM (stack_peek cand ps.ps_stack) targets` by
    metis_tac[select_spill_candidate_not_pending] >>
  `LENGTH targets < LENGTH ps.ps_stack` by
    (Cases_on `LENGTH targets <= 17` >- decide_tac >>
     qspecl_then [`ps.ps_stack`, `targets`, `stack_peek cand ps.ps_stack`]
       mp_tac list_elem_count_dom_extra >>
     simp[stack_peek_mem] >> metis_tac[]) >>
  Cases_on `k` >> Cases_on `m` >> gvs[] >>
  Cases_on `do_spill_at cand ps` >>
  rename1 `do_spill_at cand ps = (spill_ops,mid)` >>
  `16 < dist /\ cand < LENGTH ps.ps_stack` by decide_tac >>
  `LENGTH mid.ps_stack + 1 = LENGTH ps.ps_stack` by
    metis_tac[reduce_depth_step_height] >>
  `LENGTH targets <= 17 \/
    !at. MEM at targets ==>
       LIST_ELEM_COUNT at targets <= LIST_ELEM_COUNT at mid.ps_stack` by
    (Cases_on `LENGTH targets <= 17` >> simp[] >> rpt strip_tac >>
     `at <> stack_peek cand ps.ps_stack` by metis_tac[] >>
     `cand < LENGTH ps.ps_stack` by decide_tac >>
     `LIST_ELEM_COUNT at mid.ps_stack = LIST_ELEM_COUNT at ps.ps_stack` by
       metis_tac[do_spill_at_other_stack_count] >> simp[]) >>
  `reduce_depth_plan n targets op 0 0 mid = reduce_depth_plan n' targets op 0 0 mid` by
    (first_x_assum (qspec_then `mid.ps_stack` mp_tac) >>
     impl_tac >- decide_tac >>
     disch_then (qspec_then `mid` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`n`, `n'`, `targets`, `op`] mp_tac) >>
     simp[] >> decide_tac) >>
  simp[Ntimes reduce_depth_plan_def 2]
QED

Theorem reorder_reduce_bottom_frame[local]:
  !ordered targets ps prefix acc.
    EVERY (\op. MEM op targets) ordered /\
    (EVERY (\op. ~MEM op prefix) targets \/
     !at. MEM at targets ==>
       LIST_ELEM_COUNT at targets <= LIST_ELEM_COUNT at ps.ps_stack) /\
    (LENGTH targets <= 17 \/
     !at. MEM at targets ==>
       LIST_ELEM_COUNT at targets <= LIST_ELEM_COUNT at ps.ps_stack) ==>
    FOLDL (\(ops,st) op.
      (\(step,out). (ops ++ step,out))
        (reduce_depth_plan (LENGTH st.ps_stack - LENGTH targets) targets op 0 0 st))
       (acc,ps with ps_stack := prefix ++ ps.ps_stack) ordered =
    (\(ops,post). (ops,post with ps_stack := prefix ++ post.ps_stack))
      (FOLDL (\(ops,st) op.
        (\(step,out). (ops ++ step,out))
          (reduce_depth_plan (LENGTH st.ps_stack - LENGTH targets) targets op 0 0 st))
        (acc,ps) ordered)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `reduce_depth_plan (LENGTH ps.ps_stack - LENGTH targets)
    targets h 0 0 ps` >>
  rename1 `reduce_depth_plan _ _ _ _ _ ps = (step_ops,mid)` >>
  `(~MEM h prefix \/ IS_SOME (stack_get_unfixed_depth h 0 0 ps.ps_stack))` by
    (Cases_on `MEM h prefix` >> simp[] >>
     `LIST_ELEM_COUNT h targets <= LIST_ELEM_COUNT h ps.ps_stack` by
       (qpat_assum `EVERY _ targets \/ _`
          (DISJ_CASES_THEN2
            (qspec_then `h` mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM])
            (qspec_then `h` mp_tac)) >> simp[]) >>
     `1 <= LIST_ELEM_COUNT h targets` by
       metis_tac[elem_count_mem_pos_inventory] >>
     `MEM h ps.ps_stack` by
       (pure_rewrite_tac[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
     drule stack_get_depth_exists_inventory >> strip_tac >>
     simp[stack_get_unfixed_depth_empty_window]) >>
  `reduce_depth_plan (LENGTH (prefix ++ ps.ps_stack) - LENGTH targets)
    targets h 0 0 ps = (step_ops,mid)` by
    (qspecl_then [`ps`, `LENGTH (prefix ++ ps.ps_stack) - LENGTH targets`,
        `LENGTH ps.ps_stack - LENGTH targets`, `targets`, `h`] mp_tac
       reduce_depth_plan_excess_fuel >>
     simp[] >> decide_tac) >>
  `reduce_depth_plan (LENGTH prefix + LENGTH ps.ps_stack - LENGTH targets)
    targets h 0 0 ps = (step_ops,mid)` by fs[LENGTH_APPEND] >>
  `reduce_depth_plan (LENGTH prefix + LENGTH ps.ps_stack - LENGTH targets)
    targets h 0 0 (ps with ps_stack := prefix ++ ps.ps_stack) =
    (step_ops,mid with ps_stack := prefix ++ mid.ps_stack)` by
    (irule reduce_depth_plan_shielded_bottom_frame >> simp[]) >>
  `!at. MEM at targets ==>
      LIST_ELEM_COUNT at mid.ps_stack = LIST_ELEM_COUNT at ps.ps_stack` by
    (rpt strip_tac >>
     qspecl_then [`LENGTH ps.ps_stack - LENGTH targets`, `targets`, `h`,
       `0`, `0`, `ps`, `step_ops`, `mid`, `at`] mp_tac
       reduce_depth_plan_keeps_pending_count >> simp[]) >>
  simp[] >>
  first_x_assum (qspecl_then [`targets`, `mid`, `prefix`, `acc ++ step_ops`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem reorder_prepare_bottom_frame:
  !targets ps prefix ops post.
    (EVERY (\op. ~MEM op prefix) targets \/
     !at. MEM at targets ==>
       LIST_ELEM_COUNT at targets <= LIST_ELEM_COUNT at ps.ps_stack) /\
    reorder_prepare_plan targets ps = (ops,post) ==>
    reorder_prepare_plan targets (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,post with ps_stack := prefix ++ post.ps_stack)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `restore_spilled_plan (FILTER is_var_operand targets) ps` >>
  rename1 `restore_spilled_plan _ ps = (restore_ops,restored)` >>
  drule restore_spilled_plan_bottom_frame >>
  disch_then (qspec_then `prefix` assume_tac) >>
  qspecl_then [`FILTER is_var_operand targets`, `ps`, `restore_ops`, `restored`]
    mp_tac restore_spilled_plan_counts >> simp[MEM_FILTER] >> strip_tac >>
  `(!at. MEM at targets ==> ~MEM at prefix) \/
    (!at. MEM at targets ==>
       LIST_ELEM_COUNT at targets <= LIST_ELEM_COUNT at restored.ps_stack)` by
    (Cases_on `EVERY (\op. ~MEM op prefix) targets` >- fs[EVERY_MEM] >>
     fs[EVERY_MEM] >> disj2_tac >> rpt strip_tac >>
     qpat_x_assum `!at. MEM at targets ==> _ <= _` (qspec_then `at` mp_tac) >>
     simp[] >> disch_tac >>
     qpat_x_assum `!x. LIST_ELEM_COUNT x restored.ps_stack = _`
       (qspec_then `at` mp_tac) >> simp[] >> decide_tac) >>
  `!op. MEM op targets ==>
    stack_get_depth op (prefix ++ restored.ps_stack) =
    stack_get_depth op restored.ps_stack` by
    (rpt strip_tac >> Cases_on `MEM op prefix`
     >- (`!at. MEM at targets ==>
                LIST_ELEM_COUNT at targets <= LIST_ELEM_COUNT at restored.ps_stack` by metis_tac[] >>
         `MEM op restored.ps_stack` by
           (qpat_x_assum `!at. MEM at targets ==> _ <= LIST_ELEM_COUNT at restored.ps_stack`
              (qspec_then `op` mp_tac) >> simp[] >>
            `1 <= LIST_ELEM_COUNT op targets` by metis_tac[elem_count_mem_pos_inventory] >>
            simp[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
         drule stack_get_depth_exists_inventory >> strip_tac >>
         metis_tac[stack_get_depth_suffix_hit]) >>
     simp[stack_get_depth_bottom_excluded]) >>
  `EVERY (\op. LIST_ELEM_COUNT op targets <=
    LIST_ELEM_COUNT op (prefix ++ restored.ps_stack)) targets <=>
    EVERY (\op. LIST_ELEM_COUNT op targets <=
    LIST_ELEM_COUNT op restored.ps_stack) targets` by
    (Cases_on `!at. MEM at targets ==> ~MEM at prefix`
     >- (`!op. MEM op targets ==> FILTER (\x. x = op) prefix = []` by
           (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
         `!op. MEM op targets ==>
            LIST_ELEM_COUNT op (prefix ++ restored.ps_stack) =
            LIST_ELEM_COUNT op restored.ps_stack` by
           (rpt strip_tac >>
            rewrite_tac[LIST_ELEM_COUNT_DEF, FILTER_APPEND, LENGTH_APPEND] >>
            simp[]) >>
         simp[EVERY_MEM] >> metis_tac[]) >>
     `!at. MEM at targets ==>
        LIST_ELEM_COUNT at targets <= LIST_ELEM_COUNT at restored.ps_stack` by metis_tac[] >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!at. MEM at targets ==> _ <= LIST_ELEM_COUNT at restored.ps_stack`
       (qspec_then `op` mp_tac) >>
     rewrite_tac[LIST_ELEM_COUNT_DEF, FILTER_APPEND, LENGTH_APPEND] >>
     simp[] >> decide_tac) >>
  `QSORT (\a b.
      (case stack_get_depth b (prefix ++ restored.ps_stack) of NONE => 0 | SOME d => d) <=
      (case stack_get_depth a (prefix ++ restored.ps_stack) of NONE => 0 | SOME d => d))
      targets =
    QSORT (\a b.
      (case stack_get_depth b restored.ps_stack of NONE => 0 | SOME d => d) <=
      (case stack_get_depth a restored.ps_stack of NONE => 0 | SOME d => d))
      targets` by (irule qsort_relation_on >> simp[]) >>
  gvs[reorder_prepare_plan_def] >>
  IF_CASES_TAC >> gvs[] >>
  qmatch_goalsub_abbrev_tac `FOLDL _ _ ordered` >>
  `EVERY (\op. MEM op targets) ordered` by
    simp[Abbr `ordered`, EVERY_MEM, QSORT_MEM] >>
  qspecl_then [`ordered`, `targets`, `restored`, `prefix`, `[]:stack_op list`]
    mp_tac reorder_reduce_bottom_frame >>
  impl_tac >- (rpt conj_tac >> fs[EVERY_MEM] >> first_assum ACCEPT_TAC) >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED
