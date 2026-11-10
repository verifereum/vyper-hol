Theory fnPlanLineageResourceErasure
Ancestors
  stackPlanOps list finite_map

(* Forget only address payloads, not stack actions or symbolic cells. *)
Definition erase_spill_address_def:
  erase_spill_address op =
    case op of SOSpill n => SOSpill 0 | SORestore n => SORestore 0 | _ => op
End

Definition stack_domain_eq_def:
  stack_domain_eq p q <=>
    p.ps_stack = q.ps_stack /\ FDOM p.ps_spilled = FDOM q.ps_spilled
End

Theorem do_spill_tos_resource_erasure:
  !p q os p' ts q'.
    stack_domain_eq p q /\ do_spill_tos p = (os,p') /\
    do_spill_tos q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> simp[do_spill_tos_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[stack_domain_eq_def, erase_spill_address_def]
QED

Theorem do_restore_resource_erasure:
  !op p q os p' ts q'.
    stack_domain_eq p q /\ do_restore op p = (os,p') /\
    do_restore op q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> simp[stack_domain_eq_def, do_restore_def] >>
  Cases_on `FLOOKUP p.ps_spilled op` >>
  Cases_on `FLOOKUP q.ps_spilled op` >>
  strip_tac >> gvs[stack_domain_eq_def, erase_spill_address_def] >>
  fs[FLOOKUP_DEF]
QED

Theorem do_spill_at_resource_erasure:
  !d p q os p' ts q'.
    stack_domain_eq p q /\ do_spill_at d p = (os,p') /\
    do_spill_at d q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> Cases_on `d = 0`
  >- (simp[do_spill_at_def] >>
      MATCH_ACCEPT_TAC do_spill_tos_resource_erasure) >>
  simp[do_spill_at_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  `stack_domain_eq
    (p with ps_stack := stack_swap d p.ps_stack)
    (q with ps_stack := stack_swap d q.ps_stack)` by
    fs[stack_domain_eq_def] >>
  drule_all do_spill_tos_resource_erasure >>
  gvs[erase_spill_address_def]
QED

Theorem restore_spilled_plan_resource_erasure:
  !operands p q os p' ts q'.
    stack_domain_eq p q /\ restore_spilled_plan operands p = (os,p') /\
    restore_spilled_plan operands q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  Induct >- simp[restore_spilled_plan_def] >>
  rpt gen_tac >> simp[restore_spilled_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all do_restore_resource_erasure >> strip_tac >>
  first_x_assum drule >> disch_then drule >> disch_then drule >>
  gvs[]
QED

Theorem reorder_cost_resource_erasure:
  !os. reorder_cost (MAP erase_spill_address os) = reorder_cost os
Proof
  Induct >> simp[reorder_cost_def] >>
  Cases_on `h` >> gvs[erase_spill_address_def, reorder_cost_def]
QED

Theorem spill_allocation_fold_erasure[local]:
  !(items:operand list) ops offs al os offsets al'.
    FOLDL (\(ops, offs, al) item.
      (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
        (alloc_spill_slot al))
      (ops, offs, al) items = (os, offsets, al') ==>
    MAP erase_spill_address os =
      MAP erase_spill_address ops ++ REPLICATE (LENGTH items) (SOSpill 0) /\
    LENGTH offsets = LENGTH offs + LENGTH items
Proof
  Induct >> simp[] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> strip_tac >>
  first_x_assum drule >>
  simp[erase_spill_address_def, APPEND_ASSOC]
QED

Theorem do_swap_resource_erasure:
  !d p q os p' ts q'.
    stack_domain_eq p q /\ do_swap d p = (os,p') /\
    do_swap d q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> Cases_on `d = 0`
  >- (strip_tac >> gvs[do_swap_def]) >>
  Cases_on `d <= 16`
  >- (strip_tac >> gvs[do_swap_def, stack_domain_eq_def]) >>
  simp[do_swap_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac (SRULE [] spill_allocation_fold_erasure) >>
  gvs[stack_domain_eq_def, MAP_MAP_o, combinTheory.o_DEF,
      erase_spill_address_def]
QED

Theorem do_dup_resource_erasure:
  !d p q os p' ts q'.
    stack_domain_eq p q /\ do_dup d p = (os,p') /\
    do_dup d q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> Cases_on `d <= 15`
  >- (strip_tac >> gvs[do_dup_def, stack_domain_eq_def]) >>
  simp[do_dup_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac (SRULE [] spill_allocation_fold_erasure) >>
  gvs[stack_domain_eq_def, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF,
      erase_spill_address_def]
QED

Theorem reduce_depth_plan_resource_erasure:
  !fuel targets op f n p q os p' ts q'.
    stack_domain_eq p q /\
    reduce_depth_plan fuel targets op f n p = (os,p') /\
    reduce_depth_plan fuel targets op f n q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  Induct >- (rpt strip_tac >> gvs[reduce_depth_plan_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `f + 1 < n`
  >- gvs[reduce_depth_plan_def] >>
  `p.ps_stack = q.ps_stack` by fs[stack_domain_eq_def] >>
  Cases_on `stack_get_unfixed_depth op f n p.ps_stack`
  >- gvs[reduce_depth_plan_def] >>
  rename1 `stack_get_unfixed_depth op f n p.ps_stack = SOME dist` >>
  Cases_on `dist <= 16`
  >- gvs[reduce_depth_plan_def] >>
  Cases_on `select_spill_candidate p.ps_stack targets dist n`
  >- gvs[reduce_depth_plan_def] >>
  gvs[reduce_depth_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all do_spill_at_resource_erasure >> strip_tac >>
  first_x_assum drule >> disch_then drule >> disch_then drule >>
  gvs[]
QED

Theorem reorder_one_resource_erasure:
  !dfg targets idx op p q os p' ts q'.
    stack_domain_eq p q /\ reorder_one dfg targets idx op p = (os,p') /\
    reorder_one dfg targets idx op q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  rpt gen_tac >> strip_tac >>
  `p.ps_stack = q.ps_stack` by fs[stack_domain_eq_def] >>
  qpat_x_assum `reorder_one _ _ _ _ p = _` mp_tac >>
  qpat_x_assum `reorder_one _ _ _ _ q = _` mp_tac >>
  simp[reorder_one_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `MAP erase_spill_address restore_ops = MAP erase_spill_address restore_ops' /\
   stack_domain_eq ps1 ps1'` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
       (LENGTH targets) p.ps_stack` >> gvs[] >>
     Cases_on `FLOOKUP p.ps_spilled op` >>
     Cases_on `FLOOKUP q.ps_spilled op` >> gvs[] >>
     gvs[stack_domain_eq_def, do_restore_def, FLOOKUP_DEF,
         erase_spill_address_def]) >>
  qpat_x_assum `(_ : stack_op list # plan_state) = (restore_ops,ps1)` kall_tac >>
  qpat_x_assum `(_ : stack_op list # plan_state) = (restore_ops',ps1')` kall_tac >>
  `ps1.ps_stack = ps1'.ps_stack` by fs[stack_domain_eq_def] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps1.ps_stack`
  >- (gvs[] >> rpt strip_tac >> gvs[stack_domain_eq_def]) >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >>
  `MAP erase_spill_address reduce_ops = MAP erase_spill_address reduce_ops' /\
   stack_domain_eq ps2 ps2'` by
    (Cases_on `x > 16` >> gvs[] >>
     metis_tac[reduce_depth_plan_resource_erasure]) >>
  `ps2.ps_stack = ps2'.ps_stack` by fs[stack_domain_eq_def] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps2.ps_stack`
  >- (gvs[] >> rpt strip_tac >> gvs[stack_domain_eq_def]) >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist = LENGTH targets - (idx + 1)`
  >- (gvs[] >> rpt strip_tac >> gvs[stack_domain_eq_def]) >>
  Cases_on `LENGTH targets < idx + (LENGTH ps2.ps_stack + 1) /\
            0 < LENGTH ps2.ps_stack` >> gvs[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH targets - (idx + 1)) ps2'.ps_stack)` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  TRY (gvs[stack_domain_eq_def] >> NO_TAC) >>
  `MAP erase_spill_address swap1_ops = MAP erase_spill_address swap1_ops' /\
   stack_domain_eq ps3 ps3'` by metis_tac[do_swap_resource_erasure] >>
  `MAP erase_spill_address swap2_ops = MAP erase_spill_address swap2_ops' /\
   stack_domain_eq ps4 p'` by metis_tac[do_swap_resource_erasure] >>
  gvs[stack_domain_eq_def]
QED

Theorem reorder_fold_resource_erasure[local]:
  !items dfg targets acc p bcc q os p' ts q'.
    MAP erase_spill_address acc = MAP erase_spill_address bcc /\
    stack_domain_eq p q /\
    FOLDL (\(ops,ps) (idx,op).
      (\(step,ps'). (ops ++ step,ps')) (reorder_one dfg targets idx op ps))
      (acc,p) items = (os,p') /\
    FOLDL (\(ops,ps) (idx,op).
      (\(step,ps'). (ops ++ step,ps')) (reorder_one dfg targets idx op ps))
      (bcc,q) items = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  Induct >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all reorder_one_resource_erasure >> strip_tac >>
  first_x_assum irule >>
  qexistsl [`acc ++ step'`, `bcc ++ step''`, `dfg`, `ps'`, `ps''`, `targets`] >>
  simp[]
QED

Theorem reorder_plan_resource_erasure:
  !dfg targets p q os p' ts q'.
    stack_domain_eq p q /\ reorder_plan dfg targets p = (os,p') /\
    reorder_plan dfg targets q = (ts,q') ==>
    MAP erase_spill_address os = MAP erase_spill_address ts /\
    stack_domain_eq p' q'
Proof
  simp[reorder_plan_def] >> rpt strip_tac >>
  metis_tac[reorder_fold_resource_erasure]
QED

Theorem do_swap_erased_code:
  !d p. d < LENGTH p.ps_stack ==>
    MAP erase_spill_address (FST (do_swap d p)) =
    if d = 0 then [] else if d <= 16 then [SOSwap d] else
      REPLICATE (d + 1) (SOSpill 0) ++
      MAP (\i. SORestore 0)
        (REVERSE ([d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0]))
Proof
  rpt strip_tac >> Cases_on `d = 0` >- simp[do_swap_def] >>
  Cases_on `d <= 16`
  >- simp[do_swap_def, erase_spill_address_def] >>
  simp[do_swap_def] >> rpt (pairarg_tac >> gvs[]) >>
  drule (SRULE [SNOC_APPEND] spill_allocation_fold_erasure) >>
  simp[top_n_def, LENGTH_TAKE, MAP_MAP_o, combinTheory.o_DEF,
       erase_spill_address_def]
QED

Theorem do_dup_erased_code:
  !d p. d < LENGTH p.ps_stack ==>
    MAP erase_spill_address (FST (do_dup d p)) =
    if d <= 15 then [SODup (d + 1)] else
      REPLICATE (d - 15) (SOSpill 0) ++ [SODup 16] ++
      FLAT (MAP (\i. SORestore 0 ::
              (if d - 15 <= 16 then [] else [SOSwap 1]))
        (if d - 15 <= 16 then
           GENLIST (\i. d - 15 - 2 - i) (d - 15 - 1) ++ [d - 15 - 1]
         else GENLIST (\i. d - 15 - 1 - i) (d - 15))) ++
      (if d - 15 <= 16 then [SOSwap (d - 15)] else [])
Proof
  rpt strip_tac >> Cases_on `d <= 15`
  >- simp[do_dup_def, erase_spill_address_def] >>
  simp[do_dup_def] >> rpt (pairarg_tac >> gvs[]) >>
  drule spill_allocation_fold_erasure >>
  Cases_on `d <= 31` >>
  simp[top_n_def, LENGTH_TAKE, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF,
       erase_spill_address_def]
QED

Theorem do_swap_erased_spill_count[local]:
  !d p. d < LENGTH p.ps_stack ==>
    LENGTH (FILTER ($= (SOSpill 0))
      (MAP erase_spill_address (FST (do_swap d p)))) =
    if d <= 16 then 0 else d + 1
Proof
  rpt strip_tac >> drule do_swap_erased_code >> strip_tac >>
  simp[] >> Cases_on `d = 0` >> Cases_on `d <= 16` >>
  simp[FILTER_APPEND_DISTRIB, iffRL FILTER_EQ_ID, iffRL FILTER_EQ_NIL, EVERY_MAP,
       rich_listTheory.EVERY_REPLICATE]
QED

Theorem do_dup_erased_spill_count[local]:
  !d p. d < LENGTH p.ps_stack ==>
    LENGTH (FILTER ($= (SOSpill 0))
      (MAP erase_spill_address (FST (do_dup d p)))) = d - 15
Proof
  rpt strip_tac >> drule do_dup_erased_code >> strip_tac >>
  simp[] >> Cases_on `d <= 15` >> Cases_on `d - 15 <= 16` >>
  simp[FILTER_APPEND_DISTRIB, iffRL FILTER_EQ_ID, iffRL FILTER_EQ_NIL, EVERY_MAP,
       EVERY_FLAT, rich_listTheory.EVERY_REPLICATE]
QED

Theorem do_swap_erased_code_injective:
  !d e p q. d < LENGTH p.ps_stack /\ e < LENGTH q.ps_stack ==>
    ((MAP erase_spill_address (FST (do_swap d p)) =
      MAP erase_spill_address (FST (do_swap e q))) <=> d = e)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`d`,`p`] mp_tac do_swap_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  qspecl_then [`e`,`q`] mp_tac do_swap_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  reverse eq_tac >- (strip_tac >> gvs[]) >> strip_tac >>
  qspecl_then [`d`,`p`] mp_tac do_swap_erased_spill_count >>
  qspecl_then [`e`,`q`] mp_tac do_swap_erased_spill_count >>
  simp[] >>
  Cases_on `d <= 16` >> Cases_on `e <= 16` >>
  Cases_on `d = 0` >> Cases_on `e = 0` >> gvs[]
QED

Theorem do_dup_erased_code_injective:
  !d e p q. d < LENGTH p.ps_stack /\ e < LENGTH q.ps_stack ==>
    ((MAP erase_spill_address (FST (do_dup d p)) =
      MAP erase_spill_address (FST (do_dup e q))) <=> d = e)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`d`,`p`] mp_tac do_dup_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  qspecl_then [`e`,`q`] mp_tac do_dup_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  reverse eq_tac >- (strip_tac >> gvs[]) >> strip_tac >>
  qspecl_then [`d`,`p`] mp_tac do_dup_erased_spill_count >>
  qspecl_then [`e`,`q`] mp_tac do_dup_erased_spill_count >>
  simp[] >> Cases_on `d <= 15` >> Cases_on `e <= 15` >> gvs[]
QED

Theorem do_swap_dup_erased_code_distinct:
  !d e p q. d < LENGTH p.ps_stack /\ e < LENGTH q.ps_stack ==>
    MAP erase_spill_address (FST (do_swap d p)) <>
    MAP erase_spill_address (FST (do_dup e q))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`d`,`p`] mp_tac do_swap_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  qspecl_then [`e`,`q`] mp_tac do_dup_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  `!n. ~MEM (SODup n) (MAP erase_spill_address (FST (do_swap d p)))`
    by (simp[] >> Cases_on `d = 0` >> Cases_on `d <= 16` >>
        simp[MEM_MAP, rich_listTheory.MEM_REPLICATE]) >>
  Cases_on `e <= 15`
  >- ( `MEM (SODup (e + 1))
          (MAP erase_spill_address (FST (do_dup e q)))` by simp[] >>
       metis_tac[]) >>
  `MEM (SODup 16) (MAP erase_spill_address (FST (do_dup e q)))`
    by simp[] >> metis_tac[]
QED

Theorem replicate_nonmatching_head_cancel[local]:
  !n m a b c xs ys.
    b <> a /\ c <> a ==>
    ((REPLICATE n a ++ (b::xs) = REPLICATE m a ++ (c::ys)) <=>
     n = m /\ b = c /\ xs = ys)
Proof
  Induct_on `n` >> Cases_on `m` >> simp[rich_listTheory.REPLICATE] >> gvs[]
QED

Theorem do_swap_erased_code_suffix_cancel:
  !d e p q xs ys.
    0 < d /\ 0 < e /\ d < LENGTH p.ps_stack /\ e < LENGTH q.ps_stack /\
    MAP erase_spill_address (FST (do_swap d p)) ++ xs =
    MAP erase_spill_address (FST (do_swap e q)) ++ ys ==>
    d = e /\ xs = ys
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`d`,`p`] mp_tac do_swap_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  qspecl_then [`e`,`q`] mp_tac do_swap_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  qpat_x_assum `_ ++ xs = _ ++ ys` mp_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `MAP _ (FST (do_swap d p)) = _` kall_tac >>
  qpat_x_assum `MAP _ (FST (do_swap e q)) = _` kall_tac >>
  Cases_on `d <= 16` >> Cases_on `e <= 16` >>
  simp[replicate_nonmatching_head_cancel, GSYM arithmeticTheory.ADD1,
       rich_listTheory.REPLICATE] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp_tac (srw_ss()) [replicate_nonmatching_head_cancel] >>
  strip_tac >> gvs[]
QED

Theorem do_dup_erased_code_suffix_cancel:
  !d e p q xs ys.
    d < LENGTH p.ps_stack /\ e < LENGTH q.ps_stack /\
    MAP erase_spill_address (FST (do_dup d p)) ++ xs =
    MAP erase_spill_address (FST (do_dup e q)) ++ ys ==>
    d = e /\ xs = ys
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`d`,`p`] mp_tac do_dup_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  qspecl_then [`e`,`q`] mp_tac do_dup_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  qpat_x_assum `_ ++ xs = _ ++ ys` mp_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `MAP _ (FST (do_dup d p)) = _` kall_tac >>
  qpat_x_assum `MAP _ (FST (do_dup e q)) = _` kall_tac >>
  Cases_on `d <= 15` >> Cases_on `e <= 15` >>
  Cases_on `d - 15` >> Cases_on `e - 15` >>
  simp[rich_listTheory.REPLICATE] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp_tac (srw_ss()) [replicate_nonmatching_head_cancel] >>
  strip_tac >> gvs[]
QED

Theorem do_swap_dup_erased_code_suffix_distinct:
  !d e p q xs ys.
    0 < d /\ d < LENGTH p.ps_stack /\ e < LENGTH q.ps_stack ==>
    MAP erase_spill_address (FST (do_swap d p)) ++ xs <>
    MAP erase_spill_address (FST (do_dup e q)) ++ ys
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`d`,`p`] mp_tac do_swap_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  qspecl_then [`e`,`q`] mp_tac do_dup_erased_code >>
  (impl_tac >- simp[]) >> disch_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `MAP _ (FST (do_swap d p)) = _` kall_tac >>
  qpat_x_assum `MAP _ (FST (do_dup e q)) = _` kall_tac >>
  Cases_on `d <= 16` >> Cases_on `e <= 15` >>
  Cases_on `e - 15` >>
  simp[GSYM arithmeticTheory.ADD1, rich_listTheory.REPLICATE] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp_tac (srw_ss()) [replicate_nonmatching_head_cancel] >> gvs[]
QED
