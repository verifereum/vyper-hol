(* Shared structural control facts. Their original qualified APIs are retained
   by the control-owner join; this lower theory has no control-owner import. *)
Theory symFrameControlFacts
Ancestors
  codegenSymRel symPlannerBase stackModel stackPlanOps planAlign
  doSwapSim spillPlanSim mixedPrefixSim unitShapeDefs dfgDefs asmSymSem asmSymBridge

(* Pointwise kind equivalence transports a typed symbolic stack. *)
Theorem list_rel_op_kind_transport:
  !xs vals ys fn ret.
    LIST_REL (op_kind_ok fn ret) xs vals /\
    LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                          op_kind_ok fn ret y sv) xs ys ==>
    LIST_REL (op_kind_ok fn ret) ys vals
Proof
  Induct >> Cases_on `vals` >> Cases_on `ys` >> simp[] >>
  metis_tac[]
QED

Theorem stack_poke_op_kind_equiv:
  d < LENGTH xs /\
  (!sv. op_kind_ok fn ret (stack_peek d xs) sv <=>
        op_kind_ok fn ret op sv) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv) xs (stack_poke d op xs)
Proof
  rw[listTheory.LIST_REL_EL_EQN, stackModelTheory.stack_poke_def,
     listTheory.EL_LUPDATE] >>
  gvs[stackModelTheory.stack_peek_def] >> metis_tac[]
QED

Theorem stack_exchange_op_kind_equiv:
  d < LENGTH xs /\ f < LENGTH xs /\
  op = stack_peek d xs /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f xs) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv)
    xs (stack_poke f op (stack_poke d (stack_peek f xs) xs))
Proof
  strip_tac >> drule_all symPlannerBaseTheory.op_kind_ok_operand_equiv >> strip_tac >>
  rw[listTheory.LIST_REL_EL_EQN, stackModelTheory.stack_poke_def,
     listTheory.EL_LUPDATE] >>
  gvs[stackModelTheory.stack_peek_def] >> metis_tac[]
QED

Theorem sym_kinds_ok_stack_transport:
  !cp fn ret srest ps ss xs.
  sym_kinds_ok cp fn ret srest ps ss /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv) ps.ps_stack xs ==>
  sym_kinds_ok cp fn ret srest (ps with ps_stack := xs) ss
Proof
  rw[sym_kinds_ok_def] >>
  qexists_tac `top` >> simp[] >>
  irule list_rel_op_kind_transport >> goal_assum (drule_at Any) >>
  simp[]
QED

Theorem sym_kinds_ok_reorder_relabel:
  !cp fn ret srest ps ss d f op dfg.
  sym_kinds_ok cp fn ret srest ps ss /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  op = stack_peek d ps.ps_stack /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) ==>
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := stack_poke f op
      (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack)) ss
Proof
  rpt gen_tac >> strip_tac >> irule sym_kinds_ok_stack_transport >>
  goal_assum (drule_at Any) >> irule stack_exchange_op_kind_equiv >>
  goal_assum (drule_at Any) >> gvs[]
QED

(* Restore interpretation agrees on the fields observed by symbolic kinds. *)
Theorem restore_spilled_plan_ss_align:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops, ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    !lo. (apply_prefix_ops initial_fmp lo ops ps).ps_stack = ps'.ps_stack /\
         (apply_prefix_ops initial_fmp lo ops ps).ps_spilled = ps'.ps_spilled
Proof
  Induct >> simp[stackPlanOpsTheory.restore_spilled_plan_def,
                 planAlignTheory.apply_prefix_ops_nil] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule doSwapSimTheory.spill_alloc_layout_wf_spilled_separated >> strip_tac >>
  drule_all spillPlanSimTheory.do_restore_layout_wf >> strip_tac >>
  drule_all planAlignTheory.do_restore_ss_align >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >> gen_tac >>
  simp[planAlignTheory.apply_prefix_ops_append] >>
  qspecl_then [`ops2`, `lo`] mp_tac
    mixedPrefixSimTheory.apply_prefix_ops_ext_stack_spilled >>
  metis_tac[]
QED

Theorem word_kind_concretization:
  MEM op ops /\ op_kind_ok fn ret op sv /\
  (!op sv. MEM op ops /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  sval_conc lo sv = SOME w ==> sv = Val w
Proof
  strip_tac >> `?v. sv = Val v` by metis_tac[] >> gvs[sval_conc_def]
QED

Theorem word_kind_prefix_concretization:
  !ops top values.
  LIST_REL (op_kind_ok fn ret) ops top /\
  (!op sv. MEM op ops /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w)
    (top ++ srest) (values ++ rest) /\ LENGTH values = LENGTH ops ==>
  top = MAP Val values
Proof
  Induct >> Cases_on `top` >> Cases_on `values` >>
  simp[] >> rpt strip_tac >>
  metis_tac[word_kind_concretization, listTheory.MEM]
QED
