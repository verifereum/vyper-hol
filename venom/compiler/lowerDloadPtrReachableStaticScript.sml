Theory lowerDloadPtrReachableStatic
Ancestors
  lowerDloadPtrStatic o1ContractLowerDload unitShapeDefs lowerDloadDefs
  irSupply list venomFnScheduleRunner venomFnScheduleRunnerProps
  ptrDiscipline pointerConfinedDefs pred_set venomInst passSharedDefs
  lowerDloadPtrClosure mem2varBlockSimHelpers o1PassContract

Theorem lower_dload_blocks_supply_location_covered:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) /\
    MEM bg bs /\ MEM j bg.bb_instructions /\
    EVERY (\v. MEM v s.irs_used_vars) reserved ==>
  ?bf i u ys w. MEM bf bbs /\ bf.bb_label = bg.bb_label /\
    MEM i bf.bb_instructions /\ lower_dload_inst_supply u i = (ys,w) /\
    MEM j ys /\ EVERY (\v. MEM v u.irs_used_vars) reserved /\
    EVERY (\k. MEM k bg.bb_instructions) ys
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (drule_all lower_dload_insts_supply_member_covered >> strip_tac >>
      qexistsl [`h`,`i`,`u`,`ys`,`w`] >> simp[]) >>
  drule (cj 1 lower_dload_insts_supply_reserved_operand) >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars) reserved` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`bf`,`i`,`u`,`ys`,`w`] >> simp[]
QED

Theorem lower_dload_function_supply_location_covered:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  MEM bg g.fn_blocks /\ MEM j bg.bb_instructions ==>
  ?bf i u ys w. MEM bf f.fn_blocks /\ bf.bb_label = bg.bb_label /\
    MEM i bf.bb_instructions /\ lower_dload_inst_supply u i = (ys,w) /\
    MEM j ys /\ EVERY (\v. MEM v u.irs_used_vars) (fn_ir_vars f) /\
    EVERY (\k. MEM k bg.bb_instructions) ys
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `EVERY (\v. MEM v s.irs_used_vars) (fn_ir_vars f)` by
    gvs[ir_supply_covers_fn_def, list_subset_def] >>
  drule_all lower_dload_blocks_supply_location_covered >> simp[]
QED

Theorem lower_dload_function_supply_reachable_covered:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  MEM j (fn_insts (reachable_fn g)) ==>
  ?lbl i u ys w.
    MEM (reachable_inst f lbl i) (fn_insts (reachable_fn f)) /\
    lower_dload_inst_supply u i = (ys,w) /\
    MEM j (MAP (reachable_inst f lbl) ys) /\
    EVERY (\v. MEM v u.irs_used_vars) (fn_ir_vars f) /\
    EVERY (\k. MEM k (fn_insts (reachable_fn g)))
      (MAP (reachable_inst f lbl) ys)
Proof
  strip_tac >>
  drule lower_dload_function_supply_reachable >> strip_tac >>
  drule lower_dload_function_supply_reachable_inst >> strip_tac >>
  qpat_x_assum `MEM j _` mp_tac >> rewrite_tac[MEM_reachable_fn_insts] >>
  strip_tac >> gvs[] >>
  rename1 `MEM raw bg.bb_instructions` >>
  drule_all lower_dload_function_supply_location_covered >> strip_tac >>
  rename1 `lower_dload_inst_supply u orig = (ys,w)` >>
  qexistsl [`bg.bb_label`,`orig`,`u`,`ys`,`w`] >>
  simp[MEM_MAP, EVERY_MAP, EVERY_MEM] >> conj_tac
  >- (simp[MEM_reachable_fn_insts] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> simp[MEM_reachable_fn_insts] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_retained_at:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) /\
    MEM bf bbs /\ MEM i bf.bb_instructions /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES ==>
  ?bg. MEM bg bs /\ bg.bb_label = bf.bb_label /\ MEM i bg.bb_instructions
Proof
  Induct_on `bbs` >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (drule_all lowerDloadPtrStaticTheory.lower_dload_insts_supply_retained >> strip_tac >>
      qexists_tac `bf with bb_instructions := insts` >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem lower_dload_function_supply_retained_at:
  lower_dload_function_supply s f = (g,t) /\
  MEM bf f.fn_blocks /\ MEM i bf.bb_instructions /\
  i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES ==>
  ?bg. MEM bg g.fn_blocks /\ bg.bb_label = bf.bb_label /\ MEM i bg.bb_instructions
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all lower_dload_blocks_supply_retained_at >> simp[]
QED

Theorem lower_dload_function_supply_reachable_retained:
  lower_dload_function_supply s f = (g,t) /\
  MEM i (fn_insts (reachable_fn f)) /\
  i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES ==>
  MEM i (fn_insts (reachable_fn g))
Proof
  strip_tac >>
  drule lower_dload_function_supply_reachable >> strip_tac >>
  drule lower_dload_function_supply_reachable_inst >> strip_tac >>
  qpat_x_assum `MEM i _` mp_tac >> rewrite_tac[MEM_reachable_fn_insts] >>
  strip_tac >> gvs[] >>
  `i'.inst_opcode <> DLOAD /\ i'.inst_opcode <> DLOADBYTES` by
    metis_tac[reachable_inst_fields] >>
  drule_all lower_dload_function_supply_retained_at >> strip_tac >>
  simp[MEM_reachable_fn_insts] >> metis_tac[]
QED

(* PHI filtering commutes with one actual expansion, not with restarting
   the supply on a filtered function. *)
Theorem lower_dload_inst_supply_reachable_inst:
  lower_dload_inst_supply s i = (xs,t) ==>
  lower_dload_inst_supply s (reachable_inst f lbl i) =
    (MAP (reachable_inst f lbl) xs,t)
Proof
  Cases_on `i.inst_opcode = PHI`
  >- (simp[lower_dload_inst_supply_def] >> strip_tac >>
      gvs[reachable_inst_def, lower_dload_inst_supply_def]) >>
  Cases_on `i.inst_opcode = DLOAD`
  >- (simp[lower_dload_inst_supply_def, reachable_inst_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[reachable_inst_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (simp[lower_dload_inst_supply_def, reachable_inst_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[reachable_inst_def]) >>
  simp[lower_dload_inst_supply_def, reachable_inst_def] >>
  strip_tac >> gvs[reachable_inst_def]
QED

Theorem lower_dload_reachable_alloca_roots:
  lower_dload_function_supply s f = (g,t) ==>
  alloca_roots (reachable_fn f) SUBSET alloca_roots (reachable_fn g)
Proof
  simp[alloca_roots_def, SUBSET_DEF] >> rpt strip_tac >>
  qexists_tac `inst` >> simp[] >>
  irule lower_dload_function_supply_reachable_retained >> simp[] >>
  qexistsl [`f`,`s`,`t`] >> simp[]
QED

Theorem lower_dload_reachable_scratch_fresh:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f ==>
  DISJOINT (alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f))
    (set (fn_ir_vars f))
Proof
  strip_tac >> simp[DISJOINT_DEF, EXTENSION, alloca_roots_def] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >> gvs[] >>
  drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
  `MEM x u.irs_used_vars` by gvs[EVERY_MEM] >>
  qpat_x_assum `MEM inst (MAP _ _)` mp_tac >> pure_rewrite_tac[MEM_MAP] >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  `raw.inst_opcode <> MLOAD /\ inst_output raw = SOME x` by
    gvs[inst_output_def, reachable_inst_fields, AllCaseEqs()] >>
  drule_all lowerDloadPtrStaticTheory.lower_dload_inst_supply_reserved_output >>
  strip_tac >> gvs[reachable_inst_fields] >> metis_tac[reachable_inst_fields]
QED

Theorem lower_dload_reachable_ptr_roots:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f ==>
  ptr_roots P (reachable_fn g) = ptr_roots P (reachable_fn f) UNION
    (alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f))
Proof
  strip_tac >>
  `g.fn_name = f.fn_name` by
    gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
  drule lower_dload_reachable_alloca_roots >> strip_tac >>
  `(reachable_fn g).fn_name = (reachable_fn f).fn_name` by
    simp[reachable_fn_def] >>
  simp[ptr_roots_def, EXTENSION] >> gen_tac >> eq_tac
  >- (strip_tac
      >- metis_tac[SUBSET_DEF]
      >- (drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
          drule lower_dload_inst_supply_reachable_inst >>
          disch_then (qspecl_then [`lbl`,`f`] assume_tac) >>
          `inst = reachable_inst f lbl i` by
            metis_tac[lower_dload_inst_supply_kept_dalloca] >>
          gvs[] >> metis_tac[])
      >- (drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
          drule lower_dload_inst_supply_reachable_inst >>
          disch_then (qspecl_then [`lbl`,`f`] assume_tac) >>
          `inst = reachable_inst f lbl i` by
            metis_tac[lower_dload_inst_supply_control, MEM] >>
          gvs[] >> metis_tac[])) >>
  strip_tac
  >- metis_tac[SUBSET_DEF]
  >- (disj1_tac >> disj2_tac >> qexists_tac `inst` >> simp[] >>
      irule lower_dload_function_supply_reachable_retained >> simp[] >>
      qexistsl [`f`,`s`,`t`] >> simp[])
  >- (disj2_tac >> qexistsl [`inst`,`idx`] >> simp[] >>
      irule lower_dload_function_supply_reachable_retained >> simp[] >>
      qexistsl [`f`,`s`,`t`] >> simp[]) >>
  simp[]
QED

Theorem reachable_fn_ir_vars_subset:
  set (fn_ir_vars (reachable_fn f)) SUBSET set (fn_ir_vars f)
Proof
  simp[SUBSET_DEF, fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS, reachable_fn_def, MEM_FILTER] >>
  rpt strip_tac >> gvs[inst_ir_vars_def, inst_uses_def, MEM_operand_vars_eq_Var,
                        reachable_inst_fields] >>
  metis_tac[reachable_inst_fields]
QED

Theorem lower_dload_reachable_nonalloca_roots:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f ==>
  ptr_roots P (reachable_fn g) DIFF alloca_roots (reachable_fn g) =
  ptr_roots P (reachable_fn f) DIFF alloca_roots (reachable_fn f)
Proof
  strip_tac >>
  drule_all lower_dload_reachable_ptr_roots >> strip_tac >>
  drule lower_dload_reachable_alloca_roots >> strip_tac >>
  drule_all lower_dload_reachable_scratch_fresh >> strip_tac >>
  `ptr_roots P (reachable_fn f) SUBSET set (fn_ir_vars (reachable_fn f))` by
    simp[ptr_roots_ir_vars] >>
  `set (fn_ir_vars (reachable_fn f)) SUBSET set (fn_ir_vars f)` by
    simp[reachable_fn_ir_vars_subset] >>
  gvs[EXTENSION, SUBSET_DEF, DISJOINT_DEF] >> metis_tac[]
QED

Theorem reachable_fn_pv_ir_vars:
  fn_pv P (reachable_fn f) SUBSET set (fn_ir_vars f)
Proof
  irule SUBSET_TRANS >> qexists_tac `set (fn_ir_vars (reachable_fn f))` >>
  simp[fn_pv_ir_vars, reachable_fn_ir_vars_subset]
QED

Theorem lower_dload_reachable_pointer_operand:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  MEM j (fn_insts (reachable_fn g)) /\
  is_pointer_preserving_op j.inst_opcode /\ MEM (Var v) j.inst_operands ==>
  MEM v (fn_ir_vars f)
Proof
  strip_tac >> drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
  drule lower_dload_inst_supply_reachable_inst >>
  disch_then (qspecl_then [`lbl`,`f`] assume_tac) >>
  `MEM (Var v) (reachable_inst f lbl i).inst_operands` by
    metis_tac[lower_dload_inst_supply_pointer_operand] >>
  `MEM v (fn_ir_vars (reachable_fn f))` by metis_tac[fn_ir_vars_operand] >>
  `set (fn_ir_vars (reachable_fn f)) SUBSET set (fn_ir_vars f)` by
    simp[reachable_fn_ir_vars_subset] >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem lower_dload_reachable_pointer_edge:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\
  MEM j (fn_insts (reachable_fn g)) /\
  is_pointer_preserving_op j.inst_opcode /\ MEM (Var v) j.inst_operands /\
  v IN fn_pv P (reachable_fn f) ==>
  MEM j (fn_insts (reachable_fn f))
Proof
  strip_tac >> drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
  drule lower_dload_inst_supply_reachable_inst >>
  disch_then (qspecl_then [`lbl`,`f`] assume_tac) >>
  `ptr_use_ok P (fn_pv P (reachable_fn f)) (reachable_inst f lbl i)` by
    metis_tac[] >>
  `j = reachable_inst f lbl i` by metis_tac[lower_dload_inst_supply_pointer_edge] >>
  gvs[]
QED

Theorem lower_dload_reachable_roots_closure:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\
  FINITE roots /\ roots SUBSET ptr_roots P (reachable_fn f) /\
  extra SUBSET (alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f)) ==>
  pointer_derived_vars (reachable_fn g) (roots UNION extra) =
    pointer_derived_vars (reachable_fn f) roots UNION extra
Proof
  strip_tac >>
  drule_all lower_dload_reachable_scratch_fresh >> strip_tac >>
  `FINITE (alloca_roots (reachable_fn g))` by
    (irule SUBSET_FINITE >> qexists_tac `ptr_roots P (reachable_fn g)` >>
     simp[FINITE_ptr_roots, ptr_roots_def, SUBSET_DEF]) >>
  `FINITE extra` by
    (irule SUBSET_FINITE >>
     qexists_tac `alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f)` >>
     simp[]) >>
  `pointer_derived_vars (reachable_fn f) roots SUBSET fn_pv P (reachable_fn f)` by
    (simp[fn_pv_def] >> irule pointer_derived_vars_mono >> simp[FINITE_ptr_roots]) >>
  simp[SET_EQ_SUBSET, SUBSET_DEF] >> conj_tac
  >- (ho_match_mp_tac pointer_derived_vars_induction >> simp[] >> conj_tac
      >- metis_tac[roots_in_pointer_derived_vars] >>
      rpt strip_tac >> rename1 `MEM (Var v) i.inst_operands` >>
      `MEM v (fn_ir_vars f)` by metis_tac[lower_dload_reachable_pointer_operand] >>
      `~(v IN extra)` by (gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
      `v IN fn_pv P (reachable_fn f)` by metis_tac[SUBSET_DEF] >>
      `MEM i (fn_insts (reachable_fn f))` by
        metis_tac[lower_dload_reachable_pointer_edge] >>
      metis_tac[pointer_derived_vars_edge]) >>
  rpt strip_tac
  >- (pop_assum mp_tac >> qid_spec_tac `x` >>
      ho_match_mp_tac pointer_derived_vars_induction >> simp[] >> conj_tac
      >- (rpt strip_tac >> irule roots_in_pointer_derived_vars >> simp[]) >>
      rpt strip_tac >>
      `i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` by
        (Cases_on `i.inst_opcode` >> gvs[is_pointer_preserving_op_def]) >>
      `MEM i (fn_insts (reachable_fn g))` by
        metis_tac[lower_dload_function_supply_reachable_retained] >>
      irule pointer_derived_vars_edge >> simp[] >>
      qexistsl [`i`,`x`] >> simp[]) >>
  irule roots_in_pointer_derived_vars >> simp[]
QED

Theorem lower_dload_reachable_fn_pv:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) ==>
  fn_pv P (reachable_fn g) = fn_pv P (reachable_fn f) UNION
    (alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f))
Proof
  strip_tac >> drule_all lower_dload_reachable_ptr_roots >> strip_tac >>
  simp[fn_pv_def] >> irule lower_dload_reachable_roots_closure >>
  simp[FINITE_ptr_roots] >> conj_tac
  >- (qexists_tac `P` >> simp[]) >>
  qexistsl [`s`,`t`] >> simp[]
QED

Theorem lower_dload_reachable_alloca_closure:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) ==>
  pointer_derived_vars (reachable_fn g) (alloca_roots (reachable_fn g)) =
  pointer_derived_vars (reachable_fn f) (alloca_roots (reachable_fn f)) UNION
    (alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f))
Proof
  strip_tac >> drule lower_dload_reachable_alloca_roots >> strip_tac >>
  `alloca_roots (reachable_fn f) SUBSET ptr_roots P (reachable_fn f)` by
    simp[ptr_roots_def, SUBSET_DEF] >>
  `FINITE (alloca_roots (reachable_fn f))` by metis_tac[SUBSET_FINITE, FINITE_ptr_roots] >>
  `alloca_roots (reachable_fn g) = alloca_roots (reachable_fn f) UNION
      (alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f))` by
    (gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  drule lower_dload_reachable_roots_closure >>
  disch_then (qspecl_then [`alloca_roots (reachable_fn f)`,
    `alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f)`,`P`] mp_tac) >>
  impl_tac >- simp[] >> metis_tac[]
QED

Theorem lower_dload_reachable_nonalloca_closure:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) ==>
  pointer_derived_vars (reachable_fn g)
    (ptr_roots P (reachable_fn g) DIFF alloca_roots (reachable_fn g)) =
  pointer_derived_vars (reachable_fn f)
    (ptr_roots P (reachable_fn f) DIFF alloca_roots (reachable_fn f))
Proof
  strip_tac >> drule_all lower_dload_reachable_nonalloca_roots >> strip_tac >>
  simp[] >>
  `pointer_derived_vars (reachable_fn g)
     ((ptr_roots P (reachable_fn f) DIFF alloca_roots (reachable_fn f)) UNION {}) =
   pointer_derived_vars (reachable_fn f)
     (ptr_roots P (reachable_fn f) DIFF alloca_roots (reachable_fn f)) UNION {}` suffices_by simp[] >>
  irule lower_dload_reachable_roots_closure >>
  simp[FINITE_ptr_roots] >> conj_tac
  >- (qexists_tac `P` >> simp[SUBSET_DEF]) >>
  qexistsl [`s`,`t`] >> simp[]
QED

Theorem lower_dload_reachable_old_pv:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\ MEM v (fn_ir_vars f) ==>
  (v IN fn_pv P (reachable_fn g) <=> v IN fn_pv P (reachable_fn f))
Proof
  strip_tac >> drule_all lower_dload_reachable_fn_pv >> strip_tac >>
  drule_all lower_dload_reachable_scratch_fresh >> strip_tac >>
  gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem lower_dload_reachable_old_ptr_use:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\
  MEM i (fn_insts (reachable_fn f)) ==>
  ptr_use_ok P (fn_pv P (reachable_fn g)) i
Proof
  strip_tac >>
  `!v. MEM (Var v) i.inst_operands ==>
       (v IN fn_pv P (reachable_fn f) <=> v IN fn_pv P (reachable_fn g))` by
    metis_tac[lower_dload_reachable_old_pv, fn_ir_vars_operand,
              reachable_fn_ir_vars_subset, SUBSET_DEF] >>
  drule ptr_use_ok_cong >> metis_tac[]
QED

Theorem lower_dload_reachable_fresh_nonalloca_pv:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\
  MEM j (fn_insts (reachable_fn g)) /\ j.inst_opcode <> ALLOCA /\
  MEM v j.inst_outputs /\ ~MEM v (fn_ir_vars f) ==>
  v NOTIN fn_pv P (reachable_fn g)
Proof
  strip_tac >> drule_all lower_dload_reachable_fn_pv >> strip_tac >>
  `v NOTIN alloca_roots g` by
    (qpat_assum `MEM j _` mp_tac >> rewrite_tac[MEM_reachable_fn_insts] >>
     strip_tac >> gvs[] >>
     irule lower_dload_function_supply_nonalloca_output >>
     conj_tac
     >- (qexists_tac `i` >>
         gvs[reachable_inst_fields, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
     qexistsl [`f`,`s`,`t`] >> simp[]) >>
  `v NOTIN alloca_roots (reachable_fn g)` by
    (qpat_x_assum `v NOTIN alloca_roots g` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[alloca_roots_def, MEM_reachable_fn_insts] >>
     rpt strip_tac >> gvs[reachable_inst_fields, inst_output_def, AllCaseEqs(),
                         fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[] >> metis_tac[reachable_fn_pv_ir_vars, SUBSET_DEF]
QED

Theorem lower_dload_reachable_ptr_use:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\
  MEM j (fn_insts (reachable_fn g)) ==>
  ptr_use_ok P (fn_pv P (reachable_fn g)) j
Proof
  strip_tac >> drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
  drule lower_dload_inst_supply_reachable_inst >>
  disch_then (qspecl_then [`lbl`,`f`] assume_tac) >>
  `ptr_use_ok P (fn_pv P (reachable_fn g)) (reachable_inst f lbl i)` by
    metis_tac[lower_dload_reachable_old_ptr_use] >>
  Cases_on `i.inst_opcode = DLOAD \/ i.inst_opcode = DLOADBYTES`
  >- (`!k v. MEM k (MAP (reachable_inst f lbl) ys) /\
          k.inst_opcode = ADD /\ MEM v k.inst_outputs ==>
          v NOTIN fn_pv P (reachable_fn g)` by
        (rpt gen_tac >> strip_tac >>
         `inst_output k = SOME v` by
           metis_tac[lower_dload_inst_supply_add_output, reachable_inst_fields] >>
         `~MEM v (fn_ir_vars f)` by
           (strip_tac >>
            `MEM v u.irs_used_vars` by gvs[EVERY_MEM] >>
            `k = reachable_inst f lbl i` by
              (irule lowerDloadPtrStaticTheory.lower_dload_inst_supply_reserved_output >>
               simp[] >> goal_assum (drule_at Any) >> simp[]) >>
            gvs[reachable_inst_fields]) >>
         irule lower_dload_reachable_fresh_nonalloca_pv >>
         conj_tac
         >- (qexists_tac `k` >> gvs[EVERY_MEM]) >>
         qexistsl [`f`,`s`,`t`] >> simp[]) >>
      drule_all lower_dload_inst_supply_ptr_use >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  `j = reachable_inst f lbl i` by
    (gvs[lower_dload_inst_supply_def] >> metis_tac[]) >> gvs[]
QED

Theorem lower_dload_reachable_pointer_operand_pv:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\
  MEM i (fn_insts (reachable_fn g)) /\ is_pointer_preserving_op i.inst_opcode /\
  MEM (Var v) i.inst_operands ==>
  (v IN fn_pv P (reachable_fn g) <=> v IN fn_pv P (reachable_fn f))
Proof
  strip_tac >> irule lower_dload_reachable_old_pv >> simp[] >>
  conj_tac >- metis_tac[lower_dload_reachable_pointer_operand] >>
  qexistsl [`s`,`t`] >> simp[]
QED

Theorem lower_dload_reachable_affine:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\
  affine_pointer_ops (reachable_fn f) (ptr_roots P (reachable_fn f)) ==>
  affine_pointer_ops (reachable_fn g) (ptr_roots P (reachable_fn g))
Proof
  strip_tac >>
  `!i v. MEM i (fn_insts (reachable_fn g)) /\ is_pointer_preserving_op i.inst_opcode /\
      MEM (Var v) i.inst_operands ==>
      (v IN fn_pv P (reachable_fn g) <=> v IN fn_pv P (reachable_fn f))` by
    metis_tac[lower_dload_reachable_pointer_operand_pv] >>
  gvs[affine_pointer_ops_def, GSYM fn_pv_def] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `MEM inst (fn_insts (reachable_fn g))` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `is_pointer_preserving_op inst.inst_opcode` by simp[is_pointer_preserving_op_def] >>
  `MEM inst (fn_insts (reachable_fn f))` by
    (irule lower_dload_reachable_pointer_edge >> simp[] >> conj_tac
     >- (qexists_tac `P` >> simp[] >> gvs[] >> metis_tac[MEM]) >>
     qexistsl [`g`,`s`,`t`] >> simp[]) >>
  gvs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM]
QED

Theorem lower_dload_reachable_phi:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts (reachable_fn f)) ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i) /\
  phi_pv_all_var (reachable_fn f) (ptr_roots P (reachable_fn f)) ==>
  phi_pv_all_var (reachable_fn g) (ptr_roots P (reachable_fn g))
Proof
  strip_tac >>
  `!i v. MEM i (fn_insts (reachable_fn g)) /\ is_pointer_preserving_op i.inst_opcode /\
      MEM (Var v) i.inst_operands ==>
      (v IN fn_pv P (reachable_fn g) <=> v IN fn_pv P (reachable_fn f))` by
    metis_tac[lower_dload_reachable_pointer_operand_pv] >>
  gvs[phi_pv_all_var_def, GSYM fn_pv_def] >> rpt strip_tac >>
  `MEM inst (fn_insts (reachable_fn g))` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `is_pointer_preserving_op inst.inst_opcode` by simp[is_pointer_preserving_op_def] >>
  `MEM inst (fn_insts (reachable_fn f))` by
    (irule lower_dload_reachable_pointer_edge >> simp[] >> conj_tac
     >- (qexists_tac `P` >> simp[] >> metis_tac[]) >>
     qexistsl [`g`,`s`,`t`] >> simp[]) >>
  gvs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem lower_dload_reachable_no_mixed_write:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_ptr_ok P (reachable_fn f) ==>
  !j ops v. MEM j (fn_insts (reachable_fn g)) /\ mem_write_ops j = SOME ops /\
    ops.iao_ofst = Var v ==>
    ~(v IN pointer_derived_vars (reachable_fn g) (alloca_roots (reachable_fn g)) /\
      v IN pointer_derived_vars (reachable_fn g)
        (ptr_roots P (reachable_fn g) DIFF alloca_roots (reachable_fn g)))
Proof
  rpt gen_tac >> strip_tac >>
  `!i. MEM i (fn_insts (reachable_fn f)) ==> ptr_use_ok P (fn_pv P (reachable_fn f)) i` by
    gvs[fn_ptr_ok_def] >>
  drule_all lower_dload_reachable_alloca_closure >> strip_tac >>
  drule_all lower_dload_reachable_nonalloca_closure >> strip_tac >>
  drule_all lower_dload_reachable_scratch_fresh >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  `v IN fn_pv P (reachable_fn f)` by
    (simp[fn_pv_def] >>
     `pointer_derived_vars (reachable_fn f)
        (ptr_roots P (reachable_fn f) DIFF alloca_roots (reachable_fn f))
       SUBSET pointer_derived_vars (reachable_fn f) (ptr_roots P (reachable_fn f))` by
       (irule pointer_derived_vars_mono >> simp[FINITE_ptr_roots, SUBSET_DEF]) >>
     gvs[SUBSET_DEF]) >>
  `MEM v (fn_ir_vars f)` by metis_tac[reachable_fn_pv_ir_vars, SUBSET_DEF] >>
  `v NOTIN (alloca_roots (reachable_fn g) DIFF alloca_roots (reachable_fn f))` by
    (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
  drule lower_dload_inst_supply_reachable_inst >>
  disch_then (qspecl_then [`lbl`,`f`] assume_tac) >>
  `MEM v u.irs_used_vars` by gvs[EVERY_MEM] >>
  drule_all lower_dload_inst_supply_reserved_write >> strip_tac >>
  gvs[fn_ptr_ok_def] >> metis_tac[]
QED

Theorem lower_dload_reachable_definition_closure:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_ptr_ok P (reachable_fn f) ==>
  !j v. MEM j (fn_insts (reachable_fn g)) /\ MEM v j.inst_outputs /\
    v IN fn_pv P (reachable_fn g) ==>
    j.inst_opcode = ALLOCA \/
    ((j.inst_opcode = DALLOCA \/
      (j.inst_opcode = PARAM /\
       ?idx. j.inst_operands = [Lit idx] /\ w2n idx IN P (reachable_fn g).fn_name)) /\
      v NOTIN alloca_roots (reachable_fn g)) \/
    (is_pointer_preserving_op j.inst_opcode /\
     ?u. MEM (Var u) j.inst_operands /\ u IN fn_pv P (reachable_fn g))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `j.inst_opcode = ALLOCA` >- simp[] >>
  `!i. MEM i (fn_insts (reachable_fn f)) ==> ptr_use_ok P (fn_pv P (reachable_fn f)) i` by
    gvs[fn_ptr_ok_def] >>
  `MEM v (fn_ir_vars f)` by
    (spose_not_then assume_tac >>
     drule_all lower_dload_reachable_fresh_nonalloca_pv >> simp[]) >>
  `v IN fn_pv P (reachable_fn f)` by metis_tac[lower_dload_reachable_old_pv] >>
  `(reachable_fn g).fn_name = (reachable_fn f).fn_name` by
    gvs[lower_dload_function_supply_def, reachable_fn_def, AllCaseEqs()] >>
  `!x. MEM x (fn_ir_vars f) ==>
     (x IN fn_pv P (reachable_fn g) <=> x IN fn_pv P (reachable_fn f))` by
    metis_tac[lower_dload_reachable_old_pv] >>
  `v NOTIN alloca_roots (reachable_fn f) ==> v NOTIN alloca_roots (reachable_fn g)` by
    (drule_all lower_dload_reachable_scratch_fresh >>
     simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
  drule lower_dload_inst_supply_reachable_inst >>
  disch_then (qspecl_then [`lbl`,`f`] assume_tac) >>
  `MEM v u.irs_used_vars` by gvs[EVERY_MEM] >>
  `!x. MEM (Var x) (reachable_inst f lbl i).inst_operands ==>
     (x IN fn_pv P (reachable_fn g) <=> x IN fn_pv P (reachable_fn f))` by
    metis_tac[fn_ir_vars_operand, reachable_fn_ir_vars_subset, SUBSET_DEF] >>
  `!x. MEM x (reachable_inst f lbl i).inst_outputs /\ x IN fn_pv P (reachable_fn f) ==>
     (reachable_inst f lbl i).inst_opcode = ALLOCA \/
     (((reachable_inst f lbl i).inst_opcode = DALLOCA \/
       ((reachable_inst f lbl i).inst_opcode = PARAM /\
        ?idx. (reachable_inst f lbl i).inst_operands = [Lit idx] /\
          w2n idx IN P (reachable_fn f).fn_name)) /\
       x NOTIN alloca_roots (reachable_fn f)) \/
     (is_pointer_preserving_op (reachable_inst f lbl i).inst_opcode /\
       ?a. MEM (Var a) (reachable_inst f lbl i).inst_operands /\
           a IN fn_pv P (reachable_fn f))` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOAD \/ i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, reachable_inst_fields, AllCaseEqs(), fresh_inst_id_def] >>
      imp_res_tac fresh_ir_var_contract >>
      gvs[is_pointer_preserving_op_def] >> metis_tac[]) >>
  `j = reachable_inst f lbl i` by
    (gvs[lower_dload_inst_supply_def] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem lower_dload_reachable_fn_ptr_ok:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_ptr_ok P (reachable_fn f) ==> fn_ptr_ok P (reachable_fn g)
Proof
  strip_tac >>
  `!i. MEM i (fn_insts (reachable_fn f)) ==> ptr_use_ok P (fn_pv P (reachable_fn f)) i` by
    gvs[fn_ptr_ok_def] >>
  `!i v. MEM i (fn_insts (reachable_fn f)) /\ MEM (Var v) i.inst_operands ==>
     (v IN fn_pv P (reachable_fn g) <=> v IN fn_pv P (reachable_fn f))` by
    metis_tac[lower_dload_reachable_old_pv, fn_ir_vars_operand,
              reachable_fn_ir_vars_subset, SUBSET_DEF] >>
  `!i. MEM i (fn_insts (reachable_fn f)) ==> ptr_use_ok P (fn_pv P (reachable_fn g)) i` by
    metis_tac[lower_dload_reachable_old_ptr_use] >>
  `(reachable_fn g).fn_forced_alloc_positions = (reachable_fn f).fn_forced_alloc_positions` by
    gvs[lower_dload_function_supply_def, reachable_fn_def, AllCaseEqs()] >>
  simp[fn_ptr_ok_def] >> rpt conj_tac
  >- gvs[fn_ptr_ok_def]
  >- (rpt gen_tac >> strip_tac >> rename1 `MEM j (fn_insts (reachable_fn g))` >>
      `ptr_use_ok P (fn_pv P (reachable_fn g)) j` by
        metis_tac[lower_dload_reachable_ptr_use] >>
      drule_all lower_dload_function_supply_reachable_covered >> strip_tac >>
      drule lower_dload_inst_supply_reachable_inst >>
      disch_then (qspecl_then [`lbl`,`f`] assume_tac) >>
      simp[] >> irule lower_dload_inst_supply_static_clauses >>
      qexists_tac `P` >>
      qpat_assum `lower_dload_inst_supply u (reachable_inst f lbl i) = _` (irule_at Any) >>
      gvs[fn_ptr_ok_def] >> metis_tac[])
  >- (irule lower_dload_reachable_affine >>
      qexistsl [`f`,`s`,`t`] >> gvs[fn_ptr_ok_def])
  >- (irule lower_dload_reachable_phi >>
      qexistsl [`f`,`s`,`t`] >> gvs[fn_ptr_ok_def])
  >- (rpt gen_tac >> strip_tac >>
      drule_all lower_dload_reachable_no_mixed_write >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all lower_dload_reachable_definition_closure >> simp[]
QED

Theorem lower_dload_stage_static_ptr_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn)) C.ctx_functions ==>
  EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn)) C'.ctx_functions
Proof
  strip_tac >> irule lower_dload_stage_every_covered >>
  qexistsl [`C`,`\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn)`,`rpolicy`,`view`] >>
  simp[] >> metis_tac[lower_dload_function_supply_fn_ptr_ok, lower_dload_reachable_fn_ptr_ok]
QED
