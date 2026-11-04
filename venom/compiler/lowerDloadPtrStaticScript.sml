Theory lowerDloadPtrStatic
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline lowerDloadDefs
  venomPassSchedule list lowerDloadPtrClosure pointerConfinedDefs memLocDefs
  pred_set venomInst mem2varBlockSimHelpers irSupply venomFnScheduleRunner

(* A stage-level lifting boundary, also retaining the source membership
   required by consumers whose property depends on the input context. *)
Theorem lower_dload_stage_every:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  EVERY P C.ctx_functions /\
  (!f s g t. MEM f C.ctx_functions /\ P f /\
     lower_dload_function_supply s f = (g,t) ==> Q g) ==>
  EVERY Q C'.ctx_functions
Proof
  rw[ctx_pass_stage_def, EVERY_MEM, LIST_REL_EL_EQN, MEM_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  gvs[fn_pass_step_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem lower_dload_function_no_dalloca:
  lower_dload_function_supply s f = (g,t) /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts g)
Proof
  strip_tac >> irule lower_dload_function_supply_every >>
  conj_tac
  >- (rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
      metis_tac[lower_dload_inst_supply_kept_dalloca]) >>
  qexistsl [`f`,`s`,`t`] >> simp[]
QED

Theorem lower_dload_stage_no_dalloca:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  ~ctx_has_dalloca C ==> ~ctx_has_dalloca C'
Proof
  simp[ctx_has_dalloca_def, GSYM EVERY_NOT_EXISTS] >> strip_tac >>
  irule lower_dload_stage_every >>
  qexistsl [`C`,`\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)`,
            `rpolicy`,`view`] >>
  pure_rewrite_tac[combinTheory.o_DEF, GSYM EVERY_NOT_EXISTS] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all lower_dload_function_no_dalloca >>
      simp[combinTheory.o_DEF]) >>
  fs[EVERY_MEM, EXISTS_MEM, combinTheory.o_DEF] >> metis_tac[]
QED

(* Code offsets are not pointers, even when an operand is repeated in the
   destination position: the single-use clause excludes that case. *)
Theorem ptr_use_ok_dload_offsets:
  ptr_use_ok P pv i ==>
  (i.inst_opcode = DLOAD ==>
     !v. MEM (Var v) i.inst_operands ==> v NOTIN pv) /\
  (i.inst_opcode = DLOADBYTES ==>
     !dst src sz v. i.inst_operands = [dst; src; sz] /\ src = Var v ==>
       v NOTIN pv)
Proof
  simp[ptr_use_ok_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `v` mp_tac) >>
      gvs[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]) >>
  rpt strip_tac >> first_x_assum (qspec_then `v` mp_tac) >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  strip_tac >> gvs[] >> Cases_on `sz = Var v` >>
  Cases_on `dst = Var v` >> gvs[]
QED

Theorem FINITE_ptr_roots:
  FINITE (ptr_roots P fn)
Proof
  irule SUBSET_FINITE >>
  qexists_tac `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  simp[SUBSET_DEF, ptr_roots_def, alloca_roots_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  qexists_tac `inst.inst_outputs` >>
  gvs[inst_output_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem lower_dload_inst_supply_pointer_edge:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  is_pointer_preserving_op j.inst_opcode /\ MEM (Var v) j.inst_operands /\
  v IN pv /\ ptr_use_ok P pv i ==> j = i
Proof
  strip_tac >> drule ptr_use_ok_dload_offsets >> strip_tac >>
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      gvs[is_pointer_preserving_op_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      gvs[is_pointer_preserving_op_def] >> metis_tac[]) >>
  gvs[lower_dload_inst_supply_def]
QED

Theorem lower_dload_function_supply_pointer_edge:
  lower_dload_function_supply s f = (g,t) /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P pv i) /\
  MEM j (fn_insts g) /\ is_pointer_preserving_op j.inst_opcode /\
  MEM (Var v) j.inst_operands /\ v IN pv ==> MEM j (fn_insts f)
Proof
  strip_tac >> drule_all lower_dload_function_supply_member >> strip_tac >>
  `ptr_use_ok P pv i` by metis_tac[] >>
  drule_all lower_dload_inst_supply_pointer_edge >> strip_tac >> gvs[]
QED

Theorem lower_dload_insts_supply_retained:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) ==>
  !i. MEM i ins /\ i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES ==>
      MEM i xs
Proof
  Induct_on `ins` >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >- gvs[lower_dload_inst_supply_def] >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_retained:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) ==>
  !i. MEM i (fn_insts_blocks bbs) /\
      i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES ==>
      MEM i (fn_insts_blocks bs)
Proof
  Induct_on `bbs` >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs(), fn_insts_blocks_def] >> rpt strip_tac >> gvs[]
  >- (drule_all lower_dload_insts_supply_retained >> simp[fn_insts_blocks_def]) >>
  gvs[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem lower_dload_function_supply_retained:
  lower_dload_function_supply s f = (g,t) /\ MEM i (fn_insts f) /\
  i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES ==>
  MEM i (fn_insts g)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[lower_dload_blocks_supply_retained]
QED

(* With unchanged roots, no generated pointer edge can be reached.  This
   isolates the non-alloca-root case from scratch-root freshness. *)
Theorem lower_dload_function_supply_old_closure:
  lower_dload_function_supply s f = (g,t) /\ FINITE roots /\
  roots SUBSET ptr_roots P f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) ==>
  pointer_derived_vars g roots = pointer_derived_vars f roots
Proof
  strip_tac >>
  `pointer_derived_vars f roots SUBSET fn_pv P f` by
    (simp[fn_pv_def] >> irule pointer_derived_vars_mono >>
     simp[FINITE_ptr_roots]) >>
  simp[SET_EQ_SUBSET, SUBSET_DEF] >> conj_tac
  >- (ho_match_mp_tac pointer_derived_vars_induction >> simp[] >> conj_tac
      >- metis_tac[roots_in_pointer_derived_vars] >>
      rpt strip_tac >> rename1 `MEM (Var v) i.inst_operands` >>
      `v IN fn_pv P f` by metis_tac[SUBSET_DEF] >>
      `MEM i (fn_insts f)` by
        (drule_all lower_dload_function_supply_pointer_edge >> simp[]) >>
      metis_tac[pointer_derived_vars_edge]) >>
  ho_match_mp_tac pointer_derived_vars_induction >> simp[] >> conj_tac
  >- metis_tac[roots_in_pointer_derived_vars] >>
  rpt strip_tac >>
  `i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` by
    (Cases_on `i.inst_opcode` >> gvs[is_pointer_preserving_op_def]) >>
  `MEM i (fn_insts g)` by metis_tac[lower_dload_function_supply_retained] >>
  metis_tac[pointer_derived_vars_edge]
QED

Theorem lower_dload_inst_supply_reserved_alloca:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  j.inst_opcode = ALLOCA /\ inst_output j = SOME v /\
  MEM v s.irs_used_vars ==> j = i
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[inst_output_def] >>
      imp_res_tac fresh_ir_var_contract >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_insts_supply_reserved_alloca:
  !s xs t j v. lower_dload_insts_supply s ins = (xs,t) /\ MEM j xs /\
  j.inst_opcode = ALLOCA /\ inst_output j = SOME v /\
  MEM v s.irs_used_vars ==> MEM j ins
Proof
  Induct_on `ins` >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule_all lower_dload_inst_supply_reserved_alloca >> simp[]) >>
  drule lower_dload_inst_supply_preserves_vars >> strip_tac >>
  metis_tac[]
QED

Theorem lower_dload_blocks_supply_reserved_alloca:
  !s bs t j v. lower_dload_blocks_supply s bbs = (bs,t) /\
  MEM j (fn_insts_blocks bs) /\ j.inst_opcode = ALLOCA /\
  inst_output j = SOME v /\ MEM v s.irs_used_vars ==>
  MEM j (fn_insts_blocks bbs)
Proof
  Induct_on `bbs` >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[fn_insts_blocks_def]
  >- (drule_all lower_dload_insts_supply_reserved_alloca >> simp[]) >>
  drule (cj 1 lower_dload_insts_supply_reserved_operand) >> strip_tac >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_reserved_alloca:
  lower_dload_function_supply s f = (g,t) /\
  MEM j (fn_insts g) /\ j.inst_opcode = ALLOCA /\
  inst_output j = SOME v /\ MEM v s.irs_used_vars ==>
  MEM j (fn_insts f)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[lower_dload_blocks_supply_reserved_alloca]
QED

Theorem lower_dload_function_supply_scratch_fresh:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f ==>
  DISJOINT (alloca_roots g DIFF alloca_roots f) (set (fn_ir_vars f))
Proof
  simp[DISJOINT_DEF, EXTENSION, alloca_roots_def] >> rpt strip_tac >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
  metis_tac[lower_dload_function_supply_reserved_alloca]
QED

Theorem lower_dload_function_supply_alloca_roots:
  lower_dload_function_supply s f = (g,t) ==>
  alloca_roots f SUBSET alloca_roots g
Proof
  simp[alloca_roots_def, SUBSET_DEF] >> rpt strip_tac >>
  qexists_tac `inst` >> simp[] >>
  irule lower_dload_function_supply_retained >> simp[] >>
  qexistsl [`f`,`s`,`t`] >> simp[]
QED

Theorem lower_dload_function_supply_ptr_roots:
  lower_dload_function_supply s f = (g,t) ==>
  ptr_roots P g = ptr_roots P f UNION alloca_roots g
Proof
  strip_tac >>
  `g.fn_name = f.fn_name` by
    gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
  `alloca_roots f SUBSET alloca_roots g` by
    metis_tac[lower_dload_function_supply_alloca_roots] >>
  simp[ptr_roots_def, EXTENSION] >> gen_tac >> eq_tac
  >- (strip_tac >> simp[]
      >- (drule_all lower_dload_function_supply_member >> strip_tac >>
          `inst = i` by metis_tac[lower_dload_inst_supply_kept_dalloca] >>
          gvs[] >> metis_tac[])
      >- (metis_tac[lower_dload_function_supply_control, MEM])) >>
  strip_tac >> simp[]
  >- metis_tac[SUBSET_DEF]
  >- (disj1_tac >> disj2_tac >> qexists_tac `inst` >> simp[] >>
      irule lower_dload_function_supply_retained >> simp[] >>
      qexistsl [`f`,`s`,`t`] >> simp[]) >>
  disj2_tac >> qexistsl [`inst`,`idx`] >> simp[] >>
  irule lower_dload_function_supply_retained >> simp[] >>
  qexistsl [`f`,`s`,`t`] >> simp[]
QED
