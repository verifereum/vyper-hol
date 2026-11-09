Theory lowerDloadPtrStatic
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline lowerDloadDefs
  venomPassSchedule list lowerDloadPtrClosure pointerConfinedDefs memLocDefs
  pred_set venomInst mem2varBlockSimHelpers irSupply venomFnScheduleRunner
  venomExecSemantics venomFnScheduleRunnerProps

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

Theorem lower_dload_stage_labels_distinct:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C ==>
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions
Proof
  strip_tac >> irule lower_dload_stage_every >>
  qexistsl [`C`,`\f. ALL_DISTINCT (fn_labels f)`,`rpolicy`,`view`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule lower_dload_function_supply_labels >> simp[] >> metis_tac[]) >>
  gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def,
      unitShapeDefsTheory.fn_shape_ok_def, venomWfTheory.wf_function_def] >>
  metis_tac[]
QED

(* Input coverage is distinct from the runner's output-supply checks. *)
Theorem fn_pass_step_input_covers_fn:
  fn_pass_step rpolicy pass observed s f out ==>
  ir_supply_covers_fn s f
Proof
  strip_tac >> irule lower_dload_covers_member >>
  gvs[fn_pass_step_def] >>
  drule lookup_unique_function_member >> metis_tac[]
QED

Theorem lower_dload_stage_every_covered:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  EVERY P C.ctx_functions /\
  (!f s g t. MEM f C.ctx_functions /\ P f /\
     ir_supply_covers_fn s f /\
     lower_dload_function_supply s f = (g,t) ==> Q g) ==>
  EVERY Q C'.ctx_functions
Proof
  rw[ctx_pass_stage_def, EVERY_MEM, LIST_REL_EL_EQN, MEM_EL] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  drule fn_pass_step_input_covers_fn >> strip_tac >>
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

(* The full source contract excludes DALLOCA; the target conditional is
   therefore vacuous, rather than a bound on relocated alloca sites. *)
Theorem lower_dload_src_inv_below_fmp:
  !rpolicy view C C' D vs t.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_src_inv D C vs ==>
    (ctx_has_dalloca C' ==> allocas_below_fmp t)
Proof
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca C` by fs[o1_src_inv_def] >>
  drule_all lower_dload_stage_no_dalloca >> simp[]
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

Theorem lower_dload_inst_supply_reserved_output:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  j.inst_opcode <> MLOAD /\ inst_output j = SOME v /\
  MEM v s.irs_used_vars ==> j = i
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[inst_output_def] >>
      imp_res_tac fresh_ir_var_contract >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[inst_output_def] >>
      imp_res_tac fresh_ir_var_contract >> gvs[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_insts_supply_reserved_output:
  !s xs t j v. lower_dload_insts_supply s ins = (xs,t) /\ MEM j xs /\
  j.inst_opcode <> MLOAD /\ inst_output j = SOME v /\
  MEM v s.irs_used_vars ==> MEM j ins
Proof
  Induct_on `ins` >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule_all lower_dload_inst_supply_reserved_output >> simp[]) >>
  drule lower_dload_inst_supply_preserves_vars >> strip_tac >>
  metis_tac[]
QED

Theorem lower_dload_blocks_supply_reserved_output:
  !s bs t j v. lower_dload_blocks_supply s bbs = (bs,t) /\
  MEM j (fn_insts_blocks bs) /\ j.inst_opcode <> MLOAD /\
  inst_output j = SOME v /\ MEM v s.irs_used_vars ==>
  MEM j (fn_insts_blocks bbs)
Proof
  Induct_on `bbs` >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[fn_insts_blocks_def]
  >- (drule_all lower_dload_insts_supply_reserved_output >> simp[]) >>
  drule (cj 1 lower_dload_insts_supply_reserved_operand) >> strip_tac >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_reserved_output:
  lower_dload_function_supply s f = (g,t) /\
  MEM j (fn_insts g) /\ j.inst_opcode <> MLOAD /\
  inst_output j = SOME v /\ MEM v s.irs_used_vars ==>
  MEM j (fn_insts f)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[lower_dload_blocks_supply_reserved_output]
QED

Theorem lower_dload_function_supply_scratch_fresh:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f ==>
  DISJOINT (alloca_roots g DIFF alloca_roots f) (set (fn_ir_vars f))
Proof
  simp[DISJOINT_DEF, EXTENSION, alloca_roots_def] >> rpt strip_tac >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
  spose_not_then strip_assume_tac >> gvs[] >>
  `MEM inst (fn_insts f)` by
    (irule lower_dload_function_supply_reserved_output >> simp[] >>
     qexistsl [`g`,`s`,`t`] >> simp[]) >> metis_tac[]
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

Theorem ptr_roots_ir_vars:
  ptr_roots P f SUBSET set (fn_ir_vars f)
Proof
  simp[SUBSET_DEF, ptr_roots_def, alloca_roots_def] >> rpt strip_tac >>
  simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS, inst_ir_vars_def] >>
  gvs[fn_insts_def, fn_insts_blocks_MEM, MEM_FLAT, MEM_MAP,
      inst_output_def, AllCaseEqs()] >>
  qexistsl [`bb`,`inst`] >> simp[]
QED

Theorem lower_dload_function_supply_nonalloca_roots:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f ==>
  ptr_roots P g DIFF alloca_roots g = ptr_roots P f DIFF alloca_roots f
Proof
  strip_tac >>
  drule lower_dload_function_supply_ptr_roots >> strip_tac >>
  drule lower_dload_function_supply_alloca_roots >> strip_tac >>
  drule_all lower_dload_function_supply_scratch_fresh >> strip_tac >>
  mp_tac ptr_roots_ir_vars >>
  gvs[EXTENSION, SUBSET_DEF, DISJOINT_DEF] >> metis_tac[]
QED

Theorem lower_dload_inst_supply_pointer_operand:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  is_pointer_preserving_op j.inst_opcode /\ MEM (Var v) j.inst_operands ==>
  MEM (Var v) i.inst_operands
Proof
  strip_tac >> Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(),
          is_pointer_preserving_op_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(),
          is_pointer_preserving_op_def] >> metis_tac[]) >>
  gvs[lower_dload_inst_supply_def]
QED

Theorem fn_ir_vars_operand:
  MEM i (fn_insts f) /\ MEM (Var v) i.inst_operands ==>
  MEM v (fn_ir_vars f)
Proof
  strip_tac >> gvs[fn_insts_def, fn_insts_blocks_MEM] >>
  simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS, inst_ir_vars_def] >>
  qexistsl [`bb`,`i`] >> simp[venomInstTheory.inst_uses_def] >>
  disj2_tac >>
  qpat_x_assum `MEM (Var v) i.inst_operands` mp_tac >>
  qspec_tac (`i.inst_operands`,`ops`) >> Induct >>
  simp[venomInstTheory.operand_vars_def] >>
  Cases_on `h` >> gvs[venomInstTheory.operand_var_def] >> metis_tac[]
QED

Theorem lower_dload_function_supply_pointer_operand:
  lower_dload_function_supply s f = (g,t) /\ MEM j (fn_insts g) /\
  is_pointer_preserving_op j.inst_opcode /\ MEM (Var v) j.inst_operands ==>
  MEM v (fn_ir_vars f)
Proof
  strip_tac >> drule_all lower_dload_function_supply_member >> strip_tac >>
  `MEM (Var v) i.inst_operands` by
    metis_tac[lower_dload_inst_supply_pointer_operand] >>
  metis_tac[fn_ir_vars_operand]
QED

Theorem lower_dload_function_supply_scratch_closure:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  FINITE roots /\ roots SUBSET ptr_roots P f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) ==>
  pointer_derived_vars g (roots UNION (alloca_roots g DIFF alloca_roots f)) =
  pointer_derived_vars f roots UNION (alloca_roots g DIFF alloca_roots f)
Proof
  strip_tac >>
  `FINITE (alloca_roots g)` by
    (irule SUBSET_FINITE >> qexists_tac `ptr_roots P g` >>
     simp[FINITE_ptr_roots, ptr_roots_def, SUBSET_DEF]) >>
  drule_all lower_dload_function_supply_old_closure >> strip_tac >>
  drule_all lower_dload_function_supply_scratch_fresh >> strip_tac >>
  simp[SET_EQ_SUBSET, SUBSET_DEF] >> conj_tac
  >- (ho_match_mp_tac pointer_derived_vars_induction >> simp[] >> conj_tac
      >- metis_tac[roots_in_pointer_derived_vars] >>
      rpt strip_tac >> rename1 `MEM (Var v) i.inst_operands` >>
      `MEM v (fn_ir_vars f)` by
        metis_tac[lower_dload_function_supply_pointer_operand] >>
      `v NOTIN (alloca_roots g DIFF alloca_roots f)` by
        (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      gvs[] >>
      `v IN pointer_derived_vars g roots` by metis_tac[] >>
      metis_tac[pointer_derived_vars_edge]) >>
  rpt strip_tac
  >- (`pointer_derived_vars g roots SUBSET
         pointer_derived_vars g (roots UNION (alloca_roots g DIFF alloca_roots f))`
        by (irule pointer_derived_vars_mono >> simp[]) >>
      gvs[SUBSET_DEF]) >>
  irule roots_in_pointer_derived_vars >> simp[]
QED

Theorem lower_dload_function_supply_fn_pv:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) ==>
  fn_pv P g = fn_pv P f UNION (alloca_roots g DIFF alloca_roots f)
Proof
  strip_tac >>
  `ptr_roots P g = ptr_roots P f UNION (alloca_roots g DIFF alloca_roots f)` by
    (drule lower_dload_function_supply_ptr_roots >> strip_tac >>
     simp[ptr_roots_def, EXTENSION] >> metis_tac[]) >>
  simp[fn_pv_def] >> irule lower_dload_function_supply_scratch_closure >>
  simp[FINITE_ptr_roots] >> conj_tac
  >- (qexists_tac `P` >> simp[]) >>
  qexistsl [`s`,`t`] >> simp[]
QED

Theorem lower_dload_function_supply_old_pv:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) /\
  MEM v (fn_ir_vars f) ==>
  (v IN fn_pv P g <=> v IN fn_pv P f)
Proof
  strip_tac >> drule_all lower_dload_function_supply_fn_pv >> strip_tac >>
  drule_all lower_dload_function_supply_scratch_fresh >> strip_tac >>
  gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem lower_dload_function_supply_nonalloca_closure:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) ==>
  pointer_derived_vars g (ptr_roots P g DIFF alloca_roots g) =
  pointer_derived_vars f (ptr_roots P f DIFF alloca_roots f)
Proof
  strip_tac >>
  drule_all lower_dload_function_supply_nonalloca_roots >> strip_tac >> simp[] >>
  irule lower_dload_function_supply_old_closure >>
  simp[FINITE_ptr_roots] >> conj_tac
  >- (qexistsl [`s`,`t`] >> simp[]) >>
  qexists_tac `P` >> simp[SUBSET_DEF]
QED

Theorem lower_dload_function_supply_alloca_closure:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) ==>
  pointer_derived_vars g (alloca_roots g) =
  pointer_derived_vars f (alloca_roots f) UNION (alloca_roots g DIFF alloca_roots f)
Proof
  strip_tac >>
  `FINITE (alloca_roots f)` by
    (irule SUBSET_FINITE >> qexists_tac `ptr_roots P f` >>
     simp[FINITE_ptr_roots, ptr_roots_def, SUBSET_DEF]) >>
  `alloca_roots f SUBSET alloca_roots g` by
    metis_tac[lower_dload_function_supply_alloca_roots] >>
  `alloca_roots g = alloca_roots f UNION (alloca_roots g DIFF alloca_roots f)` by
    (simp[EXTENSION] >> metis_tac[SUBSET_DEF]) >>
  drule lower_dload_function_supply_scratch_closure >>
  disch_then (qspecl_then [`alloca_roots f`,`P`] mp_tac) >>
  impl_tac >- simp[ptr_roots_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_pointer_operand_pv:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) /\
  MEM i (fn_insts g) /\ is_pointer_preserving_op i.inst_opcode /\
  MEM (Var v) i.inst_operands ==>
  (v IN fn_pv P g <=> v IN fn_pv P f)
Proof
  strip_tac >> irule lower_dload_function_supply_old_pv >> simp[] >>
  conj_tac >- metis_tac[lower_dload_function_supply_pointer_operand] >>
  qexistsl [`s`,`t`] >> simp[]
QED

Theorem lower_dload_function_supply_affine:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) /\
  affine_pointer_ops f (ptr_roots P f) ==>
  affine_pointer_ops g (ptr_roots P g)
Proof
  strip_tac >>
  `!i v. MEM i (fn_insts g) /\ is_pointer_preserving_op i.inst_opcode /\
      MEM (Var v) i.inst_operands ==>
      (v IN fn_pv P g <=> v IN fn_pv P f)` by
    metis_tac[lower_dload_function_supply_pointer_operand_pv] >>
  gvs[affine_pointer_ops_def, GSYM fn_pv_def] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `MEM inst (fn_insts g)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `is_pointer_preserving_op inst.inst_opcode` by
    simp[is_pointer_preserving_op_def] >>
  `MEM inst (fn_insts f)` by
    (irule lower_dload_function_supply_pointer_edge >>
     simp[] >> conj_tac
     >- (qexistsl [`g`,`s`,`t`] >> simp[]) >>
     qexistsl [`P`,`fn_pv P f`] >> simp[] >>
     gvs[] >> metis_tac[MEM]) >>
  gvs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM]
QED

Theorem lower_dload_function_supply_phi:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) /\
  phi_pv_all_var f (ptr_roots P f) ==>
  phi_pv_all_var g (ptr_roots P g)
Proof
  strip_tac >>
  `!i v. MEM i (fn_insts g) /\ is_pointer_preserving_op i.inst_opcode /\
      MEM (Var v) i.inst_operands ==>
      (v IN fn_pv P g <=> v IN fn_pv P f)` by
    metis_tac[lower_dload_function_supply_pointer_operand_pv] >>
  gvs[phi_pv_all_var_def, GSYM fn_pv_def] >> rpt strip_tac >>
  `MEM inst (fn_insts g)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `is_pointer_preserving_op inst.inst_opcode` by
    simp[is_pointer_preserving_op_def] >>
  `MEM inst (fn_insts f)` by
    (irule lower_dload_function_supply_pointer_edge >> simp[] >> conj_tac
     >- (qexistsl [`g`,`s`,`t`] >> simp[]) >>
     qexistsl [`P`,`fn_pv P f`] >> simp[] >> metis_tac[]) >>
  gvs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem ptr_use_ok_cong:
  (!v. MEM (Var v) i.inst_operands ==> (v IN pv <=> v IN qv)) ==>
  (ptr_use_ok P pv i <=> ptr_use_ok P qv i)
Proof
  strip_tac >> simp[ptr_use_ok_def] >>
  `!nm args k v. decode_invoke i = SOME (nm,args) /\ k < LENGTH args /\
       EL k args = Var v ==> MEM (Var v) i.inst_operands` by
    (simp[decode_invoke_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
     metis_tac[MEM_EL, MEM]) >>
  eq_tac >> rpt strip_tac >> metis_tac[MEM]
QED

Theorem lower_dload_function_supply_old_ptr_use:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) /\
  MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P g) i
Proof
  strip_tac >>
  `!v. MEM (Var v) i.inst_operands ==>
       (v IN fn_pv P f <=> v IN fn_pv P g)` by
    metis_tac[lower_dload_function_supply_old_pv, fn_ir_vars_operand] >>
  drule ptr_use_ok_cong >> metis_tac[]
QED

Theorem lower_dload_inst_supply_fresh_outputs:
  lower_dload_inst_supply s i = (xs,t) /\
  EVERY (\v. MEM v s.irs_used_vars) i.inst_outputs ==>
  EVERY (\v. MEM v t.irs_used_vars) (FLAT (MAP (\j. j.inst_outputs) xs)) /\
  (!v. MEM v s.irs_used_vars /\ MEM v (FLAT (MAP (\j. j.inst_outputs) xs)) ==>
       MEM v i.inst_outputs) /\
  (!j k v. MEM j xs /\ MEM k xs /\ MEM v j.inst_outputs /\
      MEM v k.inst_outputs /\ ~MEM v s.irs_used_vars ==> j = k)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[EVERY_MEM] >>
      metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[EVERY_MEM] >>
      metis_tac[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[EVERY_MEM]
QED

Theorem lower_dload_insts_supply_fresh_outputs:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) /\
  EVERY (\v. MEM v s.irs_used_vars) (FLAT (MAP (\i. i.inst_outputs) ins)) ==>
  EVERY (\v. MEM v t.irs_used_vars) (FLAT (MAP (\j. j.inst_outputs) xs)) /\
  (!v. MEM v s.irs_used_vars /\ MEM v (FLAT (MAP (\j. j.inst_outputs) xs)) ==>
       MEM v (FLAT (MAP (\i. i.inst_outputs) ins))) /\
  (!j k v. MEM j xs /\ MEM k xs /\ MEM v j.inst_outputs /\
      MEM v k.inst_outputs /\ ~MEM v s.irs_used_vars ==> j = k)
Proof
  Induct_on `ins` >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all lower_dload_inst_supply_fresh_outputs >> strip_tac >>
  drule lower_dload_inst_supply_preserves_vars >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (FLAT (MAP (\i. i.inst_outputs) ins))` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule (cj 1 lower_dload_insts_supply_reserved_operand) >> strip_tac >>
  gvs[EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_fresh_outputs:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) /\
  EVERY (\v. MEM v s.irs_used_vars)
    (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) ==>
  EVERY (\v. MEM v t.irs_used_vars)
    (FLAT (MAP (\j. j.inst_outputs) (fn_insts_blocks bs))) /\
  (!v. MEM v s.irs_used_vars /\
       MEM v (FLAT (MAP (\j. j.inst_outputs) (fn_insts_blocks bs))) ==>
       MEM v (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))) /\
  (!j k v. MEM j (fn_insts_blocks bs) /\ MEM k (fn_insts_blocks bs) /\
      MEM v j.inst_outputs /\ MEM v k.inst_outputs /\
      ~MEM v s.irs_used_vars ==> j = k)
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs(), fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all lower_dload_insts_supply_fresh_outputs >> strip_tac >>
  drule (cj 1 lower_dload_insts_supply_reserved_operand) >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule (cj 1 lower_dload_blocks_supply_reserved_operand) >> strip_tac >>
  gvs[fn_insts_blocks_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_fresh_output_unique:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  MEM j (fn_insts g) /\ MEM k (fn_insts g) /\
  MEM v j.inst_outputs /\ MEM v k.inst_outputs /\ ~MEM v (fn_ir_vars f) ==>
  j = k
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `EVERY (\v. MEM v s.irs_used_vars)
     (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks f.fn_blocks)))` by
    (gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
          PULL_EXISTS, inst_ir_vars_def] >>
     gvs[MEM_FLAT, MEM_MAP, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all lower_dload_blocks_supply_fresh_outputs >> strip_tac >>
  `~MEM v s.irs_used_vars` by
    (strip_tac >>
     `MEM v (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks f.fn_blocks)))` by
       (gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
     gvs[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
         PULL_EXISTS, inst_ir_vars_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_nonalloca_output:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  MEM j (fn_insts g) /\ j.inst_opcode <> ALLOCA /\
  MEM v j.inst_outputs /\ ~MEM v (fn_ir_vars f) ==> v NOTIN alloca_roots g
Proof
  simp[alloca_roots_def] >> rpt strip_tac >>
  `MEM v inst.inst_outputs` by gvs[inst_output_def, AllCaseEqs()] >>
  `j = inst` by metis_tac[lower_dload_function_supply_fresh_output_unique] >>
  gvs[]
QED

Theorem lower_dload_insts_supply_member_covered:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) /\ MEM j xs /\
    EVERY (\v. MEM v s.irs_used_vars) reserved ==>
  ?i u ys w. MEM i ins /\ lower_dload_inst_supply u i = (ys,w) /\
    MEM j ys /\ EVERY (\v. MEM v u.irs_used_vars) reserved /\
    EVERY (\k. MEM k xs) ys
Proof
  Induct_on `ins` >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (qexistsl [`h`,`s`,`out`,`s1`] >> simp[EVERY_MEM]) >>
  drule lower_dload_inst_supply_preserves_vars >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars) reserved` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`i`,`u`,`ys`,`w`] >> gvs[EVERY_MEM]
QED

Theorem lower_dload_blocks_supply_member_covered:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) /\
    MEM j (fn_insts_blocks bs) /\ EVERY (\v. MEM v s.irs_used_vars) reserved ==>
  ?i u ys w. MEM i (fn_insts_blocks bbs) /\
    lower_dload_inst_supply u i = (ys,w) /\ MEM j ys /\
    EVERY (\v. MEM v u.irs_used_vars) reserved /\
    EVERY (\k. MEM k (fn_insts_blocks bs)) ys
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[fn_insts_blocks_def]
  >- (drule_all lower_dload_insts_supply_member_covered >>
      strip_tac >> qexistsl [`i`,`u`,`ys`,`w`] >> gvs[EVERY_MEM]) >>
  drule (cj 1 lower_dload_insts_supply_reserved_operand) >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars) reserved` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`i`,`u`,`ys`,`w`] >> gvs[EVERY_MEM]
QED

Theorem lower_dload_function_supply_member_covered:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  MEM j (fn_insts g) ==>
  ?i u ys w. MEM i (fn_insts f) /\ lower_dload_inst_supply u i = (ys,w) /\
    MEM j ys /\ EVERY (\v. MEM v u.irs_used_vars) (fn_ir_vars f) /\
    EVERY (\k. MEM k (fn_insts g)) ys
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_def] >>
  strip_tac >> gvs[] >>
  `EVERY (\v. MEM v s.irs_used_vars) (fn_ir_vars f)` by
    gvs[ir_supply_covers_fn_def, list_subset_def] >>
  drule_all lower_dload_blocks_supply_member_covered >> simp[]
QED

Theorem fn_pv_ir_vars:
  fn_pv P f SUBSET set (fn_ir_vars f)
Proof
  simp[fn_pv_def, SUBSET_DEF] >>
  ho_match_mp_tac pointer_derived_vars_induction >> simp[FINITE_ptr_roots] >>
  conj_tac >- (rpt strip_tac >> irule (SRULE [SUBSET_DEF] ptr_roots_ir_vars) >>
              qexists_tac `P` >> simp[]) >>
  rpt strip_tac >>
  gvs[fn_insts_def, fn_insts_blocks_MEM] >>
  simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS, inst_ir_vars_def] >>
  qexistsl [`bb`,`i`] >> gvs[inst_output_def, AllCaseEqs()]
QED

Theorem lower_dload_function_supply_fresh_nonalloca_pv:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) /\
  MEM j (fn_insts g) /\ j.inst_opcode <> ALLOCA /\
  MEM v j.inst_outputs /\ ~MEM v (fn_ir_vars f) ==> v NOTIN fn_pv P g
Proof
  strip_tac >> drule_all lower_dload_function_supply_fn_pv >> strip_tac >>
  drule_all lower_dload_function_supply_nonalloca_output >> strip_tac >>
  simp[] >> metis_tac[fn_pv_ir_vars, SUBSET_DEF]
QED

Theorem lower_dload_inst_supply_ptr_use:
  lower_dload_inst_supply s i = (xs,t) /\ ptr_use_ok P pv i /\
  (!j v. MEM j xs /\ j.inst_opcode = ADD /\ MEM v j.inst_outputs ==>
     v NOTIN pv) ==> EVERY (ptr_use_ok P pv) xs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >>
      gvs[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM] >>
      fs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
      rpt strip_tac >> gvs[is_pointer_preserving_op_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >>
      gvs[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM] >>
      fs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
      rpt strip_tac >> gvs[is_pointer_preserving_op_def] >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
      Cases_on `Var v = src_op` >> Cases_on `Var v = size_op` >>
      Cases_on `Var v = dst_op` >> gvs[] >>
      `v <> add_v` by metis_tac[] >> simp[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_add_output:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  (i.inst_opcode = DLOAD \/ i.inst_opcode = DLOADBYTES) /\
  j.inst_opcode = ADD /\ MEM v j.inst_outputs ==> inst_output j = SOME v
Proof
  strip_tac >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
  gvs[inst_output_def]
QED


Theorem lower_dload_function_supply_ptr_use:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i) ==>
  !j. MEM j (fn_insts g) ==> ptr_use_ok P (fn_pv P g) j
Proof
  rpt strip_tac >>
  drule_all lower_dload_function_supply_member_covered >> strip_tac >>
  Cases_on `i.inst_opcode = DLOAD \/ i.inst_opcode = DLOADBYTES`
  >- (`ptr_use_ok P (fn_pv P g) i` by
        metis_tac[lower_dload_function_supply_old_ptr_use] >>
      `!k v. MEM k ys /\ k.inst_opcode = ADD /\ MEM v k.inst_outputs ==>
         v NOTIN fn_pv P g` by
        (rpt gen_tac >> strip_tac >>
         `inst_output k = SOME v` by
           metis_tac[lower_dload_inst_supply_add_output] >>
         `~MEM v (fn_ir_vars f)` by
           (strip_tac >>
            `MEM v u.irs_used_vars` by gvs[EVERY_MEM] >>
            `k = i` by
              (irule lower_dload_inst_supply_reserved_output >> simp[] >>
               qexistsl [`u`,`w`,`ys`] >> simp[]) >>
            gvs[]) >>
         irule lower_dload_function_supply_fresh_nonalloca_pv >> simp[] >>
         conj_tac
         >- (qexists_tac `k` >> gvs[EVERY_MEM]) >>
         qexistsl [`f`,`s`,`t`] >> simp[]) >>
      drule_all lower_dload_inst_supply_ptr_use >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  `j = i` by (gvs[lower_dload_inst_supply_def] >> metis_tac[]) >>
  metis_tac[lower_dload_function_supply_old_ptr_use]
QED

Theorem lower_dload_inst_supply_static_clauses:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  ptr_use_ok P pv i /\
  i.inst_opcode <> MEMTOP /\ i.inst_opcode <> DRET /\
  i.inst_opcode <> GETFMP /\ i.inst_opcode <> SETFMP /\
  i.inst_opcode <> RETFMP /\ i.inst_opcode <> FMP_PARAM /\
  ((i.inst_opcode = ISTORE \/ i.inst_opcode = ILOAD) ==>
    !v. MEM (Var v) i.inst_operands ==> v NOTIN pv) /\
  ((i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
    (?v. MEM (Var v) i.inst_operands /\ v IN pv) ==>
    !l. ~MEM (Label l) i.inst_operands) ==>
  j.inst_opcode <> MEMTOP /\ j.inst_opcode <> DRET /\
  j.inst_opcode <> GETFMP /\ j.inst_opcode <> SETFMP /\
  j.inst_opcode <> RETFMP /\ j.inst_opcode <> FMP_PARAM /\
  ((j.inst_opcode = ISTORE \/ j.inst_opcode = ILOAD) ==>
    !v. MEM (Var v) j.inst_operands ==> v NOTIN pv) /\
  ((j.inst_opcode = ADD \/ j.inst_opcode = SUB) /\
    (?v. MEM (Var v) j.inst_operands /\ v IN pv) ==>
    !l. ~MEM (Label l) j.inst_operands)
Proof
  strip_tac >> drule ptr_use_ok_dload_offsets >> strip_tac >>
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[lower_dload_inst_supply_def] >> metis_tac[]
QED

Theorem lower_dload_inst_supply_reserved_write:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  mem_write_ops j = SOME ops /\ ops.iao_ofst = Var v /\
  MEM v s.irs_used_vars ==>
  ?old_ops. mem_write_ops i = SOME old_ops /\ old_ops.iao_ofst = Var v
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[mem_write_ops_def] >>
      imp_res_tac fresh_ir_var_contract >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[mem_write_ops_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[] >> metis_tac[]
QED

Theorem lower_dload_function_supply_no_mixed_write:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_ptr_ok P f ==>
  !j ops v. MEM j (fn_insts g) /\ mem_write_ops j = SOME ops /\
    ops.iao_ofst = Var v ==>
    ~(v IN pointer_derived_vars g (alloca_roots g) /\
      v IN pointer_derived_vars g (ptr_roots P g DIFF alloca_roots g))
Proof
  rpt gen_tac >> strip_tac >>
  `!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i` by
    gvs[fn_ptr_ok_def] >>
  drule_all lower_dload_function_supply_alloca_closure >> strip_tac >>
  drule_all lower_dload_function_supply_nonalloca_closure >> strip_tac >>
  drule_all lower_dload_function_supply_scratch_fresh >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  `v IN fn_pv P f` by
    (simp[fn_pv_def] >>
     `pointer_derived_vars f (ptr_roots P f DIFF alloca_roots f)
       SUBSET pointer_derived_vars f (ptr_roots P f)` by
       (irule pointer_derived_vars_mono >> simp[FINITE_ptr_roots, SUBSET_DEF]) >>
     gvs[SUBSET_DEF]) >>
  `MEM v (fn_ir_vars f)` by metis_tac[fn_pv_ir_vars, SUBSET_DEF] >>
  `v NOTIN (alloca_roots g DIFF alloca_roots f)` by
    (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  drule_all lower_dload_function_supply_member_covered >> strip_tac >>
  `MEM v u.irs_used_vars` by gvs[EVERY_MEM] >>
  drule_all lower_dload_inst_supply_reserved_write >> strip_tac >>
  gvs[fn_ptr_ok_def] >> metis_tac[]
QED

Theorem lower_dload_function_supply_definition_closure:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_ptr_ok P f ==>
  !j v. MEM j (fn_insts g) /\ MEM v j.inst_outputs /\ v IN fn_pv P g ==>
    j.inst_opcode = ALLOCA \/
    ((j.inst_opcode = DALLOCA \/
      (j.inst_opcode = PARAM /\
       ?idx. j.inst_operands = [Lit idx] /\ w2n idx IN P g.fn_name)) /\
      v NOTIN alloca_roots g) \/
    (is_pointer_preserving_op j.inst_opcode /\
     ?u. MEM (Var u) j.inst_operands /\ u IN fn_pv P g)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `j.inst_opcode = ALLOCA` >- simp[] >>
  `!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i` by
    gvs[fn_ptr_ok_def] >>
  `MEM v (fn_ir_vars f)` by
    (spose_not_then assume_tac >>
     drule_all lower_dload_function_supply_fresh_nonalloca_pv >> simp[]) >>
  `v IN fn_pv P f` by metis_tac[lower_dload_function_supply_old_pv] >>
  `g.fn_name = f.fn_name` by
    gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
  `!x. MEM x (fn_ir_vars f) ==> (x IN fn_pv P g <=> x IN fn_pv P f)` by
    metis_tac[lower_dload_function_supply_old_pv] >>
  `v NOTIN alloca_roots f ==> v NOTIN alloca_roots g` by
    (drule_all lower_dload_function_supply_scratch_fresh >>
     simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  drule_all lower_dload_function_supply_member_covered >> strip_tac >>
  `MEM v u.irs_used_vars` by gvs[EVERY_MEM] >>
  `!x. MEM (Var x) i.inst_operands ==>
       (x IN fn_pv P g <=> x IN fn_pv P f)` by
    metis_tac[fn_ir_vars_operand] >>
  `!x. MEM x i.inst_outputs /\ x IN fn_pv P f ==>
     i.inst_opcode = ALLOCA \/
     ((i.inst_opcode = DALLOCA \/
       (i.inst_opcode = PARAM /\ ?idx. i.inst_operands = [Lit idx] /\
          w2n idx IN P f.fn_name)) /\ x NOTIN alloca_roots f) \/
     (is_pointer_preserving_op i.inst_opcode /\
       ?a. MEM (Var a) i.inst_operands /\ a IN fn_pv P f)` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOAD \/ i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      imp_res_tac fresh_ir_var_contract >>
      gvs[is_pointer_preserving_op_def] >> metis_tac[]) >>
  `j = i` by (gvs[lower_dload_inst_supply_def] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem lower_dload_function_supply_fn_ptr_ok:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_ptr_ok P f ==> fn_ptr_ok P g
Proof
  strip_tac >>
  `!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P f) i` by
    gvs[fn_ptr_ok_def] >>
  `!i v. MEM i (fn_insts f) /\ MEM (Var v) i.inst_operands ==>
     (v IN fn_pv P g <=> v IN fn_pv P f)` by
    metis_tac[lower_dload_function_supply_old_pv, fn_ir_vars_operand] >>
  `!i. MEM i (fn_insts f) ==> ptr_use_ok P (fn_pv P g) i` by
    metis_tac[lower_dload_function_supply_old_ptr_use] >>
  `g.fn_forced_alloc_positions = f.fn_forced_alloc_positions` by
    gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
  simp[fn_ptr_ok_def] >> rpt conj_tac
  >- gvs[fn_ptr_ok_def]
  >- (rpt gen_tac >> strip_tac >>
      rename1 `MEM j (fn_insts g)` >>
      `ptr_use_ok P (fn_pv P g) j` by
        metis_tac[lower_dload_function_supply_ptr_use] >>
      drule_all lower_dload_function_supply_member_covered >> strip_tac >>
      simp[] >> irule lower_dload_inst_supply_static_clauses >>
      qexists_tac `P` >>
      qpat_assum `lower_dload_inst_supply u i = _` (irule_at Any) >>
      gvs[fn_ptr_ok_def] >> metis_tac[])
  >- (irule lower_dload_function_supply_affine >>
      qexistsl [`f`,`s`,`t`] >> gvs[fn_ptr_ok_def])
  >- (irule lower_dload_function_supply_phi >>
      qexistsl [`f`,`s`,`t`] >> gvs[fn_ptr_ok_def])
  >- (rpt gen_tac >> strip_tac >>
      drule_all lower_dload_function_supply_no_mixed_write >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all lower_dload_function_supply_definition_closure >> simp[]
QED

Theorem lower_dload_stage_fn_ptr_ok:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  EVERY (fn_ptr_ok P) C.ctx_functions ==>
  EVERY (fn_ptr_ok P) C'.ctx_functions
Proof
  strip_tac >> irule lower_dload_stage_every_covered >>
  qexistsl [`C`,`fn_ptr_ok P`,`rpolicy`,`view`] >> simp[] >>
  metis_tac[lower_dload_function_supply_fn_ptr_ok]
QED
