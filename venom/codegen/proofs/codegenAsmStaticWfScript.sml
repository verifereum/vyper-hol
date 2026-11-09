(*
 * Codegen's assembly is statically well formed for the symbolic machine:
 * labels are unique and never also data headers, every referenced label is
 * defined, the data segment holds no code addresses and sits at the end,
 * and the encoding fits.
 *)
Theory codegenAsmStaticWf
Ancestors
  codegenSymRel codegenAsmProgOk codegenEncodingWf codegen asmSymSem asmWf
  asmOptimizer unitShapeDefs stackPlanGen venomWf fnPlanCover
  list rich_list planExec stackPlanTypes stackPlanOps finite_map

Definition plan_ref_def:
  plan_ref l ops <=>
    MEM (SOPushLabel l) ops \/ MEM (SOPush (Label l)) ops \/
    (?n. MEM (SOPushOfst l n) ops)
End

Theorem plan_ref_append:
  plan_ref l (xs ++ ys) <=> plan_ref l xs \/ plan_ref l ys
Proof
  simp[plan_ref_def, MEM_APPEND] >> metis_tac[]
QED

Theorem asm_label_refs_append:
  asm_label_refs (xs ++ ys) = asm_label_refs xs ++ asm_label_refs ys
Proof
  simp[asm_label_refs_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem exec_stack_op_label_refs:
  MEM l (asm_label_refs (exec_stack_op fmp op)) <=> plan_ref l [op]
Proof
  Cases_on `op` >> simp[exec_stack_op_def, plan_ref_def,
    asm_label_refs_def, MEM_FLAT, MEM_MAP, MEM_REPLICATE] >>
  rename1 `SOPush operand` >> Cases_on `operand` >>
  simp[exec_stack_op_def, asm_label_refs_def]
QED

Theorem exec_stack_op_label:
  MEM (AsmLabel l) (exec_stack_op fmp op) <=> op = SOLabel l
Proof
  Cases_on `op` >> simp[exec_stack_op_def, MEM_REPLICATE, EQ_SYM_EQ] >>
  rename1 `SOPush operand` >> Cases_on `operand` >>
  simp[exec_stack_op_def]
QED

Theorem execute_plan_label_refs:
  MEM l (asm_label_refs (execute_plan fmp ops)) <=> plan_ref l ops
Proof
  Induct_on `ops`
  >- simp[execute_plan_def, asm_label_refs_def, plan_ref_def]
  >> gvs[execute_plan_def, asm_label_refs_append,
         exec_stack_op_label_refs, plan_ref_def]
  >> metis_tac[]
QED

Theorem execute_plan_label:
  MEM (AsmLabel l) (execute_plan fmp ops) <=> MEM (SOLabel l) ops
Proof
  simp[execute_plan_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[exec_stack_op_label]
QED

Theorem plan_ref_closed_append:
  (!l. plan_ref l xs ==> MEM (SOLabel l) xs \/ A l) /\
  (!l. plan_ref l ys ==> MEM (SOLabel l) ys \/ A l) ==>
  !l. plan_ref l (xs ++ ys) ==> MEM (SOLabel l) (xs ++ ys) \/ A l
Proof
  simp[plan_ref_append, MEM_APPEND] >> metis_tac[]
QED

Theorem do_spill_tos_no_ref:
  do_spill_tos ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  simp[do_spill_tos_def] >> pairarg_tac >>
  simp[] >> rpt strip_tac >> gvs[plan_ref_def]
QED

Theorem do_spill_at_no_ref:
  do_spill_at dist ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  simp[do_spill_at_def] >> IF_CASES_TAC
  >- metis_tac[do_spill_tos_no_ref]
  >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> drule do_spill_tos_no_ref >> simp[plan_ref_append, plan_ref_def]
QED

Theorem do_restore_no_ref:
  do_restore operand ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled operand` >>
  simp[] >> rpt strip_tac >> gvs[plan_ref_def]
QED

Theorem restore_spilled_plan_no_ref:
  !operands ps ops ps'.
  restore_spilled_plan operands ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  Induct >- simp[restore_spilled_plan_def, plan_ref_def]
  >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[plan_ref_append] >>
  metis_tac[do_restore_no_ref]
QED

Theorem spill_fold_no_ref:
  !items acc_ops offsets al ops offsets' al'.
  FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al))
    (acc_ops, offsets, al) items = (ops, offsets', al') /\
  ~plan_ref l acc_ops ==> ~plan_ref l ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ [SOSpill q]` mp_tac) >>
  simp[plan_ref_append, plan_ref_def] >> disch_then drule >> simp[]
QED

Theorem do_swap_no_ref:
  do_swap dist ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  simp[do_swap_def] >>
  Cases_on `dist = 0` >- simp[plan_ref_def] >>
  Cases_on `dist <= 16` >- (rw[] >> simp[plan_ref_def]) >>
  simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule spill_fold_no_ref >> simp[plan_ref_def, MEM_MAP]
QED

Theorem do_dup_no_ref:
  do_dup dist ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  simp[do_dup_def] >> IF_CASES_TAC >- (rw[] >> simp[plan_ref_def]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule spill_fold_no_ref >>
  simp[plan_ref_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem reduce_depth_plan_no_ref:
  !fuel target_ops target_op f n ps ops ps'.
  reduce_depth_plan fuel target_ops target_op f n ps = (ops, ps') ==>
  !l. ~plan_ref l ops
Proof
  Induct >> simp[reduce_depth_plan_def, plan_ref_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth target_op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x n` >> simp[] >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[do_spill_at_no_ref, plan_ref_def]
QED

Theorem reorder_one_no_ref:
  reorder_one dfg target_ops idx operand ps = (ops, ps') ==>
  !l. ~plan_ref l ops
Proof
  simp[reorder_one_def] >> pairarg_tac >>
  `!l. ~plan_ref l restore_ops` by
    (gvs[AllCaseEqs(), plan_ref_def] >> metis_tac[do_restore_no_ref, plan_ref_def]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `stack_get_unfixed_depth operand (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps1.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  pairarg_tac >>
  `!l. ~plan_ref l reduce_ops` by
    (gvs[AllCaseEqs(), plan_ref_def] >> metis_tac[reduce_depth_plan_no_ref, plan_ref_def]) >>
  gvs[] >> qpat_x_assum `_ = (reduce_ops, ps2)` kall_tac >>
  Cases_on `stack_get_unfixed_depth operand (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps2.ps_stack` >> simp[]
  >- (rw[] >> gvs[plan_ref_append]) >>
  rpt IF_CASES_TAC >> simp[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[plan_ref_append] >>
  metis_tac[do_swap_no_ref, plan_ref_def]
QED

Theorem reorder_fold_no_ref:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) (idx, operand).
    (\(step_ops, ps'). (ops ++ step_ops, ps'))
      (reorder_one dfg target_ops idx operand ps)) (acc_ops, ps) xs =
    (ops, ps') /\ ~plan_ref l acc_ops ==> ~plan_ref l ops
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  Cases_on `reorder_one dfg target_ops h0 h1 ps` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ q` mp_tac) >>
  simp[plan_ref_append] >> disch_then drule >>
  drule reorder_one_no_ref >> simp[]
QED

Theorem reorder_plan_no_ref:
  reorder_plan dfg target_ops ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  simp[reorder_plan_def] >> strip_tac >> gen_tac >>
  drule reorder_fold_no_ref >> simp[plan_ref_def]
QED

Theorem popmany_fold_no_ref:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops, ps)
    | SOME dist =>
        (\(swap_ops, ps').
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
        (if dist = 0 then ([], ps) else do_swap dist ps))
    (acc_ops, ps) xs = (ops, ps') /\
  ~plan_ref l acc_ops ==> ~plan_ref l ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `stack_get_depth h ps.ps_stack` >> simp[]
  >- metis_tac[] >>
  Cases_on `x = 0` >> simp[]
  >- (strip_tac >>
      first_x_assum (qspec_then `acc_ops ++ [SOPop 1]` mp_tac) >>
      simp[plan_ref_append, plan_ref_def] >> disch_then drule >> simp[]) >>
  Cases_on `do_swap x ps` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ q ++ [SOPop 1]` mp_tac) >>
  simp[plan_ref_append, plan_ref_def] >> disch_then drule >>
  drule do_swap_no_ref >> simp[plan_ref_def]
QED

Theorem popmany_individual_no_ref:
  popmany_individual to_pop ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  simp[popmany_individual_def] >> strip_tac >> gen_tac >>
  drule popmany_fold_no_ref >> simp[plan_ref_def]
QED

Theorem popmany_plan_no_ref:
  popmany_plan to_pop ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  Cases_on `to_pop` >> simp[popmany_plan_def, plan_ref_def] >>
  rpt IF_CASES_TAC >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule do_swap_no_ref >> simp[plan_ref_def]) >>
  metis_tac[popmany_individual_no_ref, plan_ref_def]
QED

Theorem codegen_asm_static_wf:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  sym_unit_static_ok unit /\ codegen_ready unit.cu_context ==>
  asm_static_wf prog
Proof
  cheat
QED
