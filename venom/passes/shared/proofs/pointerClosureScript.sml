Theory pointerClosure
Ancestors venomWfProps pointerConfinedDefs venomInst While pred_set list allocaRemapSSA
  removeUnusedSsaProofs


Theorem pointer_use_step_membership:
  MEM v (pointer_use_step fn vars) <=>
  ?bb inst u. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ MEM u vars /\
    MEM v inst.inst_outputs
Proof
  simp[pointer_use_step_def, MEM_FLAT, MEM_MAP, EXISTS_MEM] >>
  eq_tac
  >- (rpt strip_tac >>
      gvs[MEM_FLAT, MEM_MAP, EXISTS_MEM, AllCaseEqs()] >>
      Cases_on `op` >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexists `bb` >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexists `inst` >> simp[] >>
  IF_CASES_TAC >> gvs[] >>
  first_x_assum (qspec_then `Var u` mp_tac) >> simp[]
QED

Theorem pointer_use_step_decreases:
  FINITE U /\ set (pointer_use_step fn vars) SUBSET U /\
  pointer_use_step_step fn vars = SOME next ==>
  CARD (U DIFF set next) < CARD (U DIFF set vars)
Proof
  strip_tac >>
  gvs[pointer_use_step_step_def, AllCaseEqs(), Excl "CARD_DIFF"] >>
  irule CARD_PSUBSET >> simp[Excl "CARD_DIFF"] >>
  gvs[PSUBSET_DEF, SUBSET_DEF, EXTENSION, MEM_FILTER, FILTER_EQ_NIL, EXISTS_MEM,
      Excl "CARD_DIFF"] >>
  metis_tac[MEM_APPEND]
QED

Theorem pointer_use_step_output_bound:
  set (pointer_use_step fn vars) SUBSET
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))
Proof
  rw[SUBSET_DEF, pointer_use_step_membership] >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexists `inst` >> simp[] >>
  metis_tac[mem_fn_insts_intro]
QED

(* Name the loop body once, keeping termination and invariant goals small. *)
Definition pointer_closure_next_def:
  pointer_closure_next fn s =
    case pointer_use_step_step fn (OUTL s) of
      NONE => INR (OUTL s)
    | SOME vs => INL vs
End



Theorem pointer_closure_terminates:
  !vars. ?result.
    OWHILE ISL (pointer_closure_next fn) (INL vars) = SOME (INR result) /\
    pointer_use_step_step fn result = NONE /\
    set vars SUBSET set result
Proof
  measureInduct_on `CARD
    (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set vars)` >>
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  Cases_on `pointer_use_step_step fn vars`
  >- (qexists `vars` >> simp[Once OWHILE_THM, pointer_closure_next_def] >>
      simp[Once OWHILE_THM]) >>
  rename1 `pointer_use_step_step fn vars = SOME next` >>
  `CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set next) <
   CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set vars)` by
    (irule pointer_use_step_decreases >>
     simp[] >> qexists `fn` >> simp[pointer_use_step_output_bound]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`fn`, `next`] mp_tac) >>
  simp[] >> strip_tac >> qexists `result` >>
  simp[Once OWHILE_THM, pointer_closure_next_def] >>
  gvs[pointer_use_step_step_def, AllCaseEqs(), SUBSET_DEF] >>
  metis_tac[MEM_APPEND]
QED

Theorem pointer_use_vars_terminal:
  !vars. pointer_use_step_step fn (pointer_use_vars fn vars) = NONE
Proof
  gen_tac >> qspec_then `vars` strip_assume_tac pointer_closure_terminates >>
  gvs[pointer_use_vars_def, GSYM pointer_closure_next_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem pointer_use_vars_roots:
  !vars. set vars SUBSET set (pointer_use_vars fn vars)
Proof
  gen_tac >> qspec_then `vars` strip_assume_tac pointer_closure_terminates >>
  gvs[pointer_use_vars_def, GSYM pointer_closure_next_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem pointer_derived_vars_roots:
  FINITE roots ==> roots SUBSET pointer_derived_vars fn roots
Proof
  strip_tac >>
  qspec_then `SET_TO_LIST roots` mp_tac pointer_use_vars_roots >>
  simp[pointer_derived_vars_def, SUBSET_DEF, MEM_SET_TO_LIST]
QED

Theorem pointer_derived_vars_closed:
  FINITE roots /\ MEM inst (fn_insts fn) /\
  is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var u) inst.inst_operands /\
  u IN pointer_derived_vars fn roots /\ MEM v inst.inst_outputs ==>
  v IN pointer_derived_vars fn roots
Proof
  strip_tac >>
  qspec_then `SET_TO_LIST roots` mp_tac pointer_use_vars_terminal >>
  simp[pointer_use_step_step_def] >>
  gvs[pointer_derived_vars_def, fn_insts_blocks_flat, MEM_FLAT,
      MEM_MAP, venomInstTheory.fn_insts_def] >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >>
  disch_then (qspec_then `v` mp_tac) >>
  simp[pointer_use_step_membership] >> metis_tac[]
QED

(* Least closed superset of the roots, independent of any particular pass. *)
Theorem ptr_closure_step_subset[local]:
  (!inst v out. MEM inst (fn_insts fn) /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var v) inst.inst_operands /\ v IN target /\ MEM out inst.inst_outputs ==>
    out IN target) /\ set vars SUBSET target /\
  pointer_use_step_step fn vars = SOME next ==> set next SUBSET target
Proof
  simp[pointer_use_step_step_def, AllCaseEqs(), SUBSET_DEF,
       pointer_use_step_membership, MEM_FILTER] >>
  rpt strip_tac >> gvs[MEM_FILTER, pointer_use_step_membership] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ptr_closure_loop_subset[local]:
  (!inst v out. MEM inst (fn_insts fn) /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var v) inst.inst_operands /\ v IN target /\ MEM out inst.inst_outputs ==>
    out IN target) /\ set vars SUBSET target /\
  OWHILE ISL (pointer_closure_next fn) (INL vars) = SOME (INR result) ==>
  set result SUBSET target
Proof
  strip_tac >>
  `(\s. case s of INL vs => set vs SUBSET target | INR vs => set vs SUBSET target)
      (INR result)` suffices_by simp[] >>
  irule OWHILE_INV_IND >>
  qexistsl [`ISL`, `pointer_closure_next fn`, `INL vars`] >>
  simp[] >> rpt gen_tac >> Cases_on `x` >> simp[pointer_closure_next_def] >>
  strip_tac >> Cases_on `pointer_use_step_step fn x'` >> simp[] >>
  metis_tac[ptr_closure_step_subset]
QED

Theorem ptr_derived_least:
  FINITE roots /\ roots SUBSET target /\
  (!inst v out. MEM inst (fn_insts fn) /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var v) inst.inst_operands /\ v IN target /\ MEM out inst.inst_outputs ==>
    out IN target) ==>
  pointer_derived_vars fn roots SUBSET target
Proof
  strip_tac >>
  qspec_then `SET_TO_LIST roots` strip_assume_tac pointer_closure_terminates >>
  `set result SUBSET target` by
    (irule ptr_closure_loop_subset >> goal_assum (drule_at Any) >>
     simp[SET_TO_LIST_INV] >> metis_tac[]) >>
  gvs[pointer_derived_vars_def, pointer_use_vars_def,
      GSYM pointer_closure_next_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem ptr_derived_mono:
  FINITE roots /\ FINITE roots' /\ roots SUBSET roots' ==>
  pointer_derived_vars fn roots SUBSET pointer_derived_vars fn roots'
Proof
  rpt strip_tac >> irule ptr_derived_least >> simp[] >> conj_tac
  >- metis_tac[pointer_derived_vars_closed]
  >> metis_tac[pointer_derived_vars_roots, SUBSET_TRANS]
QED

Theorem ptr_derived_root_witness:
  FINITE R /\ v IN pointer_derived_vars fn R ==>
  ?r. r IN R /\ v IN pointer_derived_vars fn {r}
Proof
  strip_tac >>
  `pointer_derived_vars fn R SUBSET
    {u | ?r. r IN R /\ u IN pointer_derived_vars fn {r}}` suffices_by
    (simp[SUBSET_DEF] >> metis_tac[]) >>
  irule ptr_derived_least >> simp[SUBSET_DEF] >>
  conj_tac
  >- (rpt strip_tac >> qexists `r` >> simp[] >>
      irule pointer_derived_vars_closed >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> qexists `x` >> simp[] >>
  mp_tac (Q.INST [`roots` |-> `{x}`, `fn` |-> `fn`] pointer_derived_vars_roots) >>
  simp[SUBSET_DEF]
QED

Theorem ptr_derived_union:
  FINITE roots1 /\ FINITE roots2 ==>
  pointer_derived_vars fn (roots1 UNION roots2) =
  pointer_derived_vars fn roots1 UNION pointer_derived_vars fn roots2
Proof
  strip_tac >> simp[SET_EQ_SUBSET] >> conj_tac
  >- (irule ptr_derived_least >> simp[] >> conj_tac
      >- (rpt strip_tac >>
          metis_tac[pointer_derived_vars_closed, IN_UNION]) >>
      drule_then assume_tac pointer_derived_vars_roots >>
      rev_drule_then assume_tac pointer_derived_vars_roots >>
      fs[SUBSET_DEF] >> metis_tac[]) >>
  simp[UNION_SUBSET] >> conj_tac >>
  irule ptr_derived_mono >> simp[]
QED

Theorem ptr_derived_backward_exclusion:
  FINITE roots /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  is_pointer_preserving_op inst.inst_opcode /\ MEM out inst.inst_outputs /\
  out NOTIN pointer_derived_vars fn roots /\ MEM (Var v) inst.inst_operands ==>
  v NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
  metis_tac[pointer_derived_vars_closed]
QED
