Theory pointerClosure
Ancestors pointerConfinedDefs While pred_set list allocaRemapSSA
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
