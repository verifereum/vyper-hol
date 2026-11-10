(* Finite fixed-point interface for the computed pointer closure. *)
Theory o1LowerDloadClosure
Ancestors
  pointerConfinedDefs pointerConfinedProps ptrDiscipline o1PassContract
  venomInst pred_set list rich_list While

Theorem pointer_use_step_mem:
  MEM v (pointer_use_step fn vars) <=>
  ?inst u. MEM inst (fn_insts fn) /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ MEM u vars /\ MEM v inst.inst_outputs
Proof
  simp[pointer_use_step_def, fn_insts_def, fn_insts_blocks_MEM,
       MEM_FLAT, MEM_MAP, EXISTS_MEM, PULL_EXISTS] >>
  eq_tac >> rpt strip_tac
  >- (gvs[COND_RAND, COND_RATOR] >> Cases_on `op` >> gvs[] >> metis_tac[]) >>
  qexists_tac `bb` >> qexists_tac `inst` >>
  simp[COND_RAND, COND_RATOR] >>
  qexists_tac `Var u` >> simp[]
QED

Theorem pointer_use_step_output_bound:
  set (pointer_use_step fn vars) SUBSET
  set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))
Proof
  simp[SUBSET_DEF, pointer_use_step_mem, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem pointer_use_step_decreases:
  pointer_use_step_step fn vars = SOME next ==>
  CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set next) <
  CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set vars)
Proof
  qmatch_goalsub_abbrev_tac `CARD (U DIFF _)` >>
  pure_rewrite_tac[pointer_use_step_step_def, LET_THM] >>
  Cases_on `FILTER (\v. ~MEM v vars) (pointer_use_step fn vars) = []` >>
  asm_rewrite_tac[] >>
  strip_tac >> gvs[Excl "CARD_DIFF", Excl "CARD_UNION"] >>
  irule CARD_PSUBSET >>
  conj_tac >- simp[Abbr `U`] >>
  `?v. MEM v (FILTER (\v. ~MEM v vars) (pointer_use_step fn vars))` by
    (Cases_on `FILTER (\v. ~MEM v vars) (pointer_use_step fn vars)` >> gvs[] >> metis_tac[]) >>
  `set (pointer_use_step fn vars) SUBSET U` by
    simp[Abbr `U`, pointer_use_step_output_bound] >>
  gvs[MEM_FILTER] >>
  simp[PSUBSET_DEF, SUBSET_DEF, EXTENSION, MEM_FILTER] >>
  qexists_tac `v` >> fs[SUBSET_DEF]
QED

Theorem pointer_use_iteration_terminates:
  !fn vars. ?result.
    OWHILE ISL
      (\v. case pointer_use_step_step fn (OUTL v) of
              NONE => INR (OUTL v) | SOME vs => INL vs)
      (INL vars) = SOME (INR result) /\
    set vars SUBSET set result /\
    set (pointer_use_step fn result) SUBSET set result
Proof
  gen_tac >>
  completeInduct_on
    `CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set vars)` >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[OWHILE_THM] >> simp[] >>
  Cases_on `pointer_use_step_step fn vars` >> simp[]
  >- (qexists_tac `vars` >> once_rewrite_tac[OWHILE_THM] >> simp[] >>
      gvs[pointer_use_step_step_def, AllCaseEqs(), FILTER_EQ_NIL,
          EVERY_MEM, SUBSET_DEF]) >>
  rename1 `pointer_use_step_step fn vars = SOME next` >>
  drule pointer_use_step_decreases >> strip_tac >>
  gvs[Excl "CARD_DIFF"] >>
  qpat_x_assum `!m. _` drule >>
  disch_then (qspecl_then [`fn`, `next`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `result` >> simp[] >>
  gvs[pointer_use_step_step_def, AllCaseEqs(), SUBSET_DEF] >>
  metis_tac[MEM_APPEND]
QED

Theorem pointer_use_vars_closed:
  !fn vars. set (pointer_use_step fn (pointer_use_vars fn vars)) SUBSET
  set (pointer_use_vars fn vars)
Proof
  rpt gen_tac >>
  qspecl_then [`fn`, `vars`] strip_assume_tac pointer_use_iteration_terminates >>
  simp[pointer_use_vars_def]
QED

Theorem pointer_derived_vars_forward:
  FINITE roots /\ MEM inst (fn_insts fn) /\
  is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var u) inst.inst_operands /\ u IN pointer_derived_vars fn roots /\
  MEM v inst.inst_outputs ==> v IN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`, `SET_TO_LIST roots`] pointer_use_vars_closed) >>
  simp[SUBSET_DEF, pointer_use_step_mem] >>
  gvs[pointer_derived_vars_def] >> metis_tac[]
QED

Theorem FINITE_ptr_roots:
  FINITE (ptr_roots P fn)
Proof
  irule SUBSET_FINITE >>
  qexists_tac `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  simp[SUBSET_DEF, ptr_roots_def, alloca_roots_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >> rpt strip_tac >>
  qexists_tac `inst` >> simp[] >>
  gvs[inst_output_def, AllCaseEqs()]
QED

Theorem fn_pv_forward:
  MEM inst (fn_insts fn) /\ is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var u) inst.inst_operands /\ u IN fn_pv P fn /\
  MEM v inst.inst_outputs ==> v IN fn_pv P fn
Proof
  simp[fn_pv_def] >> metis_tac[pointer_derived_vars_forward, FINITE_ptr_roots]
QED

Theorem ptr_roots_subset_fn_pv:
  ptr_roots P fn SUBSET fn_pv P fn
Proof
  simp[SUBSET_DEF, fn_pv_def] >>
  metis_tac[roots_in_pointer_derived_vars, FINITE_ptr_roots]
QED
