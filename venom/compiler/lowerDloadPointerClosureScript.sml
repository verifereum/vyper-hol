(* The computed pointer use closure terminates over a finite output universe. *)
Theory lowerDloadPointerClosure
Ancestors
  pointerConfinedDefs allocaRemapSSA venomInst unitLabelMapIdentity While pred_set list arithmetic

Theorem ld_pointer_step_outputs[local]:
  set (pointer_use_step fn vars) SUBSET
  set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))
Proof
  simp[SUBSET_DEF, MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
  drule pointer_use_step_mem >> strip_tac >>
  qexists_tac `inst.inst_outputs` >> simp[] >>
  qexists_tac `inst` >> simp[] >>
  metis_tac[mem_fn_insts_intro]
QED

Theorem ld_pointer_additions_decrease[local]:
  FILTER (\v. ~MEM v vars) (pointer_use_step fn vars) <> [] ==>
  CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF
        set (vars ++ FILTER (\v. ~MEM v vars) (pointer_use_step fn vars))) <
  CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set vars)
Proof
  strip_tac >> irule CARD_PSUBSET >> simp[] >>
  qmatch_goalsub_abbrev_tac `U DIFF _` >>
  `set (pointer_use_step fn vars) SUBSET U` by
    simp[Abbr `U`, ld_pointer_step_outputs] >>
  `?v. MEM v (FILTER (\v. ~MEM v vars) (pointer_use_step fn vars))` by
    (Cases_on `FILTER (\v. ~MEM v vars) (pointer_use_step fn vars)` >>
     gvs[] >> metis_tac[]) >>
  `v IN U /\ v NOTIN set vars /\
   v IN set (FILTER (\v. ~MEM v vars) (pointer_use_step fn vars))` by
    (gvs[MEM_FILTER, SUBSET_DEF] >> metis_tac[]) >>
  ASM_SET_TAC[]
QED

Theorem ld_pointer_iteration_terminates:
  !vars. ?result.
    OWHILE ISL (\v. case pointer_use_step_step fn (OUTL v) of
                         NONE => INR (OUTL v)
                       | SOME vs => INL vs) (INL vars) = SOME (INR result) /\
    set (pointer_use_step fn result) SUBSET set result
Proof
  measureInduct_on `CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set vars)` >>
  rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `OWHILE ISL step (INL vars)` >>
  `step (INL vars) =
    if FILTER (\v. ~MEM v vars) (pointer_use_step fn vars) = [] then INR vars
    else INL (vars ++ FILTER (\v. ~MEM v vars) (pointer_use_step fn vars))` by
      (simp[Abbr `step`, pointer_use_step_step_def] >> IF_CASES_TAC >> simp[]) >>
  once_rewrite_tac[OWHILE_THM] >> simp[] >>
  Cases_on `FILTER (\v. ~MEM v vars) (pointer_use_step fn vars) = []`
  >- (simp[Once OWHILE_THM, SUBSET_DEF] >>
      gvs[FILTER_EQ_NIL, EVERY_MEM]) >>
  simp[Abbr `step`] >> first_x_assum irule >>
  simp[] >> drule ld_pointer_additions_decrease >> simp[]
QED

Theorem ld_pointer_use_vars_closed:
  set (pointer_use_step fn (pointer_use_vars fn vars)) SUBSET
  set (pointer_use_vars fn vars)
Proof
  qspec_then `vars` strip_assume_tac ld_pointer_iteration_terminates >>
  simp[pointer_use_vars_def]
QED

Theorem ld_pointer_preserving_output:
  MEM inst (fn_insts fn) /\ is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var v) inst.inst_operands /\ v IN pointer_derived_vars fn roots /\
  MEM out inst.inst_outputs ==>
  out IN pointer_derived_vars fn roots
Proof
  strip_tac >>
  `MEM out (pointer_use_step fn (pointer_use_vars fn (SET_TO_LIST roots)))` by
    (gvs[pointer_derived_vars_def, fn_insts_MEM] >>
     simp[pointer_use_step_def, MEM_FLAT, MEM_MAP] >>
     irule_at Any EQ_REFL >> qexists_tac `bb` >> simp[MEM_FLAT, MEM_MAP] >>
     irule_at Any EQ_REFL >> qexists_tac `inst` >>
     simp[EXISTS_MEM] >>
     `?op. MEM op inst.inst_operands /\
       (case op of Var u => MEM u (pointer_use_vars fn (SET_TO_LIST roots)) | _ => F)` by
       (qexists_tac `Var v` >> simp[]) >>
     IF_CASES_TAC >> simp[] >> metis_tac[]) >>
  simp[pointer_derived_vars_def] >>
  irule (SRULE[SUBSET_DEF] ld_pointer_use_vars_closed) >> simp[]
QED
