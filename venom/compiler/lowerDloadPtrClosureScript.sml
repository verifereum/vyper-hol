Theory lowerDloadPtrClosure
Ancestors
  pointerConfinedDefs venomInst o1PassContract list pred_set While

Theorem pointer_use_step_member:
  MEM y (pointer_use_step fn xs) <=>
  ?i v. MEM i (fn_insts fn) /\
        is_pointer_preserving_op i.inst_opcode /\
        MEM (Var v) i.inst_operands /\ MEM v xs /\ MEM y i.inst_outputs
Proof
  simp[pointer_use_step_def, fn_insts_def, fn_insts_blocks_MEM,
       MEM_FLAT, MEM_MAP, EXISTS_MEM, PULL_EXISTS] >>
  eq_tac >> rpt strip_tac >> gvs[COND_RAND, COND_RATOR, AllCaseEqs()]
  >- (Cases_on `op` >> gvs[] >> metis_tac[]) >>
  qexistsl [`bb`,`i`] >> simp[] >> qexists_tac `Var v` >> simp[]
QED

Theorem pointer_use_step_outputs:
  set (pointer_use_step fn xs) SUBSET
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))
Proof
  simp[SUBSET_DEF, pointer_use_step_member, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem pointer_use_update_decreases:
  pointer_use_step_step fn xs = SOME ys ==>
  CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set ys) <
  CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set xs)
Proof
  pure_rewrite_tac[pointer_use_step_step_def, LET_THM, BETA_THM] >>
  BETA_TAC >> IF_CASES_TAC >- simp[] >>
  pure_rewrite_tac[optionTheory.SOME_11] >>
  disch_then (SUBST1_TAC o SYM) >>
  irule CARD_PSUBSET >>
  conj_tac >- simp[] >>
  simp[PSUBSET_DEF, SUBSET_DEF, MEM_FILTER, EXTENSION] >>
  fs[FILTER_EQ_NIL, EVERY_MEM] >>
  mp_tac pointer_use_step_outputs >> simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem pointer_use_loop_terminates:
  !fn xs. ?ys.
    OWHILE ISL
      (\v. case pointer_use_step_step fn (OUTL v) of
             NONE => INR (OUTL v) | SOME vs => INL vs) (INL xs) =
      SOME (INR ys) /\ pointer_use_step_step fn ys = NONE /\
    set xs SUBSET set ys
Proof
  gen_tac >>
  measureInduct_on `CARD
    (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set xs)` >>
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  Cases_on `pointer_use_step_step fn xs`
  >- (qexists_tac `xs` >> simp[Once OWHILE_THM] >>
      simp[Once OWHILE_THM]) >>
  rename1 `pointer_use_step_step fn xs = SOME next` >>
  `CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set next) <
   CARD (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) DIFF set xs)` by
    metis_tac[pointer_use_update_decreases] >>
  first_x_assum drule >>
  disch_then (qspecl_then [`fn`,`next`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `ys` >> simp[Once OWHILE_THM] >>
  `set xs SUBSET set next` by
    (gvs[pointer_use_step_step_def, AllCaseEqs()] >> simp[]) >>
  metis_tac[SUBSET_TRANS]
QED

Theorem pointer_use_vars_contains:
  set xs SUBSET set (pointer_use_vars fn xs)
Proof
  qspecl_then [`fn`,`xs`] strip_assume_tac pointer_use_loop_terminates >>
  simp[pointer_use_vars_def]
QED

Theorem pointer_use_vars_closed:
  set (pointer_use_step fn (pointer_use_vars fn xs)) SUBSET
  set (pointer_use_vars fn xs)
Proof
  qspecl_then [`fn`,`xs`] strip_assume_tac pointer_use_loop_terminates >>
  simp[pointer_use_vars_def] >>
  gvs[pointer_use_step_step_def, AllCaseEqs(), FILTER_EQ_NIL,
      EVERY_MEM, SUBSET_DEF]
QED

Theorem pointer_use_vars_least:
  EVERY X xs /\
  (!i v w. MEM i (fn_insts fn) /\
    is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
    X v /\ MEM w i.inst_outputs ==> X w) ==>
  EVERY X (pointer_use_vars fn xs)
Proof
  strip_tac >> simp[pointer_use_vars_def] >>
  qabbrev_tac `loopfn = \v:string list + string list.
    case pointer_use_step_step fn (OUTL v) of
      NONE => INR (OUTL v) | SOME vs => INL vs` >>
  mp_tac (DB.fetch "While" "OWHILE_INV_IND"
    |> INST_TYPE [alpha |-> ``:string list + string list``] |> Q.INST
    [`P` |-> `\s:string list + string list.
       case s of INL l => EVERY X l | INR l => EVERY X l`]) >>
  disch_then (qspecl_then [`ISL`,`loopfn`,`INL xs`] mp_tac) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >> rename1 `ISL st` >> Cases_on `st` >> gvs[Abbr `loopfn`] >>
      Cases_on `pointer_use_step_step fn x` >> simp[] >>
      gvs[pointer_use_step_step_def, AllCaseEqs(), EVERY_APPEND,
          EVERY_FILTER, EVERY_MEM, pointer_use_step_member] >> metis_tac[]) >>
  strip_tac >> Cases_on `OWHILE ISL loopfn (INL xs)` >> simp[] >>
  Cases_on `x` >> simp[] >> first_x_assum (qspec_then `INR y` mp_tac) >> simp[]
QED

Theorem pointer_derived_vars_induction:
  FINITE roots /\ (!v. v IN roots ==> X v) /\
  (!i v w. MEM i (fn_insts fn) /\
    is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
    X v /\ MEM w i.inst_outputs ==> X w) ==>
  !w. w IN pointer_derived_vars fn roots ==> X w
Proof
  strip_tac >>
  `EVERY X (pointer_use_vars fn (SET_TO_LIST roots))` by
    (irule pointer_use_vars_least >>
     simp[EVERY_MEM, MEM_SET_TO_LIST] >> metis_tac[]) >>
  gvs[pointer_derived_vars_def, EVERY_MEM]
QED

Theorem pointer_derived_vars_edge:
  FINITE roots /\ MEM i (fn_insts fn) /\
  is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
  v IN pointer_derived_vars fn roots /\ MEM w i.inst_outputs ==>
  w IN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  gvs[pointer_derived_vars_def] >>
  mp_tac (pointer_use_vars_closed |> Q.INST [`xs` |-> `SET_TO_LIST roots`]) >>
  simp[SUBSET_DEF, pointer_use_step_member] >> metis_tac[]
QED

Theorem pointer_derived_vars_mono:
  !R S. FINITE R /\ FINITE S /\ R SUBSET S ==>
  pointer_derived_vars fn R SUBSET pointer_derived_vars fn S
Proof
  qx_gen_tac `roots1` >> qx_gen_tac `roots2` >>
  strip_tac >> simp[SUBSET_DEF] >>
  ho_match_mp_tac pointer_derived_vars_induction >> simp[] >> conj_tac
  >- (mp_tac (pointer_use_vars_contains |>
        Q.INST [`xs` |-> `SET_TO_LIST roots2`]) >>
      gvs[pointer_derived_vars_def, SUBSET_DEF, MEM_SET_TO_LIST] >> metis_tac[]) >>
  metis_tac[pointer_derived_vars_edge]
QED
