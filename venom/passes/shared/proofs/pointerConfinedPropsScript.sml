(*
 * Properties of pointer_use_vars / pointer_derived_vars.
 *
 * TOP-LEVEL:
 *   pointer_use_step_intro   — a pp instruction reading a listed var adds
 *                              its outputs to pointer_use_step
 *   pointer_use_vars_initial — pointer_use_vars contains its initial list
 *   pointer_use_vars_closed  — pointer_use_vars is closed under
 *                              pointer-preserving instructions
 *   pointer_use_vars_least   — pointer_use_vars lies inside every set that
 *                              contains the initial list and is closed
 *                              under pointer-preserving instructions
 *)

Theory pointerConfinedProps
Ancestors
  allocaRemapSSA pointerConfinedDefs venomInst While
Libs
  listTheory pred_setTheory

Theorem pointer_use_step_intro:
  !fn vars bb inst u v.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ MEM u vars /\
    MEM v inst.inst_outputs ==>
    MEM v (pointer_use_step fn vars)
Proof
  rpt strip_tac >>
  `EXISTS (\op. case op of Var v => MEM v vars | _ => F)
          inst.inst_operands` by
    (simp[EXISTS_MEM] >> qexists_tac `Var u` >> simp[]) >>
  simp[pointer_use_step_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

(* Each unfinished OWHILE step adds a variable from the function's outputs
   that the current list lacks, so induction on the number of outputs still
   missing reaches a fixpoint that contains the starting list. *)
Theorem pointer_use_owhile_fixpoint[local]:
  !n fn l.
    CARD (set (FLAT (MAP (\bb. FLAT (MAP (\inst. inst.inst_outputs)
                                         bb.bb_instructions))
                        fn.fn_blocks)) DIFF set l) = n ==>
    ?r. OWHILE ISL (\w. case pointer_use_step_step fn (OUTL w) of
                          NONE => INR (OUTL w) | SOME vs => INL vs)
               (INL l) = SOME (INR r) /\
        set l SUBSET set r /\ pointer_use_step_step fn r = NONE
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  ONCE_REWRITE_TAC [OWHILE_THM] >> simp[] >>
  Cases_on `pointer_use_step_step fn l` >> simp[]
  >- (ONCE_REWRITE_TAC [OWHILE_THM] >> simp[]) >>
  rename1 `pointer_use_step_step fn l = SOME vs` >>
  qmatch_asmsub_abbrev_tac `CARD (outs DIFF set l)` >>
  first_x_assum (qspec_then `CARD (outs DIFF set vs)` mp_tac) >>
  impl_tac
  >- (gvs[] >> irule CARD_PSUBSET >>
      simp[Abbr `outs`, PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
      qpat_x_assum `pointer_use_step_step _ _ = SOME _` mp_tac >>
      simp[pointer_use_step_step_def] >> rw[] >>
      Cases_on `FILTER (\v. ~MEM v l) (pointer_use_step fn l)` >> gvs[] >>
      `MEM h (FILTER (\v. ~MEM v l) (pointer_use_step fn l))` by simp[] >>
      gvs[MEM_FILTER] >>
      drule pointer_use_step_mem >> strip_tac >>
      qexists_tac `h` >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      metis_tac[]) >>
  disch_then (qspecl_then [`fn`, `vs`] mp_tac) >> simp[Abbr `outs`] >>
  strip_tac >> qexists_tac `r` >> fs[] >>
  qpat_x_assum `pointer_use_step_step _ _ = SOME _` mp_tac >>
  simp[pointer_use_step_step_def] >> rw[] >> fs[SUBSET_DEF]
QED

Theorem pointer_use_vars_fixpoint[local]:
  !fn vars.
    set vars SUBSET set (pointer_use_vars fn vars) /\
    pointer_use_step_step fn (pointer_use_vars fn vars) = NONE
Proof
  rpt gen_tac >> simp[pointer_use_vars_def] >>
  qspecl_then [`CARD (set (FLAT (MAP (\bb. FLAT (MAP (\inst.
                 inst.inst_outputs) bb.bb_instructions)) fn.fn_blocks))
                 DIFF set vars)`, `fn`, `vars`] mp_tac
    pointer_use_owhile_fixpoint >>
  simp[] >> rpt strip_tac >> fs[]
QED

Theorem pointer_use_vars_initial:
  !fn vars v. MEM v vars ==> MEM v (pointer_use_vars fn vars)
Proof
  rpt strip_tac >>
  qspecl_then [`fn`, `vars`] strip_assume_tac pointer_use_vars_fixpoint >>
  gvs[SUBSET_DEF]
QED

Theorem roots_in_pointer_derived_vars:
  !fn roots v. FINITE roots /\ v IN roots ==>
    v IN pointer_derived_vars fn roots
Proof
  rw[pointer_derived_vars_def] >>
  irule pointer_use_vars_initial >>
  metis_tac[MEM_SET_TO_LIST]
QED

Theorem FINITE_alloca_roots:
  !fn. FINITE (alloca_roots fn)
Proof
  rw[alloca_roots_def] >>
  irule SUBSET_FINITE >>
  qexists `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  simp[SUBSET_DEF, MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
  rename1 `MEM ainst (fn_insts fn)` >>
  qexists `ainst.inst_outputs` >> simp[] >>
  (conj_tac >- (qexists `ainst` >> simp[])) >>
  gvs[inst_output_def] >>
  Cases_on `ainst.inst_outputs` >> gvs[inst_output_def] >>
  Cases_on `t` >> gvs[]
QED

Theorem pointer_use_vars_closed:
  !fn vars bb inst u v.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ MEM u (pointer_use_vars fn vars) /\
    MEM v inst.inst_outputs ==>
    MEM v (pointer_use_vars fn vars)
Proof
  rpt strip_tac >>
  qspecl_then [`fn`, `vars`] strip_assume_tac pointer_use_vars_fixpoint >>
  `MEM v (pointer_use_step fn (pointer_use_vars fn vars))` by
    (irule pointer_use_step_intro >> metis_tac[]) >>
  qpat_x_assum `pointer_use_step_step _ _ = NONE` mp_tac >>
  simp[pointer_use_step_step_def] >> rw[] >>
  gvs[FILTER_EQ_NIL, EVERY_MEM]
QED

Theorem pointer_use_vars_least:
  !fn vars pv.
    (!v. MEM v vars ==> v IN pv) /\
    (!bb inst u v.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       is_pointer_preserving_op inst.inst_opcode /\
       MEM (Var u) inst.inst_operands /\ u IN pv /\
       MEM v inst.inst_outputs ==> v IN pv) ==>
    !v. MEM v (pointer_use_vars fn vars) ==> v IN pv
Proof
  rpt gen_tac >> strip_tac >> simp[pointer_use_vars_def] >>
  qmatch_goalsub_abbrev_tac `OWHILE ISL g (INL vars)` >>
  qspecl_then [`ISL`, `g`, `INL vars`]
    mp_tac (DB.fetch "While" "OWHILE_INV_IND"
      |> INST_TYPE [alpha |-> ``:string list + string list``]
      |> Q.INST [`P` |->
           `\s. !v. MEM v (case s of INL l => l | INR l => l) ==> v IN pv`]
      |> SIMP_RULE (srw_ss()) []) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      rename [`ISL xx`] >> Cases_on `xx` >> gvs[Abbr `g`] >>
      Cases_on `pointer_use_step_step fn x` >> gvs[] >>
      qpat_x_assum `pointer_use_step_step _ _ = SOME _` mp_tac >>
      simp[pointer_use_step_step_def] >> rw[] >>
      gvs[MEM_APPEND, MEM_FILTER] >>
      drule pointer_use_step_mem >> strip_tac >> metis_tac[]) >>
  strip_tac >>
  Cases_on `OWHILE ISL g (INL vars)` >> gvs[] >>
  rename1 `OWHILE ISL g (INL vars) = SOME res` >>
  Cases_on `res` >> gvs[]
QED
