(* ASSIGN observations suffice to transport copy-forwarding traversals.
   Non-ASSIGN instructions and their use lists may change freely. *)
Theory invokeCopyFwdTransport
Ancestors
  invokeCopyFwdCommonDefs list pair option pred_set

Definition icf_assign_predecessor_def:
  icf_assign_predecessor dfg v =
    case dfg_get_def dfg v of
      NONE => NONE
    | SOME inst =>
        if inst.inst_opcode = ASSIGN then
          case inst.inst_operands of [Var src] => SOME src | _ => NONE
        else NONE
End

Theorem icf_assign_root_observation:
  icf_assign_root dfg visited v =
    if v IN visited then v
    else case icf_assign_predecessor dfg v of
      NONE => v
    | SOME src => icf_assign_root dfg (v INSERT visited) src
Proof
  CONV_TAC (LHS_CONV (REWR_CONV icf_assign_root_def)) >>
  simp[icf_assign_predecessor_def] >>
  Cases_on `v IN visited` >> simp[] >>
  Cases_on `dfg_get_def dfg v` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `x.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem icf_assign_root_cong:
  !dfg visited v.
    !other. (!x. icf_assign_predecessor dfg x =
                 icf_assign_predecessor other x) ==>
      icf_assign_root dfg visited v = icf_assign_root other visited v
Proof
  recInduct icf_assign_root_ind >> rpt strip_tac >>
  once_rewrite_tac[icf_assign_root_observation] >>
  Cases_on `v IN visited` >> simp[] >>
  Cases_on `icf_assign_predecessor dfg v` >> gvs[] >>
  qpat_x_assum `!inst src. _` irule >>
  simp[] >>
  `icf_assign_predecessor dfg v = SOME x` by metis_tac[] >>
  gvs[icf_assign_predecessor_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem icf_aliases_step_cong:
  (!v out.
    (?inst. MEM inst (dfg_get_uses dfg v) /\
            inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out]) <=>
    (?inst. MEM inst (dfg_get_uses other v) /\
            inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out])) ==>
  !als. icf_aliases_step dfg als = icf_aliases_step other als
Proof
  strip_tac >> gen_tac >>
  `!als. SND (icf_aliases_step dfg als) =
          SND (icf_aliases_step other als)` by
    (simp[EXTENSION, icf_aliases_step_mem] >> metis_tac[]) >>
  `FST (icf_aliases_step dfg als) = FST (icf_aliases_step other als)` by
    simp[icf_aliases_step_changed] >>
  simp[PAIR_FST_SND_EQ]
QED

Theorem icf_collect_aliases_cong:
  (!v out.
    (?inst. MEM inst (dfg_get_uses dfg v) /\
            inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out]) <=>
    (?inst. MEM inst (dfg_get_uses other v) /\
            inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [out])) ==>
  !root. icf_collect_aliases dfg root = icf_collect_aliases other root
Proof
  strip_tac >>
  `icf_aliases_step dfg = icf_aliases_step other` by
    (simp[FUN_EQ_THM] >> irule icf_aliases_step_cong >> metis_tac[]) >>
  simp[icf_collect_aliases_def]
QED

Theorem icf_assign_root_op_cong:
  (!x. icf_assign_predecessor dfg x = icf_assign_predecessor other x) ==>
  !op. icf_assign_root_op dfg op = icf_assign_root_op other op
Proof
  strip_tac >> Cases >> simp[icf_assign_root_op_def] >>
  irule icf_assign_root_cong >> simp[]
QED
