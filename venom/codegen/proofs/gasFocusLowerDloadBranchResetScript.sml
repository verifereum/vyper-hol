(* Reset the ghost prefix at the operationally selected branch destination. *)
Theory gasFocusLowerDloadBranchReset
Ancestors
  lowerDloadPtrBranch lowerDloadPtrRel lowerDloadPtrPhase
  lowerDloadSafetyRelation lowerDloadDefs fmpStageBlockSimCode
  ptrDiscipline pointerConfinedDefs contextCodegenRel venomExecSemantics
  venomInst venomState finite_map pred_set list

Theorem ld_focus_actual_branch_reset:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  MEM i.inst_opcode [JMP;JNZ;DJMP] /\ fn_ptr_ok P f /\
  FDOM G SUBSET fn_pv P f /\ taint_ok f tn i s /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!a v lbl op w. MEM a (fn_insts f) /\ a.inst_opcode = PHI /\
    a.inst_outputs = [v] /\ v IN V /\
    resolve_phi lbl a.inst_operands = SOME op /\ op = Var w ==> w IN V) /\
  lower_dload_function_supply q f = (g,q') /\
  ALL_DISTINCT (MAP (\b. b.bb_label) f.fn_blocks) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) g.fn_blocks) /\
  dload_boundary_core fl lo rs V Ws PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK b' /\ ~b'.vs_halted /\
  enters_block g b' t1 /\ active_inst g j t1 /\
  step_inst fuel C i s = OK b /\ enters_block f b s1 /\ active_inst f ni s1 /\
  ld_envelope q f s1 s1.vs_inst_idx X t1.vs_inst_idx ==>
  dload_control_match q f g s1 t1 ni X 0 /\ j = EL 0 X /\
  (!v. v IN set (fn_ir_vars f) ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
  dload_boundary_core fl lo rs V Ws PG PH (entry_prov f b G) (entry_prov g b' H)
    (entry_taint_vars f b tn) (entry_taint_vars g b' un) s1 t1 cs ds /\
  dload_prefix_match pf C' PH X 0 t1 (entry_prov g b' H) (entry_taint_vars g b' un)
    t1 (entry_prov g b' H) (entry_taint_vars g b' un)
Proof
  strip_tac >>
  drule_all dload_actual_branch_block_tracked >>
  disch_then (qx_choose_then `b0` (qx_choose_then `s2`
    (qx_choose_then `ni0` (qx_choose_then `Y` strip_assume_tac)))) >>
  `b0 = b` by fs[] >>
  qpat_x_assum `b0 = b` SUBST_ALL_TAC >>
  `s2 = s1` by
    (qpat_x_assum `enters_block f b s1` mp_tac >>
     qpat_x_assum `enters_block f b s2` mp_tac >>
     simp[enters_block_def] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `s2 = s1` SUBST_ALL_TAC >>
  `ni0 = ni` by metis_tac[dload_control_match_boundary, active_inst_unique,
    fn_labels_def] >>
  qpat_x_assum `ni0 = ni` SUBST_ALL_TAC >>
  `X = Y` by
    (qpat_x_assum `ld_envelope q f s1 _ X _`
       (qx_choose_then `bb1` (qx_choose_then `bi1` strip_assume_tac) o
        REWRITE_RULE[ld_envelope_def]) >>
     qpat_x_assum `dload_control_match q f g s1 t1 ni Y 0`
       (strip_assume_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        REWRITE_RULE[dload_control_match_def]) >>
     rename1 `bb2 = EL bi2 f.fn_blocks` >>
     `bi1 = bi2` by
       (qspecl_then [`MAP (\bb. bb.bb_label) f.fn_blocks`, `bi1`, `bi2`]
          mp_tac ALL_DISTINCT_EL_IMP >>
        simp[EL_MAP] >> metis_tac[]) >>
     qpat_x_assum `bi1 = bi2` SUBST_ALL_TAC >>
     `bb1 = bb2` by metis_tac[] >>
     qpat_x_assum `bb1 = bb2` SUBST_ALL_TAC >>
     `ub = bs` by metis_tac[] >>
     qpat_x_assum `ub = bs` SUBST_ALL_TAC >>
     `ui = is` by (qpat_x_assum `ui = SND _` SUBST1_TAC >> simp[]) >>
     qpat_x_assum `ui = is` SUBST_ALL_TAC >>
     qpat_x_assum `X = FST _` SUBST1_TAC >>
     qpat_x_assum `ni = EL _ _` (SUBST1_TAC o SYM) >>
     simp[]) >>
  qpat_x_assum `X = Y` SUBST_ALL_TAC >>
  `0 < LENGTH Y` by metis_tac[dload_control_match_expansion] >>
  Cases_on `Y` >- fs[] >> simp[dload_prefix_zero]
QED
