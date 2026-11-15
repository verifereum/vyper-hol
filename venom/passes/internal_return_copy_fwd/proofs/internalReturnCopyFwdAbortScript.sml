(* Source-side availability at a discarded REVERT suffix. *)
Theory internalReturnCopyFwdAbort
Ancestors
  internalReturnCopyFwdAlias reachableFnSim o1LowerDloadAvailableSuffix
  venomInst venomExecSemantics ptrDiscipline taintAgree list
  internalReturnCopyFwdPlan arithmetic finite_map

Theorem ircf_assign_prefix_abort_trace:
  frame_reachable vs C stk PG G tn fn
    (EL s.vs_inst_idx bb.bb_instructions) s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ircf_block_plan fn bb bb2 /\
  (!j ii. j < d /\ get_instruction bb (s.vs_inst_idx + j) = SOME ii ==>
    ii.inst_opcode = ASSIGN) /\
  get_instruction bb (s.vs_inst_idx + d) = SOME ri /\
  ri.inst_opcode = REVERT /\ exec_block fuel C bb s = Abort reason s1 ==>
  ?seq off len.
    seq 0 = s /\
    (!j. j <= d ==> (seq j).vs_inst_idx = s.vs_inst_idx + j) /\
    (!j. j < d ==> ?ii u.
      get_instruction bb (s.vs_inst_idx + j) = SOME ii /\
      ii.inst_opcode = ASSIGN /\ step_inst_base ii (seq j) = OK u /\
      seq (SUC j) = (u with vs_inst_idx := SUC (seq j).vs_inst_idx)) /\
    ri.inst_operands = [off;len] /\
    IS_SOME (eval_operand (ircf_redirect_op fn bb bb2 off) (seq d)) /\
    IS_SOME (eval_operand (ircf_redirect_op fn bb bb2 len) (seq d))
Proof
  strip_tac >> drule_all ld_assign_prefix_abort_trace >> strip_tac >>
  rename1 `seq 0 = s` >>
  `!j. j < d ==> ?ii u.
    get_instruction bb (s.vs_inst_idx + j) = SOME ii /\
    ii.inst_opcode = ASSIGN /\ step_inst_base ii (seq j) = OK u /\
    seq (SUC j) = (u with vs_inst_idx := SUC (seq j).vs_inst_idx)` by
    metis_tac[] >>
  `lookup_block (seq d).vs_current_bb fn.fn_blocks = SOME bb /\
   ?Gd tnd. frame_reachable vs C stk PG Gd tnd fn ri (seq d)` by
    (irule frame_reachable_assign_prefix >> goal_assum drule >> simp[] >>
     metis_tac[]) >>
  qexistsl_tac [`seq`, `off`, `len`] >> simp[] >>
  `(seq d).vs_inst_idx = s.vs_inst_idx + d` by simp[] >>
  qpat_x_assum `get_instruction bb (s.vs_inst_idx + d) = SOME ri` mp_tac >>
  simp[get_instruction_def] >> strip_tac >>
  conj_tac >> irule ircf_redirect_reachable_revert_operand >>
  goal_assum drule >> simp[] >> metis_tac[]
QED


Theorem ircf_assign_prefix_abort_domain:
  frame_reachable vs C stk PG G tn fn
    (EL s.vs_inst_idx bb.bb_instructions) s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ircf_block_plan fn bb bb2 /\
  (!j ii. j < d /\ get_instruction bb (s.vs_inst_idx + j) = SOME ii ==>
    ii.inst_opcode = ASSIGN) /\
  get_instruction bb (s.vs_inst_idx + d) = SOME ri /\
  ri.inst_opcode = REVERT /\ exec_block fuel C bb s = Abort reason s1 /\
  s.vs_inst_idx = t.vs_inst_idx /\ s.vs_labels = t.vs_labels /\
  FDOM s.vs_vars = FDOM t.vs_vars ==>
  !fuel' C'. ?u. exec_block fuel' C' bb2 t = Abort reason u
Proof
  strip_tac >>
  `reason = Revert_abort` by (drule_all ld_assign_prefix_abort_reason >> simp[]) >>
  qpat_x_assum `reason = Revert_abort` SUBST_ALL_TAC >>
  drule_all ircf_assign_prefix_abort_trace >> strip_tac >>
  rename1 `seq 0 = s` >>
  rpt gen_tac >> irule ld_available_assign_prefix_revert_pointwise >>
  qexistsl_tac [`seq`, `UNIV`, `d`,
    `ircf_redirect_op fn bb bb2 len`, `ircf_redirect_op fn bb bb2 off`,
    `ri with inst_operands := MAP (ircf_redirect_op fn bb bb2) ri.inst_operands`] >>
  simp[] >> conj_tac
  >- (gen_tac >> simp[FLOOKUP_DEF] >>
      Cases_on `v IN FDOM t.vs_vars` >> simp[]) >>
  reverse conj_tac
  >- (drule ircf_block_plan_fetch_noncopy >>
      disch_then drule >> simp[ADD_COMM]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!j. j < d ==> ?ii u. _` drule >> strip_tac >>
  `get_instruction bb2 (s.vs_inst_idx + j) = SOME ii` by
    (drule ircf_block_plan_fetch_noncopy >>
     disch_then drule >> simp[]) >>
  qexistsl_tac [`ii`, `u`] >> simp[] >> metis_tac[ADD_COMM]
QED

Theorem ircf_assign_prefix_abort_target:
  frame_reachable vs C stk PG G tn fn
    (EL s.vs_inst_idx bb.bb_instructions) s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ircf_block_plan fn bb bb2 /\
  (!j ii. j < d /\ get_instruction bb (s.vs_inst_idx + j) = SOME ii ==>
    ii.inst_opcode = ASSIGN) /\
  get_instruction bb (s.vs_inst_idx + d) = SOME ri /\
  ri.inst_opcode = REVERT /\ exec_block fuel C bb s = Abort reason s1 /\
  taint_agree D X tnA s t ==>
  !fuel' C'. ?u. exec_block fuel' C' bb2 t = Abort Revert_abort u
Proof
  strip_tac >>
  `reason = Revert_abort` by (drule_all ld_assign_prefix_abort_reason >> simp[]) >>
  qpat_x_assum `reason = Revert_abort` SUBST_ALL_TAC >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    (drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_inst_idx`) >> simp[]) >>
  drule taint_agree_labels >> drule taint_agree_var_domain >>
  rpt strip_tac >> drule_all ircf_assign_prefix_abort_domain >> simp[]
QED

Theorem ircf_revert_forward_copy_abort:
  frame_reachable vs C stk PG G tn fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  EVERY ircf_no_dst_write_alias C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ircf_block_plan fn bb bb2 /\ revert_forward_pair bb s.vs_inst_idx j /\
  taint_ok fn tn inst s /\ taint_agree D X tn s t /\
  exec_block fuel C bb s = Abort reason se ==>
  !fuel' C'. ?te. exec_block fuel' C' bb2 t = Abort reason te
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule o1LowerDloadOccurrenceTheory.frame_reachable_occurrence_lift >>
     strip_tac >> drule o1LowerDloadOccurrenceTheory.occ_frame_reachable_annotation >>
     simp[]) >>
  `fn_inst_ids_distinct fn /\ ircf_no_dst_write_alias fn` by
    (gvs[EVERY_MEM] >> metis_tac[venomWfTheory.wf_function_def]) >>
  fs[contextCodegenRelTheory.revert_forward_pair_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   inst = EL s.vs_inst_idx bb.bb_instructions` by gvs[get_instruction_def] >>
  `inst1 = inst` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `inst1 = inst` SUBST_ALL_TAC >>
  `EL s.vs_inst_idx bb2.bb_instructions = inst` by
    (qpat_x_assum `inst = EL _ _` SUBST_ALL_TAC >>
     irule ircf_block_plan_writer >>
     simp[ircf_fwds_def, memLocDefsTheory.mem_write_ops_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    (drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_inst_idx`) >> simp[]) >>
  `get_instruction bb2 t.vs_inst_idx = SOME inst` by
    gvs[get_instruction_def, ircf_block_plan_def] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule taint_agree_operand_clean >>
     goal_assum (drule_at Any) >> gvs[taint_ok_def] >> metis_tac[]) >>
  drule taint_agree_read_fields >> strip_tac >>
  `EL t.vs_inst_idx bb.bb_instructions = inst` by metis_tac[] >>
  qpat_x_assum `inst = EL _ _` (assume_tac o SYM) >>
  qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
  pure_once_rewrite_tac[exec_block_def] >>
  pure_asm_rewrite_tac[] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), is_terminator_def] >>
  reverse strip_tac
  >- (rpt gen_tac >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> simp[] >>
  suspend "copy_suffix"
QED

Resume ircf_revert_forward_copy_abort[copy_suffix]:
  qmatch_goalsub_abbrev_tac `exec_block fuel' C' bb2 tu` >>
  qmatch_asmsub_abbrev_tac `exec_block fuel C bb su = Abort reason se` >>
  `step_inst fuel C inst s = OK s''` by
    (simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[MEM]) >>
  `su.vs_inst_idx = SUC s.vs_inst_idx /\
   su.vs_current_bb = s.vs_current_bb /\
   su.vs_labels = tu.vs_labels /\ FDOM su.vs_vars = FDOM tu.vs_vars /\
   su.vs_inst_idx = tu.vs_inst_idx` by
    (drule taint_agree_labels >> drule taint_agree_var_domain >>
     qpat_x_assum `write_memory_with_expansion _ _ s = s''` (SUBST_ALL_TAC o SYM) >>
     simp[Abbr `su`, Abbr `tu`, venomStateTheory.write_memory_with_expansion_def]) >>
  `su.vs_inst_idx <= j` by simp[] >>
  `get_instruction bb (su.vs_inst_idx + (j - su.vs_inst_idx)) = SOME inst2` by simp[] >>
  `!q ii. q < j - su.vs_inst_idx /\
    get_instruction bb (su.vs_inst_idx + q) = SOME ii ==>
    ii.inst_opcode = ASSIGN` by
    (rpt strip_tac >> first_x_assum irule >>
     qexists_tac `su.vs_inst_idx + q` >> simp[] >> decide_tac) >>
  `active_inst fn inst s /\
   active_inst fn (EL su.vs_inst_idx bb.bb_instructions) su` by
    (conj_tac >> simp[contextCodegenRelTheory.active_inst_def] >> qexists_tac `bb` >>
     gvs[get_instruction_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
               venomExecPropsTheory.lookup_block_label]) >>
  `frame_reachable vs C stk PG (step_prov PG G inst s'')
     (step_taint inst s s'' tn) fn (EL su.vs_inst_idx bb.bb_instructions) su` by
    (drule frame_reachable_next >>
     disch_then (qspecl_then [`EL su.vs_inst_idx bb.bb_instructions`, `s''`, `fuel`] mp_tac) >>
     simp[is_terminator_def] >>
     `su = (s'' with vs_inst_idx := SUC s.vs_inst_idx)` by
       simp[Abbr `su`] >>
     metis_tac[]) >>
  metis_tac[ircf_assign_prefix_abort_domain]
QED

Finalise ircf_revert_forward_copy_abort
