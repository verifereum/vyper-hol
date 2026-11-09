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
  strip_tac >> drule_all ircf_assign_prefix_abort_trace >> strip_tac >>
  rename1 `seq 0 = s` >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    (drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_inst_idx`) >> simp[]) >>
  drule taint_agree_labels >> strip_tac >>
  drule taint_agree_var_domain >> strip_tac >>
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
