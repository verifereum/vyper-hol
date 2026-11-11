Theory symPlannerInput
Ancestors
  symPlannerMoves symPlannerBase symPlannerScratch stackPlanGen stackPlanOps
  stackModel stackOpSim planExec asmSymSem asmSem codegenSymRel list
  deepResidualBudget allocMono generatedPrefixSim

Theorem sym_push_kind_step:
  sym_kinds_ok cplan fn ret srest ps ss /\ op_kind_ok fn ret op sv ==>
  ?last. sym_set_stack (sv :: ss.sym_stack) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_push op ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> simp[sym_set_stack_def, asm_next_def,
    sym_kinds_ok_base_change, sym_kinds_ok_push]
QED

Theorem sym_exec_push_kind:
  sym_kinds_ok cplan fn ret srest ps ss /\ op_kind_ok fn ret op sv /\
  execute_plan initial_fmp [sop] = [inst] /\
  sym_step p env inst ss = sym_set_stack (sv :: ss.sym_stack) ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [sop]) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp [sop])) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_push op ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [sop]) /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  rw[] >> drule_all_then strip_assume_tac sym_push_kind_step >>
  metis_tac[sym_steps_singleton]
QED

Theorem sym_exec_push_label:
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOPushLabel l]) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp [SOPushLabel l])) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_push (Label l) ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [SOPushLabel l]) /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> irule sym_exec_push_kind >>
  dsimp[execute_plan_def, exec_stack_op_def, sym_step_def, op_kind_ok_def]
QED

Theorem sym_exec_push_literal:
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOPush (Lit v)]) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp [SOPush (Lit v)])) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_push (Lit v) ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [SOPush (Lit v)]) /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  rw[execute_plan_def, exec_stack_op_def] >>
  drule_then (qspec_then `env` SUBST1_TAC) sym_steps_singleton >>
  simp[sym_step_push_bytes, sym_kinds_ok_base_change,
    sym_kinds_ok_push, op_kind_ok_def, asm_next_def]
QED

Theorem sym_input_dup[local]:
  stack_get_depth op ps.ps_stack = SOME dist /\ do_dup dist ps = (ops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> irule sym_do_dup >> metis_tac[planWfTheory.stack_get_depth_bound]
QED

Theorem sym_input_var[local]:
  (if MEM v nl then
     case stack_get_depth (Var v) ps.ps_stack of
       NONE => ([],ps) | SOME dist => do_dup dist ps
   else ([],ps)) = (ops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> Cases_on `MEM v nl`
  >- (Cases_on `stack_get_depth (Var v) ps.ps_stack`
      >- gvs[execute_plan_def, sym_steps_def] >>
      irule sym_input_dup >> gvs[SF SFY_ss]) >>
  gvs[execute_plan_def, sym_steps_def]
QED

Theorem sym_emit_one_input_unspilled:
  opc <> INVOKE /\
  ~(is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_one_input opc nl op ps = (ops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> Cases_on `op`
  >- (gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def] >>
      drule_all sym_exec_push_literal >> metis_tac[arithmeticTheory.ADD_SYM]) 
  >- (irule sym_input_var >>
      gvs[SF SFY_ss, emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
        GSYM pairTheory.LAMBDA_PROD]) >>
  gvs[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def] >>
  drule_all sym_exec_push_label >> metis_tac[arithmeticTheory.ADD_SYM]
QED

Theorem input_restore_ready[local]:
  do_restore op ps = (rops,midps) /\
  emit_one_input opc nl op midps = (sops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf midps.ps_alloc midps.ps_spilled /\
  ~(is_var_operand op /\ IS_SOME (FLOOKUP midps.ps_spilled op)) /\
  r.sr_spill_base <= midps.ps_alloc.sa_spill_base /\
  midps.ps_alloc.sa_next_offset <= r.sr_spill_end
Proof
  strip_tac >>
  drule_then assume_tac do_restore_not_spilled >>
  drule_then assume_tac do_restore_spill_base >>
  drule_then assume_tac emit_one_input_next_offset >>
  gvs[] >> metis_tac[do_restore_layout_wf, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem sym_input_restore_finish[local]:
  sym_steps p env (LENGTH (execute_plan initial_fmp rops)) ss = SymOK mid /\
  sym_kinds_ok cplan fn ret srest midps mid /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp rops) /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
    FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  opc <> INVOKE /\
  ~(is_var_operand op /\ IS_SOME (FLOOKUP midps.ps_spilled op)) /\
  emit_one_input opc nl op midps = (sops,out) /\
  spill_alloc_layout_wf midps.ps_alloc midps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= midps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) sops /\
  asm_block_at p mid.sym_base.as_pc (execute_plan initial_fmp sops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp (rops ++ sops))) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (rops ++ sops)) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule_all_then (qspec_then `env` (qx_choose_then `last` strip_assume_tac))
    sym_emit_one_input_unspilled >>
  qexists_tac `last` >>
  pure_rewrite_tac[execute_plan_append, LENGTH_APPEND] >>
  ho_match_mp_tac sym_steps_frame_compose >> asm_rewrite_tac[]
QED

Theorem sym_input_restore_run[local]:
  opc <> INVOKE /\ do_restore op ps = (rops,midps) /\
  emit_one_input opc nl op midps = (sops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) rops /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) sops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp rops) /\
  asm_block_at p (ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp rops))
    (execute_plan initial_fmp sops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp (rops ++ sops))) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (rops ++ sops)) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_all_then strip_assume_tac input_restore_ready >>
  `EVERY (\s. case s of SORestore off => off < dimword(:256) | _ => T) rops`
    by (irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >> Cases >> simp[]) >>
  drule_all_then (qspecl_then [`r`, `env`] (qx_choose_then `mid` strip_assume_tac))
    sym_do_restore >>
  ho_match_mp_tac sym_input_restore_finish >> asm_rewrite_tac[]
QED

Theorem sym_input_spilled[local]:
  is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op) /\
  opc <> INVOKE /\
  emit_one_input opc nl op ps = (ops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  Cases_on `do_restore op ps` >> rename1 `do_restore op ps = (rops,midps)` >>
  drule_all_then assume_tac emit_one_input_restore_decompose >>
  Cases_on `emit_one_input opc nl op midps` >>
  rename1 `emit_one_input opc nl op midps = (sops,finalps)` >>
  `ops = rops ++ sops /\ out = finalps` by
    (qpat_x_assum `emit_one_input opc nl op ps = _` mp_tac >> simp[]) >>
  qpat_x_assum `ops = _` SUBST1_TAC >>
  qpat_x_assum `out = _` SUBST1_TAC >>
  irule sym_input_restore_run >>
  gvs[SF SFY_ss, execute_plan_append, asm_block_at_append, EVERY_APPEND]
QED

Theorem sym_emit_one_input:
  opc <> INVOKE /\
  emit_one_input opc nl op ps = (ops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)`
  >- (irule sym_input_spilled >> metis_tac[]) >>
  irule sym_emit_one_input_unspilled >> metis_tac[]
QED

Theorem input_cons_ready[local]:
  emit_one_input opc nl op ps = (hops,midps) /\
  emit_input_plan opc rest next_live midps = (tops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf midps.ps_alloc midps.ps_spilled /\
  r.sr_spill_base <= midps.ps_alloc.sa_spill_base /\
  midps.ps_alloc.sa_next_offset <= r.sr_spill_end
Proof
  strip_tac >> drule_then assume_tac emit_one_input_spill_base >>
  drule_then assume_tac emit_input_plan_next_offset >>
  metis_tac[emit_one_input_layout_wf, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem sym_input_cons_run[local]:
  (!ps ops out ss.
    opc <> INVOKE /\
    emit_input_plan opc rest nl ps = (ops,out) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
    out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    sym_kinds_ok cplan fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
      sym_kinds_ok cplan fn ret srest out last /\
      last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
        FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)) ==>
  !ps ops out ss.
  opc <> INVOKE /\
  emit_input_plan opc (op::rest) nl ps = (ops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `emit_one_input opc (operand_vars rest ++ nl) op ps` >>
  rename1 `emit_one_input opc (operand_vars rest ++ nl) op ps = (hops,midps)` >>
  Cases_on `emit_input_plan opc rest nl midps` >>
  rename1 `emit_input_plan opc rest nl midps = (tops,finalps)` >>
  `ops = hops ++ tops /\ out = finalps` by
    (qpat_x_assum `emit_input_plan opc (op::rest) nl ps = _` mp_tac >>
     simp[emit_input_plan_def]) >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac input_cons_ready >>
  rule_assum_tac (PURE_REWRITE_RULE [EVERY_APPEND, execute_plan_append,
    asm_block_at_append]) >>
  rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  drule_all_then (qspec_then `env` (qx_choose_then `mid` strip_assume_tac))
    sym_emit_one_input >>
  `asm_block_at p mid.sym_base.as_pc (execute_plan initial_fmp tops)`
    by asm_rewrite_tac[] >>
  qpat_x_assum `!ps ops out ss. _`
    (qspecl_then [`midps`, `tops`, `finalps`, `mid`]
      (drule_all_then (qx_choose_then `last` strip_assume_tac))) >>
  qexists_tac `last` >>
  pure_rewrite_tac[execute_plan_append, LENGTH_APPEND] >>
  ho_match_mp_tac sym_steps_frame_compose >> asm_rewrite_tac[]
QED

Theorem sym_emit_input_plan:
  !operands ps ops out ss.
  opc <> INVOKE /\
  emit_input_plan opc operands nl ps = (ops,out) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  out.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest out last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  Induct
  >- simp[emit_input_plan_def, execute_plan_def, sym_steps_def] >>
  drule_then MATCH_ACCEPT_TAC sym_input_cons_run
QED
