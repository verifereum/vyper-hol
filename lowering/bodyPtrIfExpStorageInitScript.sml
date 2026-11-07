Theory bodyPtrIfExpStorageInit
Ancestors
  bodyPtrIfExpStorageControl bodyPtrIfExpAssign bodyPtrIfExpAssignFrame ifJumpPtr
  copyExecution slotCopyExecution fragExec fragGasPathPtr emitHelper compileEnv
  ptrDiscipline venomState venomInst finite_map exprLoweringProps list

Theorem ifexp_copy_initial_code:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  cut.cs_blocks = cs.cs_blocks /\ cut.cs_current_bb = cs.cs_current_bb /\
  isPREFIX cut.cs_current_insts (cs.cs_current_insts ++ slot_copy_init_insts cs) ==>
  fn_has_code cs cut fn
Proof
  strip_tac >> drule slot_copy_lookup >> strip_tac >>
  simp[fn_has_code_def, emitted_blocks_def] >>
  qexists_tac `<|bb_label := cs.cs_current_bb;
    bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>` >> simp[]
QED

Theorem ifexp_copy_initial_assign_path:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {slot_copy_var cs 0}))
    (tn with t_var := tn.t_var |+ (slot_copy_var cs 0,{}))
    (OK ((update_var (slot_copy_var cs 0) 0w s)
      with vs_inst_idx := LENGTH cs.cs_current_insts+1))
Proof
  strip_tac >>
  qabbrev_tac `cut = cs with <|cs_next_id := cs.cs_next_id+1;
    cs_current_insts := cs.cs_current_insts ++
      [mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]]|>` >>
  `emit_inst ASSIGN [Lit 0w] [slot_copy_var cs 0] cs = ((),cut)` by
    simp[Abbr `cut`, emit_inst_def, fresh_id_def, emit_def,
         comp_bind_def, comp_return_def] >>
  `fn_has_code cs cut fn` by
    (irule ifexp_copy_initial_code >>
     simp[Abbr `cut`, slot_copy_init_insts_def] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0])
      (update_var (slot_copy_var cs 0) 0w s))
    (step_taint (mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]) s
      (update_var (slot_copy_var cs 0) 0w s) tn)
    (OK ((update_var (slot_copy_var cs 0) 0w s) with
      vs_inst_idx := LENGTH cut.cs_current_insts))` by
    (irule emit_assign_zero_path_ptr >> simp[eval_operand_def]) >>
  gvs[assign_taint, eval_operand_def, op_taint_def, step_prov_def,
      set_prov_def, out_prov_def, first_prov_def, op_prov_def, mk_inst_def,
      Abbr `cut`]
QED

Theorem ifexp_copy_initial_jump_path:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = cs.cs_current_bb /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts+1 /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to (slot_copy_cond cs) s))
Proof
  strip_tac >>
  qabbrev_tac `cut1 = cs with <|cs_next_id := cs.cs_next_id+1;
    cs_current_insts := cs.cs_current_insts ++
      [mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]]|>` >>
  qabbrev_tac `cut2 = cs with <|cs_next_id := cs.cs_next_id+2;
    cs_current_insts := cs.cs_current_insts ++ slot_copy_init_insts cs|>` >>
  `fn_has_code cs cut2 fn` by
    (irule ifexp_copy_initial_code >> simp[Abbr `cut2`] >> metis_tac[]) >>
  `fn_has_code cut1 cut2 fn` by
    (qpat_x_assum `fn_has_code cs cut2 fn` mp_tac >>
     simp[fn_has_code_def, emitted_blocks_def, Abbr `cut1`, Abbr `cut2`]) >>
  irule if_emit_jump_zero_path_ptr >> simp[] >>
  qexistsl_tac [`cut1`, `cut2`] >>
  simp[Abbr `cut1`, Abbr `cut2`, slot_copy_init_insts_def, APPEND_ASSOC]
QED

Theorem ifexp_copy_initial_path:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {slot_copy_var cs 0}))
    (tn with t_var := tn.t_var |+ (slot_copy_var cs 0,{}))
    (OK (slot_copy_initial cs s))
Proof
  strip_tac >>
  qabbrev_tac `u = (update_var (slot_copy_var cs 0) 0w s)
    with vs_inst_idx := LENGTH cs.cs_current_insts+1` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {slot_copy_var cs 0})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (slot_copy_var cs 0,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u)` by
    (simp[Abbr `u`, Abbr `G1`, Abbr `tn1`] >>
     irule ifexp_copy_initial_assign_path >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 u 0 G1 tn1 (OK (jump_to (slot_copy_cond cs) u))` by
    (irule ifexp_copy_initial_jump_path >> simp[Abbr `u`, update_var_def] >> metis_tac[]) >>
  `jump_to (slot_copy_cond cs) u = slot_copy_initial cs s` by
    simp[Abbr `u`, slot_copy_initial_def, jump_to_def] >>
  fs[Abbr `G1`, Abbr `tn1`] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_copy_initial_transition:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK (slot_copy_initial cs s)) /\
    op_prov G' (Var (slot_copy_var cs 0)) = NONE /\
    op_taint tn' (Var (slot_copy_var cs 0)) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> slot_copy_var cs 0 ==>
      lookup_var x (slot_copy_initial cs s) = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qexistsl_tac [`DRESTRICT G (COMPL {slot_copy_var cs 0})`,
    `tn with t_var := tn.t_var |+ (slot_copy_var cs 0,{})`] >>
  conj_tac >- (irule ifexp_copy_initial_path >> metis_tac[]) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       slot_copy_initial_def, lookup_var_def, update_var_def, jump_to_def]
QED
