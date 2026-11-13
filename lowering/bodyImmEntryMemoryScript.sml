(* Memory-safe initialization for immutable array iteration. *)
Theory bodyImmEntryMemory
Ancestors
  whitelistForIterImmFrag stmtForArrayMemoryEntry
  exprSimBopRestWordTail exprSimBopRestWordLoadSafety
  bodyMemoryDefs allocaHistory fragGasSeqMem fragGasMode fragExecMem
  memSafeRun instMemFrontier gasCount venomExecProps venomInstProofs
  stmtSimProps exprLoweringProps context emitHelper compileEnv
  words arithmetic list rich_list finite_map
  fragGasPathMem fragExec venomInst venomState venomExecSemantics
  exprSimBopRestWordLayout exprSimProps localPtrsProps
  whitelistForIterImmCopy whitelistForIterImmLoop exprSimCopy
  bodyLiteralBufferMemory emitHelperProps
  stmtSimForArrayLoop loweringPosts loweringStateRelDefs
Libs
  monadsyntax

Theorem immutable_inst_seq_jump_mem[local]:
  !code s t ctx func bb iid lbl.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions =
      code ++ [mk_inst iid JMP [Label lbl] []] /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) code /\
    run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t ==>
    gas_marked_path T ctx func s 0 (OK (jump_to lbl t))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `~t.vs_halted` by
    (drule (cj 1 gas_path_mem_exec) >>
     disch_then (mp_tac o MATCH_MP fragGasPathTheory.gas_path_normal) >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule run_inst_seq_preserves_field >> goal_assum (drule_at Any) >>
     rpt strip_tac >> fs[EVERY_MEM] >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by metis_tac[] >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all step_preserves_control_flow >> simp[]) >>
  `s.vs_inst_idx + LENGTH code < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP]) >>
  `get_instruction bb (s.vs_inst_idx + LENGTH code) =
     SOME (mk_inst iid JMP [Label lbl] [])` by
    (`DROP (s.vs_inst_idx + LENGTH code) bb.bb_instructions =
       [mk_inst iid JMP [Label lbl] []]` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP (LENGTH code)`) >>
        simp[DROP_DROP, DROP_LENGTH_APPEND, ADD_COMM]) >>
     simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = [_]` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  `gas_path_mem_edge ctx func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)
     0 (OK (jump_to lbl t))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst iid JMP [Label lbl] []` >>
     simp[gas_count_step_def, mem_safe_step_non_invoke, step_inst_non_invoke,
          mk_inst_def, inst_dload_in_section_def, is_terminator_def,
          step_jmp_behavior, jump_to_def] >>
     conj_tac >- fs[ADD_COMM, mk_inst_def] >>
     conj_tac >- simp[below_frontier_no_ranges] >>
     disj2_tac >> disj1_tac >> qexists_tac `lbl` >> simp[]) >>
  `gas_path_mem ctx func (jump_to lbl t) 0 (OK (jump_to lbl t))` by
    (irule (cj 1 gas_path_mem_rules) >> simp[jump_to_def]) >>
  drule (cj 2 gas_path_mem_rules) >> disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `gas_path_mem _ _ s _ _` mp_tac >>
  disch_then (mp_then Any mp_tac gas_path_mem_then) >>
  disch_then drule >> simp[gas_marked_path_def]
QED

Theorem immutable_length_load_mem[local]:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
    (n2w off) es s /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
  LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av /\
  compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off)) sa = (lvo,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ret_pc_ok cenv sa s /\ alloca_history func s /\ fn_inst_ids_distinct func ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    stmt_state_rel ctx func cenv cx es u /\ ret_pc_ok cenv sa u /\
    array_caller_frame sa s u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    alloca_history func u
Proof
  strip_tac >>
  `context$compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode
     (Lit (n2w off)) sa = (lvo,sb)` by simp[compile_ptr_load_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off : bytes32)` by simp[eval_operand_def] >>
  drule_all exprSimBopRestWordLoadsTheory.rest_word_array_immutable_header >> strip_tac >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (fs[stmt_state_rel_def, loweringStateRelDefsTheory.immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand lvo t = SOME (n2w (LENGTH vs))` by
    (drule (Q.INST [`b` |-> `0w`] exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run) >> simp[] >>
     disch_then (qspecl_then [`s`, `n2w off`] mp_tac) >>
     Cases_on `cenv.ce_is_ctor` >> Cases_on `cenv.ce_imm_alloca` >> gvs[WORD_ADD_0]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all rest_word_array_immutable_header_mem_ok >> simp[]) >>
  drule (Q.INST [`memory` |-> `T`] rest_word_ptr_load_marked) >> simp[] >>
  disch_then drule_all >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run_frame >> simp[] >>
  disch_then drule >> strip_tac >>
  drule rest_word_ptr_load_fresh >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (simp[lookup_var_def] >> rpt strip_tac >> first_x_assum irule >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = s with vs_vars := t.vs_vars` SUBST1_TAC >>
     irule stmt_state_rel_vars_frame >> simp[lookup_var_def] >>
     fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_code >> simp[] >> strip_tac >>
     `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
       (gvs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
       (fs[EVERY_MEM] >> rpt strip_tac >>
        qpat_x_assum `!i. MEM i _ ==> _` drule >>
        simp[] >> rpt strip_tac >> gvs[is_terminator_def]) >>
     `alloca_inv s` by fs[stmt_state_rel_def] >>
     drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >>
     simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, array_caller_frame_def, ret_pc_ok_def,
       lookup_var_def] >>
  conj_tac >- (Cases_on `lvo` >> gvs[eval_operand_def, lookup_var_def, ret_pc_ok_def] >> metis_tac[]) >>
  conj_tac >- (conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
    qpat_x_assum `t = s with vs_vars := t.vs_vars` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `t = s with vs_vars := t.vs_vars` SUBST1_TAC >> simp[]
QED

Theorem immutable_allocate_initialize_mem[local]:
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
         mk_inst e3 ISZERO [Var g] [vld];
         mk_inst e4 ASSERT [Var vld] []] else []) ++
      [mk_inst e5 JMP [Label cond_lbl] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  stmt_state_rel ctx func cenv cx es s0 /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand lvo s0 = SOME (n2w (LENGTH vs)) /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  ret_pc_ok cenv st s0 /\ ALL_DISTINCT [p; idx; g; vld] /\
  not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes idx /\
  not_local_ptr cenv es.scopes g /\ not_local_ptr cenv es.scopes vld /\
  (!x. lvo = Var x ==> ~MEM x [p; idx; g; vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [p; idx; g; vld]) /\
  alloca_history func s0 ==>
  ?dst cc.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond_lbl st 0 es cc /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s0 cc /\
    gas_marked_path T ctx func s0 0 (OK cc) /\
    cc.vs_memory = s0.vs_memory /\ s0.vs_alloca_next <= cc.vs_alloca_next /\
    alloca_history func cc
Proof
  strip_tac >> fs[ALL_DISTINCT] >>
  `eval_operand (Lit (n2w off)) s0 = SOME (n2w off : bytes32)` by simp[eval_operand_def] >>
  `!x. Lit (n2w off : bytes32) = Var x ==> x <> p` by simp[] >>
  drule_all stmtSimForArrayFragTheory.array_allocate_ready >> strip_tac >>
  rename1 `exec_alloca ainst s0 (n2w sz : bytes32) = OK s1` >>
  rename1 `lookup_var p s1 = SOME dst` >>
  drule_all stmtSimForArrayFragTheory.array_alloca_frame >> strip_tac >>
  `step_inst_base ainst s0 = OK s1` by
    simp[step_inst_base_opcode_eqs, eval_operand_def] >>
  `gas_marked_path T ctx func s0 0 (OK (jump_to entry s1))` by
    (irule immutable_inst_seq_jump_mem >> simp[] >>
     qexistsl_tac [`[ainst]`, `j`] >>
     simp[DROP_LENGTH_APPEND, run_inst_seq_def, is_terminator_def,
          run_inst_seq_mem_ok_def, inst_dload_in_section_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `s1.vs_labels = s0.vs_labels /\ s1.vs_memory = s0.vs_memory /\
   s0.vs_alloca_next <= s1.vs_alloca_next` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def] >>
     gvs[AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  `eval_operand lvo s1 = SOME (n2w (LENGTH vs))` by
    (Cases_on `lvo` >> gvs[eval_operand_def] >> metis_tac[]) >>
  qabbrev_tac `e0 = jump_to entry s1` >>
  `eval_operand lvo e0 = SOME (n2w (LENGTH vs)) /\
   e0.vs_current_bb = entry /\ e0.vs_inst_idx = 0 /\ ~e0.vs_halted` by
    (Cases_on `lvo` >> gvs[Abbr `e0`, jump_to_def, eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `is = [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
    if dyn then
      [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] []] else []` >>
  qabbrev_tac `e4s = if dyn then
    update_var vld 1w (update_var g 0w (update_var idx 0w e0))
    else update_var idx 0w e0` >>
  `run_inst_seq is e0 = OK e4s` by
    (qunabbrev_tac `is` >> qunabbrev_tac `e4s` >>
     irule whitelistForIterImmLoopTheory.immutable_entry_block_run >> simp[ALL_DISTINCT] >>
     conj_tac >- metis_tac[] >> qexists_tac `LENGTH vs` >> simp[]) >>
  `gas_marked_path T ctx func e0 0 (OK (jump_to cond_lbl e4s))` by
    (irule immutable_inst_seq_jump_mem >> simp[] >> qexists_tac `e5` >>
     gvs[Abbr `is`, is_terminator_def] >>
     conj_tac
     >- (Cases_on `dyn` >> simp[is_terminator_def]) >>
     irule run_inst_seq_mem_ok_every >>
     Cases_on `dyn` >> simp[mk_inst_def, inst_dload_in_section_def,
                            below_frontier_no_ranges]) >>
  qabbrev_tac `cc = jump_to cond_lbl e4s` >>
  suspend "allocation_finish"
QED
Resume immutable_allocate_initialize_mem[allocation_finish]:
  `!x. x <> idx /\ x <> g /\ x <> vld ==> lookup_var x cc = lookup_var x s1` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `e4s`, Abbr `e0`,
       jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `cc.vs_allocas = s1.vs_allocas /\ cc.vs_current_bb = cond_lbl /\
   cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\ cc.vs_memory = s1.vs_memory /\
   cc.vs_alloca_next = s1.vs_alloca_next` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `e4s`, Abbr `e0`,
       jump_to_def, update_var_def]) >>
  `stmt_state_rel ctx func cenv cx es cc` by
    (Cases_on `dyn` >> simp[Abbr `cc`, stmt_state_rel_jump_to, Abbr `e4s`] >>
     rpt (irule stmt_state_rel_update_var >> simp[]) >>
     simp[Abbr `e0`, stmt_state_rel_jump_to]) >>
  `lookup_var idx cc = SOME (n2w 0)` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `e4s`, jump_to_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var p cc = SOME dst` by metis_tac[] >>
  `ret_pc_ok cenv st cc` by
    (Cases_on `dyn` >> simp[Abbr `cc`, ret_pc_ok_jump_to, Abbr `e4s`,
       array_ret_pc_update, Abbr `e0`]) >>
  `cc.vs_labels = s1.vs_labels` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `e4s`, Abbr `e0`,
       jump_to_def, update_var_def]) >>
  qexistsl_tac [`dst`, `cc`] >> rpt conj_tac
  >- simp[array_loop_inv_def, eval_operand_def]
  >- (Cases_on `lvo` >> gvs[eval_operand_def] >> metis_tac[])
  >- (simp[array_caller_frame_def] >> metis_tac[])
  >- (drule_all gas_marked_path_then >> simp[Abbr `e0`, Abbr `cc`])
  >- simp[]
  >- simp[] >> suspend "allocation_history"
QED
Resume immutable_allocate_initialize_mem[allocation_history]:
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  drule_at (Pat `step_inst_base _ _ = _`) alloca_history_base_step >>
  simp[] >>
  disch_then (qspecl_then [`func`,
    `<|bb_label := lbl; bb_instructions := pre ++ [ainst; mk_inst j JMP [Label entry] []]|>`] mp_tac) >>
  impl_tac >- simp[get_instruction_def, EL_APPEND_EQN] >>
  strip_tac >> irule alloca_history_jump >> simp[] >>
  qexists_tac `s1 with vs_inst_idx := SUC (LENGTH pre)` >> fs[is_terminator_def]
QED
Finalise immutable_allocate_initialize_mem

Theorem immutable_optional_length_mem:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ret_pc_ok cenv sa s /\ alloca_history func s /\ fn_inst_ids_distinct func ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    stmt_state_rel ctx func cenv cx es u /\ ret_pc_ok cenv sa u /\
    array_caller_frame sa s u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ alloca_history func u
Proof
  Cases_on `dyn` >> simp[comp_return_def] >> strip_tac
  >- (drule_all immutable_length_load_mem >> strip_tac >>
      qexists_tac `u` >> simp[] >>
      qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  gvs[] >> qexists_tac `s` >>
  simp[eval_operand_def, array_caller_frame_def, gas_marked_path_def,
       gas_path_mem_rules]
QED

(* Initialize to the condition block; the zero-length case uses the same
   endpoint and does not execute an element copy. *)
Theorem immutable_initialize_post_load_mem:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ret_pc_ok cenv sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block sb.cs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      sb.cs_current_insts ++ [ainst; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
         mk_inst e3 ISZERO [Var g] [vld];
         mk_inst e4 ASSERT [Var vld] []] else []) ++
      [mk_inst e5 JMP [Label cond_lbl] []]|> /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  ALL_DISTINCT [p; idx; g; vld] /\
  not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes idx /\
  not_local_ptr cenv es.scopes g /\ not_local_ptr cenv es.scopes vld /\
  (!x. lvo = Var x ==> ~MEM x [p; idx; g; vld]) /\
  (!x. not_fresh_at sb x ==> ~MEM x [p; idx; g; vld]) /\
  alloca_history func s /\ return_buf_frame d cenv sa s ==>
  ?u dst cc.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond_lbl sa 0 es cc /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame sa s u /\ array_caller_frame sb u cc /\
    gas_marked_path T ctx func s 0 (OK cc) /\
    u.vs_memory = s.vs_memory /\ cc.vs_memory = s.vs_memory /\
    s.vs_alloca_next <= u.vs_alloca_next /\ u.vs_alloca_next <= cc.vs_alloca_next /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP cc.vs_allocas aid = SOME b) /\
    alloca_history func u /\ alloca_history func cc /\
    return_buf_frame d cenv sa u /\ return_buf_frame d cenv sb u /\
    return_buf_frame d cenv sa cc /\ return_buf_frame d cenv sb cc
Proof
  strip_tac >> drule_all immutable_optional_length_mem >> strip_tac >>
  `ret_pc_ok cenv sb u` by
    (fs[ret_pc_ok_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `lookup_block u.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      sb.cs_current_insts ++ [ainst; mk_inst j JMP [Label entry] []]|>` by simp[] >>
  drule_all immutable_allocate_initialize_mem >>
  disch_then (qspec_then `off` strip_assume_tac) >>
  `array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond_lbl sa 0 es cc` by
    (irule immutable_initial_frame_rebase >> goal_assum (drule_at Any) >>
     asm_rewrite_tac []) >>
  `return_buf_frame d cenv sa u /\ return_buf_frame d cenv sb u` by
    (conj_tac >> irule return_buf_frame_frame >>
     goal_assum (drule_at Any) >> fs[array_caller_frame_def]) >>
  `return_buf_frame d cenv sb cc` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >>
     fs[array_caller_frame_def]) >>
  `return_buf_frame d cenv sa cc` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `u`, `sa`] >>
     fs[array_caller_frame_def] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  qexistsl_tac [`u`, `dst`, `cc`] >> asm_rewrite_tac [] >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  fs[array_caller_frame_def]
QED

(* The source copy is the sole memory-accessing part of the entry prefix. *)
Theorem immutable_copy_prefix_path_mem:
  compile_iter_elem_copy cenv src dst bytes LocCode F et et sa = ((),sb) /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [MUL; ADD]) sa.cs_current_insts /\
  run_inst_seq sb.cs_current_insts s = OK t /\
  run_inst_seq_mem_ok sb.cs_current_insts s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb.cs_current_insts bb.bb_instructions /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE])
    (emitted_insts sa sb)` by
    (drule whitelistForIterImmCopyTheory.immutable_iter_copy_opcodes >> strip_tac >>
     gvs[emitted_insts_def, DROP_PREFIX]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> GAS) sb.cs_current_insts` by
    (qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >> simp[EVERY_APPEND] >>
     rpt conj_tac >> irule listTheory.EVERY_MONOTONIC >>
     goal_assum (drule_at Any) >> simp[is_terminator_def] >>
     rpt strip_tac >> gvs[is_terminator_def]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) sb.cs_current_insts) = 0` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `isPREFIX sb.cs_current_insts (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `s.vs_inst_idx = 0` (fn th => pure_rewrite_tac[th, DROP_0]) >>
     first_assum ACCEPT_TAC) >>
  drule_all run_inst_seq_gas_path_mem >> simp[gas_marked_path_def]
QED

Theorem immutable_array_entry_run_mem:
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocCode F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ 0 < stride /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
  not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var p s = SOME dst /\
  p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\ not_fresh_at sa ep /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  w2n dst + stride < dimword (:256) /\ w2n dst + stride <= s.vs_alloca_next /\
  immutable_holds cenv cx et (Value v)
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) es s /\
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]] /\
  lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  s.vs_current_bb = sb0.cs_current_bb /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  not_fresh_at sa idx /\ idx <> ov /\ idx <> tot /\ idx <> ep /\
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  ret_pc_ok bc sb0 s /\ ret_pc_ok cenv st s /\
  (!x. not_fresh_at caller x ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  alloca_history func s /\ return_buf_frame d cenv sa s /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==>
    x <> ov /\ x <> tot /\ x <> ep) /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
    (!x. region = Var x ==> x <> ov /\ x <> tot /\ x <> ep)) /\
  (!ce srcop dstop bytes ty cs ct tyv cxx cxxctx fn ee ss vv aa bb dd.
    compile_iter_elem_copy ce srcop dstop bytes LocCode F ty ty cs = ((),ct) /\
    bytes = type_memory_size tyv /\ 0 < bytes /\
    evaluate_type (get_tenv cxx) ty = SOME tyv /\
    stmt_state_rel cxxctx fn ce cxx ee ss /\
    immutable_holds ce cxx ty (Value vv) aa ee ss /\
    copy_old_operand cs srcop /\ copy_old_operand cs dstop /\
    eval_operand srcop ss = SOME aa /\ eval_operand dstop ss = SOME bb /\
    w2n bb + bytes <= ss.vs_alloca_next /\ w2n bb + bytes < dimword (:256) /\
    (ce.ce_is_ctor ==> regions_disjoint (w2n aa) bytes (w2n bb) bytes) /\
    (!region. ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME region ==>
      eval_operand region ss = SOME 0w /\ copy_old_operand cs region) /\
    alloca_history fn ss /\ return_buf_frame dd ce cs ss ==>
    run_inst_seq_mem_ok (emitted_insts cs ct) ss /\
    ?z. copy_runtime_frame cs ss ct z /\
      val_wf tyv vv /\ val_in_memory tyv vv (w2n bb) z.vs_memory /\
      val_footprint tyv vv <= bytes /\
      LENGTH ss.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n bb \/ w2n bb + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len ss.vs_memory) /\
      (z with <|vs_vars := ss.vs_vars; vs_memory := ss.vs_memory|>) = ss /\
      z.vs_alloca_next = ss.vs_alloca_next /\ z.vs_allocas = ss.vs_allocas /\
      alloca_history fn z /\ return_buf_frame dd ce ct z) ==>
  ?s2. s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := v; popped := []|>)) :: es.scopes) s2 /\
    ret_pc_ok bc sb0 s2 /\ ret_pc_ok cenv st s2 /\
    lookup_var idx s2 = SOME (n2w k) /\ lookup_var p s2 = SOME dst /\
    FLOOKUP s2.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
    array_caller_frame caller s s2 /\ gas_marked_path T ctx func s 0 (OK s2) /\
    s2.vs_allocas = s.vs_allocas /\ s2.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func s2 /\ return_buf_frame d bc sb0 s2 /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
      lookup_var x s2 = lookup_var x s)
Proof
  strip_tac >> drule_all immutable_array_entry_seq >>
  disch_then (qspecl_then [`j5`, `j4`, `j3`] strip_assume_tac) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_halted = s.vs_halted /\
   (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
     lookup_var x t = lookup_var x s)` by
    (drule_all immutable_entry_seq_frames >> simp[]) >>
  `not_fresh_at sa p` by metis_tac[array_copy_live_ptrs_reserved] >>
  `sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0` by
    fs[copy_runtime_frame_def] >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by gvs[] >>
  `EVERY (\i. MEM i.inst_opcode [MUL; ADD]) sa.cs_current_insts` by
    (Cases_on `dyn` >> simp[mk_inst_def]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb0) s1 /\
   t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t /\
   return_buf_frame d cenv sb0 t` by
    suspend "copy" >>
  `run_inst_seq_mem_ok sb0.cs_current_insts s` by suspend "safety" >>
  `gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb0.cs_current_insts))` by
    (drule_all immutable_copy_prefix_path_mem >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb0.cs_current_insts` >> simp[] >>
  conj_tac >- suspend "relation" >>
  conj_tac >- suspend "pc1" >>
  conj_tac >- suspend "pc2" >>
  conj_tac >- suspend "idx" >>
  conj_tac >- suspend "ptr" >>
  conj_tac >- suspend "caller" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "return" >>
  suspend "vars"
QED

Resume immutable_array_entry_run_mem[copy]:
  `stmt_state_rel ctx func cenv cx es s1` by
    (Cases_on `dyn` >> gvs[] >>
     rpt (irule stmt_state_rel_update_var >> simp[])) >>
  `immutable_holds cenv cx et (Value v)
    (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) es s1` by
    (irule immutable_value_holds_transport >>
     qexistsl_tac [`cenv`, `es`, `s`] >>
     simp[cenv_top_ext_refl] >> Cases_on `dyn` >> gvs[update_var_def]) >>
  `copy_old_operand sa (Var p) /\ copy_old_operand sa (Var ep) /\
   eval_operand (Var p) s1 = SOME dst /\
   eval_operand (Var ep) s1 = SOME
     (n2w off + n2w ((if dyn then 32 else 0) + k * stride)) /\
   w2n dst + stride <= s1.vs_alloca_next` by
    (Cases_on `dyn` >> gvs[copy_old_operand_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE, update_var_def]) >>
  `alloca_history func s1` by
    (irule alloca_history_frame >> qexists_tac `s` >>
     Cases_on `dyn` >> gvs[update_var_def]) >>
  `return_buf_frame d cenv sa s1` by
    (Cases_on `d` >- fs[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
     qpat_x_assum `return_buf_frame _ _ _ s` mp_tac >>
     simp[return_buf_frame_def] >> strip_tac >>
     `x <> ov /\ x <> tot /\ x <> ep` by metis_tac[] >>
     qexistsl_tac [`x`, `slot_size`] >>
     Cases_on `dyn` >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `cenv.ce_is_ctor ==> regions_disjoint
     (w2n ((n2w off : bytes32) + n2w ((if dyn then 32 else 0) + k * stride))) stride
     (w2n dst) stride` by
    (strip_tac >>
     `regions_disjoint
       (w2n ((n2w off : bytes32) + n2w ((if dyn then 32 else 0) + k * stride))) stride
       (w2n dst) sz` by
       (drule_all immutable_holds_alloca_disjoint >> simp[]) >>
     gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s1 = SOME 0w /\ copy_old_operand sa region` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!region. _` (qspec_then `region` mp_tac) >>
     simp[] >> strip_tac >> simp[] >>
     `region <> Var ep /\ region <> Var tot /\ region <> Var ov` by metis_tac[] >>
     qpat_x_assum `s1 = _` SUBST1_TAC >>
     Cases_on `dyn` >> simp[] >>
     rpt (irule eval_operand_update_other_local >> simp[])) >>
  `w2n dst + stride < dimword (:256)` by simp[] >>
  qpat_x_assum `!ce srcop dstop bytes ty cs ct tyv cxx cxxctx fn ee ss vv aa bb dd. _`
    (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ s1`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ _ s1`)) >>
  disch_then (qspec_then `dst` mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  `z = t` by fs[copy_runtime_frame_def] >>
  Cases_on `dyn` >> gvs[update_var_def]
QED

Resume immutable_array_entry_run_mem[safety]:
  `run_inst_seq sa.cs_current_insts s = OK s1` by
    (qpat_assum `sa.cs_current_insts = _` SUBST1_TAC >>
     qpat_assum `s1 = _` SUBST1_TAC >>
     irule immutable_address_prefix_run >> simp[]) >>
  qpat_assum `sb0.cs_current_insts = _` SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append_run >>
  reverse conj_tac >- gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  Cases_on `dyn` >> simp[mk_inst_def, inst_dload_in_section_def,
    below_frontier_no_ranges]
QED

Resume immutable_array_entry_run_mem[relation]:
  simp[stmt_state_rel_inst_idx]
QED
Resume immutable_array_entry_run_mem[pc1]:
  fs[ret_pc_ok_def, lookup_var_def] >> metis_tac[]
QED
Resume immutable_array_entry_run_mem[pc2]:
  fs[ret_pc_ok_def, lookup_var_def] >> metis_tac[]
QED
Resume immutable_array_entry_run_mem[idx]:
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED
Resume immutable_array_entry_run_mem[ptr]:
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED
Resume immutable_array_entry_run_mem[caller]:
  simp[array_caller_frame_def, lookup_var_def] >> metis_tac[lookup_var_def]
QED
Resume immutable_array_entry_run_mem[history]:
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `?rest. bb.bb_instructions = sb0.cs_current_insts ++ rest` by
    metis_tac[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) sb0.cs_current_insts` by
    (drule immutable_iter_copy_opcodes >> strip_tac >>
     gvs[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >>
     gvs[is_terminator_def] >> metis_tac[is_terminator_def]) >>
  `DROP s.vs_inst_idx bb.bb_instructions = sb0.cs_current_insts ++ rest` by simp[] >>
  drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >> simp[]
QED
Resume immutable_array_entry_run_mem[return]:
  `bc.ce_return_buf = cenv.ce_return_buf` by
    metis_tac[stmtFragPtrTheory.cenv_top_ext_return_buf] >>
  qpat_x_assum `return_buf_frame d cenv sb0 t` mp_tac >>
  Cases_on `d` >- simp[return_buf_frame_def] >>
  PairCases_on `x` >> simp[return_buf_frame_def, lookup_var_def]
QED
Resume immutable_array_entry_run_mem[vars]:
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED
Finalise immutable_array_entry_run_mem
