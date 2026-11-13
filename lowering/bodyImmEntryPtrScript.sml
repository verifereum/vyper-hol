(* Checked runtime entry for immutable array iteration. *)
Theory bodyImmEntryPtr
Ancestors
  immutableRegionLoadPtr bodyImmEntryMemory forPtrArrayEntry fragGasPathPtr
  forPtrRangeEntry forPtrAllocationGhost venomExecSemantics venomInstProofs bodyPtrBopScalarSeq pred_set
  bodyPtrBytestringBuiltinsCalldataReserved augAssignPtrScalarContinuation
  stmtSimForArrayLoop loweringPosts logTopicScalarPtr
  ptrDiscipline immutableCopyExecution fragGasSeqPtr stmtAppendStorageRunPtr exprSimStorageCopy
  exprSimBopRestWordLoads exprSimBopRestWordLoadPath
  appendStorageGhostPtr augAssignPtrScalarFrame abiDecodePtrScalarReplay
  bodyPtrDefs stmtSimProps exprSimCopy exprLoweringProps
  context compileEnv emitHelper emitHelperProps loweringStateRelDefs
  venomInst venomState finite_map words list arithmetic rich_list stmtSimDefs fragExec
Libs monadsyntax

Theorem immutable_optional_length_checked:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  ~cenv.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) ==>
  ?t H tm.
    copy_runtime_frame sa s sb t /\ t = s with vs_vars := t.vs_vars /\
    eval_operand lvo t = SOME (n2w (LENGTH vs)) /\
    copy_old_operand sb lvo /\ op_prov H lvo = NONE /\ op_taint tm lvo = {} /\
    (!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) H tm) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  Cases_on `dyn` >> simp[comp_return_def] >> strip_tac
  >- (gvs[] >>
      `context$compile_ptr_load F cenv.ce_imm_alloca LocCode
         (Lit (n2w off)) sa = (lvo,sb)` by simp[compile_ptr_load_def] >>
      `eval_operand (Lit (n2w off)) s = SOME (n2w off : bytes32)` by
        simp[eval_operand_def] >>
      drule_all rest_word_array_immutable_header >> strip_tac >>
      drule compile_imm_load_word_checked >>
      simp[eval_operand_def, op_taint_def] >> strip_tac >>
      gvs[GSYM immutable_copy_read_def] >>
      `!t. copy_runtime_frame sa s sb t ==> t = s with vs_vars := t.vs_vars` by
        (rpt strip_tac >> drule rest_word_ptr_load_run_frame >> simp[] >>
         fs[copy_runtime_frame_def] >> metis_tac[]) >>
      metis_tac[]) >>
  gvs[] >> qexistsl [`s`,`G`,`tn`] >>
  simp[copy_runtime_frame_def, copy_static_def, emitted_insts_def,
    copy_old_operand_def, eval_operand_def, op_prov_def, op_taint_def,
    inst_seq_ptr_def, run_inst_seq_def, same_blocks_def]
QED

Theorem immutable_optional_length_path_ptr:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  ~cenv.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ ghost_inv d cenv cx es H tm u /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    copy_old_operand sb lvo /\ op_prov H lvo = NONE /\ op_taint tm lvo = {} /\
    ret_pc_ok cenv sa u /\ array_caller_frame sa s u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all immutable_optional_length_checked >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS /\ i.inst_opcode <> ISTORE) (emitted_insts sa sb)` by
    (Cases_on `dyn`
     >- (`context$compile_ptr_load F cenv.ce_imm_alloca LocCode
          (Lit (n2w off)) sa = (lvo,sb)` by gvs[compile_ptr_load_def] >>
         drule rest_word_ptr_load_code >> simp[] >> strip_tac >>
         fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
         simp[] >> rpt strip_tac >> gvs[is_terminator_def]) >>
     gvs[comp_return_def, emitted_insts_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, copy_runtime_frame_def, same_blocks_def] >>
     simp[DROP_APPEND]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 H tm
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (fs[copy_runtime_frame_def, EVERY_CONJ] >>
     `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tm` by
       (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
     `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
       (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
     drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_ptr >>
     simp[EVERY_CONJ, ADD_COMM] >>
     disch_then irule >> metis_tac[]) >>
  `tm.t_imm = tn.t_imm` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `0` assume_tac) >>
     fs[EVERY_CONJ] >> metis_tac[inst_seq_ptr_immutable_taint_frame]) >>
  suspend "length_frame"
QED
Resume immutable_optional_length_path_ptr[length_frame]:
  qexistsl [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`H`,`tm`] >>
  simp[] >> suspend "length_frame_finish"
QED
Resume immutable_optional_length_path_ptr[length_frame_finish]:
  `stmt_state_rel ctx func cenv cx es t` by
    (irule bodyPtrBytestringBuiltinsCalldataReservedTheory.stmt_state_rel_reserved_vars_update >>
     goal_assum (drule_at Any) >> fs[copy_runtime_frame_def] >> metis_tac[]) >>
  `ghost_inv d cenv cx es H tm t` by
    (irule ghost_inv_old_transport >>
     conj_tac >- (qpat_x_assum `t = _` SUBST_ALL_TAC >>
       gvs[ghost_inv_def, stor_taint_ok_def]) >>
     qexistsl [`G`,`es`,`s`,`sa`,`tn`] >>
     fs[copy_runtime_frame_def] >>
     qpat_x_assum `t = _` SUBST_ALL_TAC >> simp[]) >>
  fs[copy_runtime_frame_def, same_blocks_def] >>
  simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx] >>
  gvs[array_caller_frame_def, ret_pc_ok_def, lookup_var_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  simp[venom_state_fupdcanon]
QED
Finalise immutable_optional_length_path_ptr

Theorem immutable_allocate_initialize_ptr:
  MEM (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
  fn_inst_ids_distinct func /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
         mk_inst e3 ISZERO [Var g] [vld];
         mk_inst e4 ASSERT [Var vld] []] else []) ++
      [mk_inst e5 JMP [Label cond_lbl] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G tn s0 /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  eval_operand lvo s0 = SOME (n2w (LENGTH vs)) /\
  op_prov G lvo = NONE /\ op_taint tn lvo = {} /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  ret_pc_ok cenv st s0 /\ ALL_DISTINCT [p; idx; g; vld] /\
  not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes idx /\
  not_local_ptr cenv es.scopes g /\ not_local_ptr cenv es.scopes vld /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> ~MEM x [p; idx; g; vld]) /\
  (!x. lvo = Var x ==> ~MEM x [p; idx; g; vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [p; idx; g; vld]) ==>
  ?dst cc H tm.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) cond_lbl st 0 es cc /\
    ghost_inv d cenv cx es H tm cc /\ ptr_covers H tm p cc sz /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    op_prov H (Var idx) = NONE /\ op_taint tm (Var idx) = {} /\
    op_prov H lvo = NONE /\ op_taint tm lvo = {} /\
    array_caller_frame st s0 cc /\
    gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK cc) /\
    cc.vs_memory = s0.vs_memory /\ s0.vs_alloca_next <= cc.vs_alloca_next /\
    tm.t_mem = tn.t_mem UNION new_site_bytes s0 cc /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `get_instruction <|bb_label := lbl; bb_instructions := pre ++
    [mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|>
    s0.vs_inst_idx = SOME (mk_inst aid ALLOCA [Lit (n2w sz)] [p])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all for_range_alloca_entry_path_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `ghost_inv d cenv cx es
    (step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) u)
    (step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s0 u tn) u` by
    (irule for_alloca_ghost_inv >> simp[] >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     qexistsl [`ctx`,`func`] >> simp[]) >>
  drule_all for_array_alloca_prefix_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s0 u tn` >>
  qabbrev_tac `e0 = jump_to entry u` >>
  qabbrev_tac `code = [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
    if dyn then [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
      mk_inst e3 ISZERO [Var g] [vld]; mk_inst e4 ASSERT [Var vld] []] else []` >>
  qabbrev_tac `q = if dyn then
    update_var vld 1w (update_var g 0w (update_var idx 0w e0))
    else update_var idx 0w e0` >>
  `u.vs_labels = s0.vs_labels` by
    (qpat_x_assum `step_inst_base _ _ = OK u` mp_tac >>
     simp[step_inst_base_opcode_eqs, eval_operand_def, exec_alloca_def] >>
     gvs[AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  `eval_operand lvo e0 = SOME (n2w (LENGTH vs)) /\
    op_prov G1 lvo = NONE /\ op_taint tn1 lvo = {}` by
    (Cases_on `lvo` >> gvs[eval_operand_def, op_prov_def, op_taint_def,
      Abbr `e0`, jump_to_def, lookup_var_def] >> metis_tac[]) >>
  `run_inst_seq code e0 = OK q` by
    (qunabbrev_tac `code` >> qunabbrev_tac `q` >>
     irule whitelistForIterImmLoopTheory.immutable_entry_block_run >>
     simp[ALL_DISTINCT] >>
     conj_tac >- (fs[MEM] >> metis_tac[]) >>
     conj_tac >- fs[ALL_DISTINCT] >>
     qexists_tac `LENGTH vs` >> simp[] >>
     irule LESS_MOD >> decide_tac) >>
  qabbrev_tac `R = {x | ~MEM x [idx; g; vld]}` >>
  qabbrev_tac `A = {lvo; Lit 0w; Lit (n2w cap)}` >>
  qabbrev_tac `B = if dyn then Var vld INSERT Var g INSERT Var idx INSERT A
    else Var idx INSERT A` >>
  `bop_scalar_seq R A code B` by
    (Cases_on `dyn` >> simp[Abbr `code`, Abbr `A`, Abbr `B`, Abbr `R`,
      bop_scalar_seq_def, mk_inst_def] >> metis_tac[]) >>
  `!op. op IN A ==> op_prov G1 op = NONE /\ op_taint tn1 op = {}` by
    (simp[Abbr `A`] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `~e0.vs_halted /\ e0.vs_current_bb = entry /\ e0.vs_inst_idx = 0` by
    simp[Abbr `e0`, jump_to_def] >>
  `lookup_block e0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions := code ++ [mk_inst e5 JMP [Label cond_lbl] []]|>` by
    simp[Abbr `code`] >>
  `isPREFIX code (DROP e0.vs_inst_idx
    (<|bb_label := entry; bb_instructions := code ++ [mk_inst e5 JMP [Label cond_lbl] []]|>).bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all scalar_seq_success_replay_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qabbrev_tac `qe = q with vs_inst_idx := LENGTH code` >>
  `gas_path_ptr D 0 ctx func PG G' tn' qe 0 G' tn'
    (OK (jump_to cond_lbl qe))` by
    (irule for_range_jump_path_ptr >>
     Cases_on `dyn` >>
     simp[Abbr `qe`, Abbr `q`, update_var_def, get_instruction_def, EL_APPEND_EQN] >>
     qexists_tac `e5` >> simp[]) >>
  `gas_path_ptr D 0 ctx func PG G tn s0 0 G' tn' (OK qe)` by
    (qunabbrev_tac `qe` >>
     drule_all gas_path_ptr_then >> simp[]) >>
  `gas_path_ptr D 0 ctx func PG G tn s0 0 G' tn'
    (OK (jump_to cond_lbl qe))` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  qabbrev_tac `cc = jump_to cond_lbl qe` >>
  suspend "finish"
QED
Resume immutable_allocate_initialize_ptr[finish]:
  `!x. x <> idx /\ x <> g /\ x <> vld ==> lookup_var x cc = lookup_var x u` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `qe`, Abbr `q`, Abbr `e0`,
       jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `cc.vs_allocas = u.vs_allocas /\ cc.vs_current_bb = cond_lbl /\
   cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\ cc.vs_memory = u.vs_memory /\
   cc.vs_alloca_next = u.vs_alloca_next /\ cc.vs_labels = u.vs_labels` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `qe`, Abbr `q`, Abbr `e0`,
       jump_to_def, update_var_def]) >>
  `stmt_state_rel ctx func cenv cx es cc` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `qe`, stmt_state_rel_jump_to,
       stmt_state_rel_inst_idx, Abbr `q`] >>
     rpt (irule stmt_state_rel_update_var >> simp[]) >>
     simp[Abbr `e0`, stmt_state_rel_jump_to]) >>
  `lookup_var idx cc = SOME (n2w 0)` by
    (fs[ALL_DISTINCT] >> Cases_on `dyn` >> simp[Abbr `cc`, Abbr `qe`, Abbr `q`, jump_to_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var p cc = SOME a` by (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `ret_pc_ok cenv st cc` by
    (fs[ret_pc_ok_def] >> rpt strip_tac >> first_x_assum drule >>
     strip_tac >> simp[] >> fs[MEM] >> metis_tac[]) >>
  `array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p a sz (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) cond_lbl st 0 es cc` by
    simp[array_loop_inv_def, eval_operand_def, mk_inst_def] >>
  `eval_operand lvo cc = SOME (n2w (LENGTH vs))` by
    (Cases_on `lvo` >> gvs[eval_operand_def] >> fs[MEM] >> metis_tac[]) >>
  `exec_alloca (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) s0 (n2w sz : bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = OK u` mp_tac >>
     simp[step_inst_base_opcode_eqs, eval_operand_def]) >>
  drule stmtSimForArrayFragTheory.array_alloca_frame >> simp[mk_inst_def] >> strip_tac >>
  `array_caller_frame st s0 cc` by
    (simp[array_caller_frame_def] >> fs[MEM] >> metis_tac[]) >>
  suspend "ghost_finish"
QED
Resume immutable_allocate_initialize_ptr[ghost_finish]:
  `!x. x <> idx /\ x <> g /\ x <> vld ==>
    FLOOKUP G' x = FLOOKUP G1 x /\ op_taint tn' (Var x) = op_taint tn1 (Var x)` by
    (fs[Abbr `R`, op_taint_def] >> metis_tac[]) >>
  `!x qsz. cenv.ce_return_pc = SOME (PtrVar (Var x) qsz) ==>
    x <> idx /\ x <> g /\ x <> vld` by
    (fs[ret_pc_ok_def, MEM] >> metis_tac[]) >>
  `!name ent x z. lookup_scopes name es.scopes = SOME ent /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) z) ==>
     x <> idx /\ x <> g /\ x <> vld` by
    (fs[not_local_ptr_def] >> metis_tac[]) >>
  `!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==>
    x <> idx /\ x <> g /\ x <> vld` by (fs[MEM] >> metis_tac[]) >>
  `!x z. x <> idx /\ x <> g /\ x <> vld ==>
    (ptr_covers G' tn' x cc z <=> ptr_covers G1 tn1 x u z)` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  `cc.vs_call_ctx = u.vs_call_ctx /\ cc.vs_accounts = u.vs_accounts /\
   cc.vs_transient = u.vs_transient` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `qe`, Abbr `q`, Abbr `e0`,
      jump_to_def, update_var_def]) >>
  `ghost_inv d cenv cx es G' tn' cc` by
    (qpat_x_assum `ghost_inv _ _ _ _ G1 _ _` mp_tac >>
     simp[ghost_inv_def, stor_taint_ok_def] >> strip_tac >>
     rpt conj_tac >-
       (rpt strip_tac >>
        qpat_assum `!name ent x z. _ ==> x <> idx /\ _` drule >>
        disch_then drule >> strip_tac >>
        qpat_assum `!name entry p' sz'. _ ==> ptr_covers _ _ _ _ _ /\ _` drule >>
        disch_then drule >> strip_tac >> fs[] >> metis_tac[]) >-
       (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
        fs[return_buf_ptr_def] >> metis_tac[]) >>
     rpt strip_tac >> metis_tac[]) >>
  `ptr_covers G' tn' p cc sz` by (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `op_prov G' (Var idx) = NONE /\ op_taint tn' (Var idx) = {} /\
   op_prov G' lvo = NONE /\ op_taint tn' lvo = {}` by
    (Cases_on `dyn` >> fs[Abbr `B`, Abbr `A`] >> metis_tac[]) >>
  `s0.vs_alloca_next <= cc.vs_alloca_next` by
    (qpat_x_assum `exec_alloca _ _ _ = OK u` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >>
     gvs[update_var_def] >> decide_tac) >>
  `tn1.t_mem = tn.t_mem UNION new_site_bytes s0 u /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, step_taint_def, mem_taint_def, store_taint_def,
      imm_taint_def, mk_inst_def, step_writes_def, written_taint_def,
      codegenRelTheory.source_memory_write_ranges_def, adopt_reset_def, range_bytes_def] >>
  `cc.vs_fmp = u.vs_fmp` by
    (Cases_on `dyn` >> simp[Abbr `cc`, Abbr `qe`, Abbr `q`, Abbr `e0`,
      jump_to_def, update_var_def]) >>
  `new_site_bytes s0 cc = new_site_bytes s0 u` by simp[new_site_bytes_def] >>
  qexistsl_tac [`a`,`cc`,`G'`,`tn'`] >> simp[GSYM mk_inst_def] >>
  rpt strip_tac >> fs[MEM] >> metis_tac[]
QED
Finalise immutable_allocate_initialize_ptr

(* Join the checked optional header read with allocated scalar entry. *)
Theorem immutable_entry_initialize_ptr:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) sa = (lvo,sb) /\
  ~cenv.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at sa x) /\
  (dyn ==>
    immutable_holds cenv cx (ArrayT et (Dynamic cap)) (Value (ArrayV av))
      (n2w off) es s /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
    LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (~dyn ==> LENGTH vs = cap) /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sa.cs_next_var <= sb.cs_next_var /\
  MEM (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
  fn_inst_ids_distinct func /\ sz < dimword (:256) /\
  lookup_block sb.cs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      sb.cs_current_insts ++
      [mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst e2 GT [lvo; Lit (n2w cap)] [g];
         mk_inst e3 ISZERO [Var g] [vld];
         mk_inst e4 ASSERT [Var vld] []] else []) ++
      [mk_inst e5 JMP [Label cond_lbl] []]|> /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\ ALL_DISTINCT [p; idx; g; vld] /\
  not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes idx /\
  not_local_ptr cenv es.scopes g /\ not_local_ptr cenv es.scopes vld /\
  (!x. lvo = Var x ==> ~MEM x [p; idx; g; vld]) /\
  (!x. not_fresh_at sb x ==> ~MEM x [p; idx; g; vld]) ==>
  ?dst cc H tm.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz (mk_inst aid ALLOCA [Lit (n2w sz)] [p]) cond_lbl sa 0 es cc /\
    ghost_inv d cenv cx es H tm cc /\ ptr_covers H tm p cc sz /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    op_prov H (Var idx) = NONE /\ op_taint tm (Var idx) = {} /\
    op_prov H lvo = NONE /\ op_taint tm lvo = {} /\
    array_caller_frame sa s cc /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK cc) /\
    cc.vs_memory = s.vs_memory /\ s.vs_alloca_next <= cc.vs_alloca_next /\
    tm.t_mem = tn.t_mem UNION new_site_bytes s cc /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all immutable_optional_length_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==>
    ~MEM x [p; idx; g; vld]` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> ~MEM x [p; idx; g; vld]` by metis_tac[] >>
  `lookup_block u.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions := sb.cs_current_insts ++
      [mk_inst aid ALLOCA [Lit (n2w sz)] [p]; mk_inst j JMP [Label entry] []]|>` by simp[] >>
  drule_all immutable_allocate_initialize_ptr >>
  disch_then (qspecl_then [`off`,`PG`,`D`] strip_assume_tac) >>
  `tm.t_imm = tn.t_imm` by
    (fs[ghost_inv_def, stor_taint_ok_def]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 H' tm' (OK cc)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `new_site_bytes u cc = new_site_bytes s cc` by
    (qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[new_site_bytes_def]) >>
  qexistsl_tac [`dst`,`cc`,`H'`,`tm'`] >> simp[] >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  fs[array_caller_frame_def] >> metis_tac[]
QED
