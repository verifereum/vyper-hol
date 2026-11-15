(* Checked paths for the arithmetic and runtime-code array tails. *)
Theory bodyMemSubscriptArrayPaths
Ancestors
  exprSimSubscriptArrayFramed exprSimArrayIndex bodyUnopFragMemory bodyImmutableCopyMemory
  allocaHistoryFragment fragExec fragGasFresh fragGasSeqMem
  fragGasSeqAbort fragGasMode freshWrites varsExt exprSimProps exprSimUnopProps
  exprLoweringProps emitHelperProps moduleLoweringProps compileEnv loweringStateRelDefs
  venomExecSemantics venomInst venomState finite_map list rich_list arithmetic

Theorem array_fresh_success_mem[local]:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ vars_ext t0 t /\
    gas_marked_path T ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `writes_fresh sa (emitted_insts sa sb) /\ same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_x_assum `straight_fresh m` mp_tac >>
     simp[straight_fresh_def, same_blocks_def] >> disch_then drule >> simp[]) >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[writes_fresh_mem_ok] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    metis_tac[writes_fresh_gas_count] >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by simp[] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    fs[IS_PREFIX_APPEND] >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
     simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[gas_marked_path_def] >>
  qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem array_fresh_abort_mem[local]:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = Abort a t0 ==>
  ?t. gas_marked_path T ctx func s 0 (Abort a t)
Proof
  strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by metis_tac[writes_fresh_mem_ok] >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >> metis_tac[]
QED

Theorem fixed_array_subscript_counted_mem_ok:
  compile_array_subscript base_op idx_op F cnt ws esz sgn loader sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand op t = SOME (b + i * n2w esz) /\
    (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==> lookup_var z t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t
Proof
  strip_tac >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx_op (drop_fresh sa s) = SOME i` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `array_len_ok F cnt loader base_op (drop_fresh sa s) (n2w cnt)` by
    simp[array_len_ok_static] >>
  drule_all compile_array_subscript_ok >> strip_tac >>
  `straight_fresh (compile_array_subscript base_op idx_op F cnt ws esz sgn loader)` by
    simp[straight_fresh_compile_array_subscript] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all array_fresh_success_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem fixed_array_subscript_counted_mem_oob:
  compile_array_subscript base_op idx_op F cnt ws esz sgn loader sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx_op (drop_fresh sa s) = SOME i` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `array_len_ok F cnt loader base_op (drop_fresh sa s) (n2w cnt)` by
    simp[array_len_ok_static] >>
  drule_all compile_array_subscript_oob >> strip_tac >>
  `straight_fresh (compile_array_subscript base_op idx_op F cnt ws esz sgn loader)` by
    simp[straight_fresh_compile_array_subscript] >>
  drule_all array_fresh_abort_mem >> simp[]
QED

Theorem array_length_runtime_mem[local]:
  compile_imm_load_word F imm base_op sa = (op,sb) /\
  eval_operand base_op s = SOME b /\ w2n b <= LENGTH s.vs_data_section /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) /\
    gas_marked_path T ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    (fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
      alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule_all compile_imm_load_word_runtime_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_immutable_load_mem_ok >> goal_assum (drule_at Any) >>
     rpt strip_tac >> gvs[]) >>
  drule_all compile_imm_load_word_runtime_run >> strip_tac >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (strip_tac >> drule_all alloca_history_run_inst_seq >> gvs[]) >>
  gvs[gas_marked_path_def, update_var_def, mk_inst_def,
      eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem runtime_length_mem_frame[local]:
  compile_imm_load_word F imm base_op sa = (lop,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  alloca_history func s /\ w2n b <= LENGTH s.vs_data_section /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ alloca_history func u /\
    u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    eval_operand base_op u = SOME b /\ eval_operand idx_op u = SOME i /\
    eval_operand lop u = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s) /\
    (!z. base_op = Var z ==> not_fresh_at sm z) /\
    (!z. idx_op = Var z ==> not_fresh_at sm z) /\
    (!z. lop = Var z ==> not_fresh_at sm z) /\
    sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sm /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all array_length_runtime_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all compile_imm_load_word_runtime_run >> strip_tac >> gvs[] >>
  drule_all compile_imm_load_word_runtime_frame >>
  disch_then (qspec_then `word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sm.cs_next_var` by simp[] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  simp[] >> rpt conj_tac
  >- (Cases_on `base_op` >> gvs[eval_operand_def] >>
      drule lookup_var_update_not_fresh >> simp[]) 
  >- (Cases_on `idx_op` >> gvs[eval_operand_def] >>
      drule lookup_var_update_not_fresh >> simp[]) >>
  simp[not_fresh_at_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[not_fresh_at_def] >>
  disch_then irule >> decide_tac
QED

Theorem runtime_array_mem_split[local]:
  compile_array_subscript base_op idx_op T cnt ws esz sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\ fn_has_code sa sb func ==>
  ?lop sm. compile_imm_load_word F imm base_op sa = (lop,sm) /\
    comp_ignore_bind (array_bounds_check idx_op lop sgn)
      (array_elem_ptr base_op idx_op T ws esz) sm = (op,sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  simp[compile_array_subscript_split, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_imm_load_word F imm base_op sa = (lop,sm)` >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op lop sgn)
      (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `cs_extends sa sm` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
     drule emit_op_extends >> strip_tac >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, IS_PREFIX_APPEND3]) >>
  `cs_extends sm sb` by metis_tac[straight_fresh_cs_extends] >>
  drule_all fn_has_code_split >> simp[] >> metis_tac[]
QED

Theorem runtime_array_subscript_counted_mem_oob:
  compile_array_subscript base_op idx_op T cnt ws esz sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  w2n b <= LENGTH s.vs_data_section /\
  ~idx_in_range sgn i (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >> drule_all runtime_array_mem_split >> strip_tac >>
  drule_all array_length_runtime_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand idx_op t = SOME i /\
   (!z. idx_op = Var z ==> not_fresh_at sm z) /\
   (!z. lop = Var z ==> not_fresh_at sm z)` by
    (drule_all compile_imm_load_word_runtime_run >> strip_tac >>
     qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
     drule emit_op_extends >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
     conj_tac
     >- (Cases_on `idx_op` >> gvs[eval_operand_def] >>
         drule lookup_var_update_not_fresh >> simp[]) >>
     simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[not_fresh_at_def] >>
     disch_then irule >> decide_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `gas_marked_path T ctx func s 0 (OK u) /\
   ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[Abbr `u`] >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op lop sgn)
      (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `eval_operand idx_op (drop_fresh sm u) = SOME i /\
   eval_operand lop (drop_fresh sm u) = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) /\
   fresh_vars_wrt sm (drop_fresh sm u)` by
    simp[fresh_vars_wrt_drop_fresh, eval_operand_drop_fresh, Abbr `u`] >>
  drule_all array_check_ptr_oob >> strip_tac >>
  drule_all array_fresh_abort_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all gas_marked_path_then >> simp[] >> metis_tac[]
QED

Theorem runtime_array_subscript_counted_mem_ok:
  compile_array_subscript base_op idx_op T cnt ws esz sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  w2n b <= LENGTH s.vs_data_section /\
  idx_in_range sgn i (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand op t = SOME ((b + n2w ws) + i * n2w esz) /\
    (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==> lookup_var z t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t
Proof
  strip_tac >> drule_all runtime_array_mem_split >> strip_tac >>
  drule_all runtime_length_mem_frame >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op lop sgn)
      (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `eval_operand base_op (drop_fresh sm u) = SOME b /\
   eval_operand idx_op (drop_fresh sm u) = SOME i /\
   eval_operand lop (drop_fresh sm u) = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) /\
   fresh_vars_wrt sm (drop_fresh sm u)` by
    simp[fresh_vars_wrt_drop_fresh, eval_operand_drop_fresh] >>
  drule_all array_check_ptr_run >> strip_tac >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  drule_all array_fresh_success_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  `gas_marked_path T ctx func s 0
    (OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexists_tac `t' with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!z v. not_fresh_at sm z /\ _ ==> _`
    (qspecl_then [`z`, `v`] irule) >>
  conj_tac
  >- (qpat_x_assum `!z. not_fresh_at sa z ==> _` drule >> simp[lookup_var_def]) >>
  irule not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]
QED
