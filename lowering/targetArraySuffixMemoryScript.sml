(* Counted execution of local array target suffixes. *)
Theory targetArraySuffixMemory
Ancestors
  targetMemoryContracts targetSubscriptMemory exprSimSubscriptArrayFramed
  exprSimArrayIndex fragGasFresh freshWrites varsExt
  emitHelper exprSimUnopProps fragExec compileEnv loweringPosts
  bodyDeclMemoryCounted bodyUnopFragMemory entryDecoderHistoryFrame
  fragGasSeqMem fragGasSeqAbort fragGasMode fragGasPathMem
  fragExecMem instMemFrontier memSafeRun allocaHistoryFragment
  exprSimProps exprLowering exprLoweringProps loweringStateRelDefs
  bodyMemAugAssignAttrLocal targetPlaceSim context exprBopSimProps
  venomInst venomState venomExecSemantics list rich_list
Libs
  pairLib

Theorem target_fresh_code_memory_safe[local]:
  !code s. EVERY (\i. fresh_write_op i.inst_opcode) code ==>
    run_inst_seq_mem_ok code s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >> rpt strip_tac
  >- (irule below_frontier_no_ranges >> fs[fresh_write_op_def])
  >- fs[fresh_write_op_def, inst_dload_in_section_def] >>
  Cases_on `step_inst_base h s` >> simp[] >> metis_tac[]
QED

Theorem target_straight_fresh_path_mem[local]:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ vars_ext t0 t /\
    gas_marked_path T ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   same_blocks sa sb` by fs[straight_fresh_def, same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule target_fresh_code_memory_safe >> fs[writes_fresh_def, EVERY_MEM]) >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all body_decl_zero_gas_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by simp[] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  qexists `t` >> simp[gas_marked_path_def]
QED

Theorem target_array_check_ptr_path_mem:
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!x. len_op = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  eval_operand len_op s = SOME len /\ idx_in_range sgn i len /\
  fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand dst t =
      SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
      lookup_var x t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
      FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx_op (drop_fresh sa s) = SOME i /\
   eval_operand len_op (drop_fresh sa s) = SOME len` by
    simp[eval_operand_drop_fresh] >>
  drule_at (Pat `comp_ignore_bind _ _ _ = _`) array_check_ptr_run >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all target_straight_fresh_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  qexists `t' with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  qpat_x_assum `t' = _` (fn th => simp[Once th])
QED

Theorem target_array_check_ptr_abort_path_mem:
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!x. len_op = Var x ==> not_fresh_at sa x) /\
  eval_operand idx_op s = SOME i /\ eval_operand len_op s = SOME len /\
  ~idx_in_range sgn i len ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `eval_operand idx_op (drop_fresh sa s) = SOME i /\
   eval_operand len_op (drop_fresh sa s) = SOME len` by
    simp[eval_operand_drop_fresh] >>
  drule_at (Pat `comp_ignore_bind _ _ _ = _`) array_check_ptr_oob >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  `vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule target_fresh_code_memory_safe >> fs[writes_fresh_def, EVERY_MEM]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  drule_all run_inst_seq_abort_zero_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Theorem target_memory_dynamic_array_path_mem:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (mload (w2n b) s) /\
  w2n b + 32 <= s.vs_alloca_next /\
  fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand dst t = SOME (b + n2w ws + i * n2w esz) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
      lookup_var x t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
      FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  drule target_memory_header_compile >> strip_tac >>
  `(!x. base_op = Var x ==> not_fresh_at sm x) /\
   (!x. idx_op = Var x ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  `emit_op MLOAD [base_op] sa = (len_op,sm)` by fs[compile_ptr_load_def] >>
  drule_all augassign_field_read_path_mem >> strip_tac >>
  `eval_operand base_op t = SOME b /\ eval_operand idx_op t = SOME i` by
    (conj_tac >> irule eval_operand_frame >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  drule_all target_array_check_ptr_path_mem >> strip_tac >>
  qexists `t'` >> simp[] >> conj_tac
  >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem target_memory_dynamic_array_abort_path_mem:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (mload (w2n b) s) /\
  w2n b + 32 <= s.vs_alloca_next /\
  fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  drule target_memory_header_compile >> strip_tac >>
  `!x. idx_op = Var x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `emit_op MLOAD [base_op] sa = (len_op,sm)` by fs[compile_ptr_load_def] >>
  drule_all augassign_field_read_path_mem >> strip_tac >>
  `eval_operand idx_op t = SOME i` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`sa`, `s`] >> simp[]) >>
  drule_all target_array_check_ptr_abort_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t'` >> metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem target_memory_array_path_mem:
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (if dyn then mload (w2n b) s else n2w cnt) /\
  (dyn ==> w2n b + 32 <= s.vs_alloca_next) /\
  fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
      lookup_var x t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
      FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all target_array_check_ptr_path_mem >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ _ sa = (len_op,sm)` >>
  drule target_memory_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all target_memory_dynamic_array_path_mem >> simp[]
QED

Theorem target_memory_array_abort_path_mem:
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (if dyn then mload (w2n b) s else n2w cnt) /\
  (dyn ==> w2n b + 32 <= s.vs_alloca_next) /\
  fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all target_array_check_ptr_abort_path_mem >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ _ sa = (len_op,sm)` >>
  drule target_memory_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all target_memory_dynamic_array_abort_path_mem >> simp[]
QED

Theorem target_memory_array_error_suffix_mem:
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 32 (type_memory_bytes cenv ety)
    (is_signed_type ity)
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\
  (!l. idx <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INR err,es') /\ fn_inst_ids_distinct func /\ alloca_history func s ==>
  (?u. gas_marked_path T ctx func s 0 (Abort Revert_abort u)) /\
  err = Error (RuntimeError "evaluate_subscripts array_index") /\ es' = es
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   ?b. eval_operand (FST rb) s = SOME b /\
       place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b
         (FST (SND rb)) (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)))` by
    fs[target_post_def] >>
  `dyn ==> w2n b + 32 <= s.vs_alloca_next` by
    (strip_tac >> gvs[] >> drule_all target_memory_dynamic_header_frontier >> simp[]) >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all extend_place_memory_array_index >>
  disch_then (qspecl_then [`i`, `cx`] assume_tac) >>
  drule_all target_memory_array_range >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all target_memory_array_abort_path_mem >> simp[]
QED

Theorem target_memory_array_suffix_mem:
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 32 (type_memory_bytes cenv ety)
    (is_signed_type ity)
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\
  (!l. idx <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INL pv',es') /\ fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
      target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety)
        (dst,SOME LocMemory,SOME (ValPT ety)) u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   (?b. eval_operand (FST rb) s = SOME b /\
        place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b
          (FST (SND rb)) (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)))) /\
   (!x. FST rb = Var x ==> not_fresh_at sm x)` by fs[target_post_def] >>
  `dyn ==> w2n b + 32 <= s.vs_alloca_next` by
    (strip_tac >> gvs[] >> drule_all target_memory_dynamic_header_frontier >> simp[]) >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all extend_place_memory_array_index >>
  disch_then (qspecl_then [`i`, `cx`] assume_tac) >>
  `0 <= i /\ Num i < array_length (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) av` by
    (gvs[AllCaseEqs()]) >>
  drule_all target_memory_array_range >> strip_tac >>
  `idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then mload (w2n b) s else n2w cnt)` by metis_tac[] >>
  drule_all target_memory_array_path_mem >> strip_tac >>
  drule_all target_memory_array_offset >>
  disch_then (qspec_then `b` strip_assume_tac) >>
  `eval_operand dst t = SOME (b + n2w k)` by metis_tac[] >>
  drule_all target_post_memory_step >> strip_tac >>
  qexists `t` >> simp[]
QED
