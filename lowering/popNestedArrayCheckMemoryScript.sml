(* Counted memory-free bounds checking and array pointer arithmetic. *)
Theory popNestedArrayCheckMemory
Ancestors
  targetSubscriptMemory exprSimArrayIndex exprSimSubscriptArrayFramed
  fragGasFresh fragGasSeqMem bodyUnopFragMemory bodyDeclMemoryCore
  freshWrites varsExt exprSimProps fragExec fragGasMode
  loweringStateRelDefs allocaHistory compileEnv exprLoweringProps
  venomState venomInst venomExecSemantics list rich_list arithmetic

Theorem pop_nested_array_check_ptr_path_mem:
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!x. len_op = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  eval_operand len_op s = SOME len /\ idx_in_range sgn i len ==>
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
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb) /\ same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_x_assum `straight_fresh _` mp_tac >>
     simp[straight_fresh_def] >> disch_then drule >> simp[same_blocks_def]) >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[writes_fresh_mem_ok] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  qmatch_asmsub_rename_tac `vars_ext t0 target` >>
  `alloca_history func (target with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> conj_tac >- simp[] >> qexistsl_tac [`s`, `sa`] >>
     fs[stmt_state_rel_def, EVERY_MEM]) >>
  `target.vs_alloca_next = s.vs_alloca_next` by
    (drule_all run_inst_seq_writes_fresh >> strip_tac >>
     qpat_x_assum `target = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    simp[] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    metis_tac[writes_fresh_gas_count] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >>
  strip_tac >> qexists_tac `target with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def] >> gvs[gas_marked_path_def, ADD_COMM]
QED

Theorem pop_nested_array_check_ptr_abort_path_mem:
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
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
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >>
     simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[writes_fresh_mem_ok] >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >> metis_tac[]
QED
