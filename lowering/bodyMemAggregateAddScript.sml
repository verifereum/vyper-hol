Theory bodyMemAggregateAdd
Ancestors
  bodyMemAggregateContinuation bodyDeclMemoryCounted allocaFootprint
  exprSimAggregateChildren exprSimVVFrame exprSimHash emitHelperProps
  exprLoweringProps venomInst venomState instMemFrontier memSafeRun fragGasMode
  bodyMemAssignAttrStorage exprOperandVar allocaHistory fragExec list rich_list

Theorem aggregate_tuple_add_marked_mem:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand buf s = SOME w /\ fn_has_code sm sn func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path T ctx func s 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
    q.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s) /\
    (vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es' tv vv s ==>
     vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es' tv vv q) /\
    (alloca_history func s ==> alloca_history func q)
Proof
  strip_tac >>
  drule_all buffer_emit_add_vv_post >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) s` by
    (drule emit_op_mem_ok >> disch_then irule >>
     simp[below_frontier_no_ranges, inst_dload_in_section_other, mk_inst_def]) >>
  `gas_path_mem ctx func s 0
     (OK (q with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
   ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[mk_inst_def, is_terminator_def] >>
     qexists_tac `sm` >> simp[mk_inst_def, is_terminator_def]) >>
  `q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
   q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s` by
    (`!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
       (drule (cj 1 compiler_compile_var) >> simp[]) >>
     Cases_on `vv_operand vv` >> simp[eval_operand_def] >>
     qpat_x_assum `q with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[gas_marked_path_def, vv_post_inst_idx,
       hash_eval_operand_inst_idx, lookup_var_def] >>
  fs[lookup_var_def] >>
  conj_tac
  >- (strip_tac >> irule vv_store_bound_frame_mem_src >>
      qexists_tac `s` >> simp[hash_eval_operand_inst_idx]) >>
  strip_tac >>
  gvs[alloca_history_def, fn_has_code_def, same_blocks_def] >>
  rpt strip_tac >>
  Cases_on `k < LENGTH sm.cs_current_insts`
  >- metis_tac[] >>
  `k = LENGTH sm.cs_current_insts` by decide_tac >> gvs[] >>
  gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN, mk_inst_def]
QED
