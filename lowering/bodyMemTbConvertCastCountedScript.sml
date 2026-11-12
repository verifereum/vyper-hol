(* Counted read-only bytestring cast execution and allocation history. *)
Theory bodyMemTbConvertCastCounted
Ancestors
  bodyMemTbConvertCastMemory exprSimConvertBytes allocaHistoryFragment
  fragExec exprLoweringProps fragGasMode fragGasPathMem compileEnv venomState
  venomExecSemantics varsExt freshWrites rich_list list loweringPosts

Theorem convert_cast_counted_mem:
  compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  stmt_state_rel ctx func cenv cx es s /\ eval_operand x s = SOME p /\
  w2n p + 32 <= s.vs_alloca_next /\ mload (w2n p) s = n2w L /\ L <= i /\
  i < dimword (:256) /\ n < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?t. gas_marked_path T ctx func s 0 (OK t) /\ L <= n /\
     stmt_state_rel ctx func cenv cx es t /\ eval_operand op t = SOME p /\
     t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
     (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==>
            lookup_var z t = SOME w) /\
     t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next) \/
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t) /\ n < L)
Proof
  strip_tac >> drule convert_cast_static_frame >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb)
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND,
         emitted_insts_def] >> simp[DROP_APPEND]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def] >>
  drule_all convert_bytestring_cast_paths_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `L <= n`
  >- suspend "success" >>
  disj2_tac >> `n < L` by decide_tac >>
  drule_all convert_cast_abort_run >> strip_tac >>
  metis_tac[]
QED

Resume convert_cast_counted_mem[success]:
  disj1_tac >> drule_all convert_cast_run_frame >> strip_tac >>
  `alloca_history func (tt with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`alloca_history func
        (tt with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))`
       suffices_by simp[] >>
     irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
     fs[IS_PREFIX_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es tt` by
    (irule convert_readonly_state_frame >> qexistsl_tac [`s`, `sa`] >> simp[]) >>
  `eval_operand x tt = SOME p` by
    (Cases_on `x` >> gvs[eval_operand_def] >>
     qpat_x_assum `tt = _` (fn th => once_rewrite_tac[th]) >>
     simp[eval_operand_def]) >>
  qexists_tac `tt with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx] >>
  qpat_x_assum `tt = _` (fn th => once_rewrite_tac[th]) >>
  simp[lookup_var_def, same_blocks_def] >> fs[same_blocks_def, lookup_var_def]
QED

Finalise convert_cast_counted_mem
