(* Memory-checked suffix introduction for list-indexed word builtins. *)
Theory bodyMemBiWordFrag
Ancestors
  bodyBinopFragMemory exprSimWordArgs bodyUnopFragMemory
  exprBopStraight exprSimMemDefs gasNormalPrefix
  gasContext gasSummary gasOutcome gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath fragGasPathMem fragGasSeqMem
  fragGasSeqAbort fragGasFresh fragExecMem allocaHistory allocaHistoryFragment
  exprSimProps exprSimDefs loweringPosts
  list rich_list fragExec varsExt freshWrites
  exprBopLowering loweringSlice localPtrsProps
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState valueEncoding venomExecSemantics venomInst
  venomState vyperValue
Libs
  pairLib

Theorem word_builtin_mem_success:
  !ctx func cenv cx code res vs es0 v.
    res = INL v /\ word_value v /\
    (!xs. straight_fresh (code xs)) /\
    (!xs sa sb op ss.
       code xs sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       LIST_REL (\x v. eval_operand x ss = SOME (val_to_w256 v)) xs vs ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
             eval_operand op ss' = SOME (val_to_w256 v)) ==>
    !sa sb xs op s0.
      code xs sa = (op, sb) /\ expr_res_ok res /\
      EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es0 s0 /\ alloca_history func s0 /\
      LIST_REL (\x v. eval_operand x s0 = SOME (val_to_w256 v)) xs vs /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?r. gas_marked_path T ctx func s0 0 r /\
        ((?s v. r = OK s /\ res = INL v /\ word_value v /\
                stmt_state_rel ctx func cenv cx es0 s /\
                eval_operand op s = SOME (val_to_w256 v) /\
                (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                       lookup_var z s = SOME w) /\
                (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                         FLOOKUP s.vs_allocas aid = SOME b) /\
                s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
                s.vs_current_bb = sb.cs_current_bb /\
                s.vs_inst_idx = LENGTH sb.cs_current_insts /\
                alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next) \/
         (exit_result r /\ expr_exit res r))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  `LIST_REL (\x v. eval_operand x (drop_fresh sa s0) = SOME (val_to_w256 v)) xs vs` by
    (drule word_operands_drop_fresh >> simp[]) >>
  `straight_fresh (code xs)` by simp[] >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    metis_tac[writes_fresh_mem_ok] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `?rest. DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest`
    by fs[IS_PREFIX_APPEND] >>
  `s0.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts`
    by simp[] >>
  qpat_x_assum `!xs sa sb op ss. _`
    (qspecl_then [`xs`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  qmatch_asmsub_rename_tac `vars_ext ss' target` >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    metis_tac[writes_fresh_gas_count] >>
  qspecl_then [`emitted_insts sa sb`, `s0`, `target`, `ctx`, `func`, `bb`]
    mp_tac run_inst_seq_gas_path_mem >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >> strip_tac >>
  qspecl_then [`func`, `bb`, `s0`, `emitted_insts sa sb`, `rest`, `target`]
    mp_tac alloca_history_run_inst_seq >>
  (impl_tac >- (fs[stmt_state_rel_def] >> fs[EVERY_MEM])) >> strip_tac >>
  qspecl_then [`emitted_insts sa sb`, `sa`, `s0`, `target`]
    mp_tac run_inst_seq_writes_fresh >>
  (impl_tac >- simp[]) >> strip_tac >>
  `target.vs_alloca_next = s0.vs_alloca_next` by
    (qpat_x_assum `target = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  qexists_tac `OK (target with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  gvs[gas_marked_path_def] >> metis_tac[]
QED

Theorem word_builtin_mem_revert:
  !ctx func cenv cx code res vs es0 msg.
    res = INR (Error (RuntimeError msg)) /\
    (!xs. straight_fresh (code xs)) /\
    (!xs sa sb op ss.
       code xs sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       LIST_REL (\x v. eval_operand x ss = SOME (val_to_w256 v)) xs vs ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss') ==>
    !sa sb xs op s0.
      code xs sa = (op, sb) /\ expr_res_ok res /\
      EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es0 s0 /\ alloca_history func s0 /\
      LIST_REL (\x v. eval_operand x s0 = SOME (val_to_w256 v)) xs vs /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?r. gas_marked_path T ctx func s0 0 r /\
        ((?s v. r = OK s /\ res = INL v /\ word_value v /\
                stmt_state_rel ctx func cenv cx es0 s /\
                eval_operand op s = SOME (val_to_w256 v) /\
                (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                       lookup_var z s = SOME w) /\
                (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                         FLOOKUP s.vs_allocas aid = SOME b) /\
                s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
                s.vs_current_bb = sb.cs_current_bb /\
                s.vs_inst_idx = LENGTH sb.cs_current_insts /\
                alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next) \/
         (exit_result r /\ expr_exit res r))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  `LIST_REL (\x v. eval_operand x (drop_fresh sa s0) = SOME (val_to_w256 v)) xs vs` by
    (drule word_operands_drop_fresh >> simp[]) >>
  `straight_fresh (code xs)` by simp[] >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    metis_tac[writes_fresh_mem_ok] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `?rest. DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest`
    by fs[IS_PREFIX_APPEND] >>
  qpat_x_assum `!xs sa sb op ss. _`
    (qspecl_then [`xs`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
  simp[] >> strip_tac >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >>
     simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  qmatch_asmsub_rename_tac `run_inst_seq _ s0 = Abort Revert_abort endt` >>
  qspecl_then [`emitted_insts sa sb`, `s0`, `endt`, `Revert_abort`, `ctx`,
               `func`, `bb`] mp_tac run_inst_seq_abort_zero_path_mem >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >> strip_tac >>
  qexists_tac `Abort Revert_abort (endt with vs_inst_idx := j)` >>
  simp[exit_result_def, expr_exit_def]
QED
