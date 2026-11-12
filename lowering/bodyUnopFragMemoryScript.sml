(* Memory-checked unary builtins: the counted unop composition of
   exprSimUnopCompose with the memory checks of expr_sim_mem. *)
Theory bodyUnopFragMemory
Ancestors
  exprSimUnop exprUnopStraight exprUnopSimDefs exprSimUnopCompose
  exprSimUnopComposeProps exprSimUnopProps exprSimMemDefs
  gasContext gasSummary gasOutcome gasSummaryCompose gasExemptCert
  gasNormalPrefix fragGasMode fragGasPath fragGasPathMem fragGasSeqMem
  fragGasSeqAbort fragGasFresh fragExecMem allocaHistory allocaHistoryFragment
  exprSimSource exprSimMemoryStack exprSimHypsDefs
  instMemFrontier memSafeRun venomExecProofs venomInstProofs instIdxIndep rich_list
  exprSimProps exprSimDefs loweringPosts
  arithmetic list integer words integer_word byte
  fragExec varsExt freshWrites
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  builtinSimple builtinProps arithmeticProps vyperArith
  compileEnv vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation valueEncoding venomExecSemantics venomInst venomState
  vyperTyping vyperTypeSystem
Libs
  intLib pairLib

(* unop_frag (exprUnopSimDefs) on a memory-checked path: the builtin's
   fragment f from an operand x holding w1 runs memory-safely and keeps
   the allocation history. *)
Definition unop_frag_mem_def:
  unop_frag_mem ctx func cenv cx f w1 t res es0 <=>
    !sa sb x op s0.
      f x sa = (op, sb) /\ expr_res_ok res /\
      (!z. x = Var z ==> not_fresh_at sa z) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es0 s0 /\ alloca_history func s0 /\
      eval_operand x s0 = SOME w1 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?r. gas_marked_path T ctx func s0 0 r /\
        ((?s v. r = OK s /\ res = INL v /\
                 stmt_state_rel ctx func cenv cx es0 s /\
                 expr_val_rel cx t v op s /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
                 s.vs_current_bb = sb.cs_current_bb /\
                 s.vs_inst_idx = LENGTH sb.cs_current_insts /\
                 alloca_history func s /\
                 s0.vs_alloca_next <= s.vs_alloca_next) \/
         (exit_result r /\ expr_exit res r))
End

(* Fresh-write opcodes touch no memory and read no data section. *)
Theorem writes_fresh_mem_ok:
  !sa code s. writes_fresh sa code ==> run_inst_seq_mem_ok code s
Proof
  rpt strip_tac >> irule run_inst_seq_mem_ok_every >>
  fs[writes_fresh_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> rw[fresh_write_op_def] >>
  gvs[below_frontier_no_ranges, inst_dload_in_section_other]
QED

(* run_inst_seq_abort_zero_path (fragGasSeqAbort) on the memory-checked
   path. *)
Theorem run_inst_seq_abort_zero_path_mem:
  !code s t a ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_marked_path T ctx func s 0
      (Abort a (t with vs_inst_idx := j))
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, run_inst_seq_mem_ok_def]
  >- (rename1 `step_inst_base h s = OK u` >>
      `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      disch_then (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `j` >>
      drule_at (Pat `step_inst_base _ _ = OK _`) gas_marked_path_step >>
      simp[] >> disch_then irule >> metis_tac[]) >>
  qexists_tac `t.vs_inst_idx` >> simp[] >>
  drule gas_marked_path_abort >> simp[] >> metis_tac[]
QED

(* unop_frag_straight for the memory-checked path. A straight_fresh
   fragment writes only through fresh_write_op opcodes (pure arithmetic,
   comparisons and ASSERT): no memory access, no DLOAD/DLOADBYTES and no
   ALLOCA, so its instructions pass the memory checks of gas_path_mem from
   any state and leave the allocations as they were. *)
Theorem unop_frag_mem_straight:
  !ctx func cenv cx f w1 t res es0.
    (!x. straight_fresh (f x)) /\ is_word_type t /\
    (expr_res_ok res ==>
     (?v w. res = INL v /\
            (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
                  w = typed_val_to_w256 tv v) /\
            !x sa sb op ss.
              f x sa = (op, sb) /\ fresh_vars_wrt sa ss /\
              eval_operand x ss = SOME w1 ==>
              ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                    eval_operand op ss' = SOME w) \/
     (?m. res = INR (Error (RuntimeError m)) /\
          !x sa sb op ss.
            f x sa = (op, sb) /\ fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME w1 ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss =
                    Abort Revert_abort ss')) ==>
    unop_frag_mem ctx func cenv cx f w1 t res es0
Proof
  rpt gen_tac >> strip_tac >> simp[unop_frag_mem_def] >> rpt gen_tac >>
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s0) = SOME w1` by
    metis_tac[eval_operand_drop_fresh] >>
  qpat_x_assum `!x. straight_fresh (f x)`
    (qspec_then `x` assume_tac) >>
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
  qpat_x_assum `expr_res_ok _ ==> _` drule >> strip_tac
  >- (qpat_x_assum `!x sa sb op ss. _`
        (qspecl_then [`x`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
      simp[] >> strip_tac >>
      drule_all straight_fresh_clean_success_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      drule_all straight_fresh_run_post >> strip_tac >>
      qmatch_asmsub_rename_tac `vars_ext ss' target` >>
      `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
        metis_tac[writes_fresh_gas_count] >>
      qspecl_then [`emitted_insts sa sb`, `s0`, `target`, `ctx`, `func`, `bb`]
        mp_tac run_inst_seq_gas_path_mem >>
      (impl_tac >- (simp[] >> fs[EVERY_MEM])) >>
      strip_tac >>
      qspecl_then [`func`, `bb`, `s0`, `emitted_insts sa sb`, `rest`, `target`]
        mp_tac alloca_history_run_inst_seq >>
      (impl_tac >- (fs[stmt_state_rel_def] >> fs[EVERY_MEM])) >>
      strip_tac >>
      qspecl_then [`emitted_insts sa sb`, `sa`, `s0`, `target`]
        mp_tac run_inst_seq_writes_fresh >>
      (impl_tac >- simp[]) >> strip_tac >>
      `target.vs_alloca_next = s0.vs_alloca_next` by
        (qpat_x_assum `target = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
      qexists_tac `OK (target with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
      gvs[gas_marked_path_def] >> simp[expr_val_rel_def] >> metis_tac[]) >>
  qpat_x_assum `!x sa sb op ss. _`
    (qspecl_then [`x`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
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

(* compile_not_frag (exprSimUnop) on the memory-checked path. *)
Theorem compile_not_frag_mem:
  !ctx func cenv cx ann tys v1 es0 tv1.
    (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
     is_flag_type ann) /\
    evaluate_type (get_tenv cx) ann = SOME tv1 /\ value_has_type tv1 v1 /\
    (!nsid m. ann = FlagT nsid /\ tv1 = FlagTV m ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    unop_frag_mem ctx func cenv cx
      (\x. if ann = BaseT BoolT then emit_op ISZERO [x]
           else compile_invert x ann cenv)
      (typed_val_to_w256 tv1 v1) ann (unop_result cx ann Not tys v1 es0) es0
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP not_type_cases)
                              strip_assume_tac) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  irule unop_frag_mem_straight >>
  (conj_tac
   >- (gen_tac >> simp[compile_invert_def, LET_THM] >>
       irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
  (conj_tac >- simp[is_word_type_def]) >>
  disch_then kall_tac >> disj1_tac >>
  Cases_on `v1` >>
  gvs[value_has_type_def, unop_result_def, evaluate_builtin_def,
      vyperASTTheory.type_to_int_bound_def, typed_val_to_w256_def,
      val_to_w256_def, compile_invert_def, vyperValueTheory.evaluate_type_def]
  >~ [`emit_op ISZERO`]
  >- (rpt strip_tac >> drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
      qexists_tac `ss'` >> asm_rewrite_tac[] >> BasicProvers.every_case_tac >>
      gvs[bool_to_word_def])
  >~ [`i2w _`]
  >- (rename1 `Num i` >> rpt strip_tac >>
      drule_all emit_op_NOT_correct >> rw[] >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      simp[integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def])
  >~ [`PAD_RIGHT`]
  >- (rename1 `LENGTH bs = 32` >> rpt strip_tac >> gvs[listTheory.PAD_RIGHT] >>
      drule_all emit_op_NOT_correct >> rw[] >>
      simp[listTheory.PAD_RIGHT, length_word_to_bytes_be,
           word_of_bytes_be_to_bytes]) >>
  rename1 `k < 2 ** m` >> rpt strip_tac >>
  qspecl_then [`XOR`, `word_xor`, `x`, `Lit (n2w (2 ** m - 1))`, `n2w k`,
               `n2w (2 ** m - 1)`, `sa`, `op`, `sb`, `ss`]
    mp_tac emit_op_pure2_correct >>
  impl_tac
  >- (simp[eval_operand_def] >> irule step_XOR >> simp[eval_operand_def]) >>
  rw[] >> simp[flag_not_xor]
QED

(* compile_abs_frag (exprSimUnop) on the memory-checked path. *)
Theorem compile_abs_frag_mem:
  !ctx func cenv cx tys v1 es0.
    value_has_type (BaseTV (IntT 256)) v1 ==>
    unop_frag_mem ctx func cenv cx compile_builtin_abs
      (typed_val_to_w256 (BaseTV (IntT 256)) v1) (BaseT (IntT 256))
      (unop_result cx (BaseT (IntT 256)) Abs tys v1 es0) es0
Proof
  rpt strip_tac >> irule unop_frag_mem_straight >>
  rpt conj_tac
  >- simp[straight_fresh_abs]
  >- simp[is_word_type_def] >>
  disch_then kall_tac >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `within_int_bound _ i` >>
  drule int256_abs_bound >> strip_tac >>
  drule_all abs_i2w >> strip_tac >>
  simp[unop_result_def, evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, bounded_int_op_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `i = INT_MIN (:256)`
  >- (`i2w i = (INT_MINw : bytes32)` by metis_tac[] >>
      qpat_x_assum `i = _`
        (fn th => REWRITE_TAC [EQT_INTRO (SIMP_RULE (srw_ss()) [] th)]) >>
      disj2_tac >> simp[] >>
      rpt strip_tac >> drule_all compile_builtin_abs_run >> simp[]) >>
  `i2w i <> (INT_MINw : bytes32)` by metis_tac[] >>
  qpat_x_assum `i <> _`
    (fn th => REWRITE_TAC [EQF_INTRO (SIMP_RULE (srw_ss()) [] th)]) >>
  disj1_tac >>
  simp[vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
       val_to_w256_def] >>
  rpt strip_tac >> drule_all compile_builtin_abs_run >>
  disch_then (drule o CONJUNCT1) >> strip_tac >>
  qexists_tac `ss'` >> asm_rewrite_tac[] >> simp[]
QED

(* compile_neg_frag (exprSimUnop) on the memory-checked path. *)
Theorem compile_neg_frag_mem:
  !ctx func cenv cx t tv v es.
    is_numeric_type t /\ ~is_uint_type t /\
    evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v ==>
    unop_frag_mem ctx func cenv cx (\x. compile_neg x t)
      (typed_val_to_w256 tv v) t (unop_result cx t Neg [t] v es) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all neg_typed_source >> disch_then (qspec_then `es` assume_tac) >>
  irule unop_frag_mem_straight >>
  (conj_tac >- (gen_tac >> BETA_TAC >>
    irule (CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg))) >>
  (conj_tac >- (Cases_on `t` >>
    gvs[is_numeric_type_def, is_int_type_def, is_word_type_def] >>
    rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def])) >>
  disch_then kall_tac >>
  Cases_on `w2i (FST (type_bounds t)) < w2i (typed_val_to_w256 tv v)` >>
  gvs[] >> rpt strip_tac >> drule_all compile_neg_run >> simp[]
QED

(* unop_continuation_summary (exprSimUnopComposeProps) on the
   memory-checked path, carrying the allocation history. *)
Theorem unop_continuation_summary_mem:
  expr_post ctx func cenv cx e1 es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  alloca_history func t0 /\ s0.vs_alloca_next <= t0.vs_alloca_next /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  unop_frag_mem ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
    (unop_result cx ann bi [expr_type e1] v1 ee) (ee with gas_obs := []) /\
  expr_res_ok (unop_result cx ann bi [expr_type e1] v1 ee) /\
  f x s1 = (op,sb) /\ (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s1 /\ is_word_type ann /\
  is_word_type (expr_type e1) /\ sa.cs_next_var <= s1.cs_next_var ==>
  gas_summary_at T (ctx,func) []
    (\vs. (unop_result cx ann bi [expr_type e1] v1 vs,vs))
    (ee with gas_obs := [],t0)
    (\res fin t. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin ann bi [e1]) es sa sb s0 fin v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
   eval_operand x t0 = SOME (typed_val_to_w256 tv1 v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  qpat_x_assum `unop_frag_mem _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [unop_frag_mem_def]) >>
  disch_then (qspecl_then [`s1`,`sb`,`x`,`op`,`t0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (simp[gas_summary_at_def] >>
      qexistsl_tac [`unop_result cx ann bi [expr_type e1] v1 ee`,`ee`,`r`] >>
      conj_tac
      >- (simp[gas_marked_exec_def, unop_result_gas_obs] >> metis_tac[]) >>
      gvs[] >> irule expr_post_unop >> simp[] >>
      qexistsl_tac [`s1`,`t0`,`v1`,`x`] >> simp[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`unop_result cx ann bi [expr_type e1] v1 ee`,`ee`,`r`] >>
  simp[gas_marked_exec_def, unop_result_gas_obs]
QED

(* compile_unop_sim (exprSimUnopCompose) for expr_sim_mem. *)
Theorem compile_unop_sim_mem:
  !ctx func cenv cx ty ann bi e1 ty1 f es.
    bi <> Len /\ ~precompile_builtin bi /\ builtin_args_length_ok bi 1 /\
    is_word_type ann /\ is_word_type (expr_type e1) /\
    (!sa sb op.
       lower_value compile_expr cenv ty (Builtin ann bi [e1]) sa = (op, sb) ==>
       ?x s1. lower_value compile_expr cenv ty1 e1 sa = (x, s1) /\
              f x s1 = (op, sb)) /\
    (!sa sb op.
       lower_value compile_expr cenv ty1 e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z)) /\
    (!x sa sb op. f x sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim_mem ctx func cenv cx ty1 e1 es /\
    (!gs1 v1 es1. (do r <- eval_expr cx e1; read_result cx r od)
        (es with gas_obs := gs1) = (INL v1, es1) ==>
       ?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
             unop_frag_mem ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
               (unop_result cx ann bi [expr_type e1] v1 es1) es1) ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann bi [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- simp[vyperASTTheory.expr_type_def] >>
    qpat_x_assum `!sa sb op. lower_value _ _ ty (Builtin _ _ _) _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty1 e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x sa sb op. f _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> qexistsl_tac [`ann`,`bi`] >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      asm_simp_tac (srw_ss()) [eval_expr_unop_action_general] >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
      strip_tac
      >- (gvs[] >>
          `bind (eval_expr cx e1) (read_result cx)
             (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL v, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          qpat_x_assum `!gs1 v1 es1. _`
            (drule o CONV_RULE (DEPTH_CONV ETA_CONV)) >> strip_tac >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `expr_res_ok (unop_result cx ann bi [expr_type e1] v es_end)` by
            (qpat_x_assum `gas_admissible (bind (eval_expr cx (Builtin _ _ _)) _) _ es`
               (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
             disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
             asm_simp_tac (srw_ss()) [eval_expr_unop_action_general] >>
             simp[bind_def, unop_result_gas_obs] >>
             disch_then irule >> simp[]) >>
          fs[unop_result_gas_obs] >>
          drule_all unop_continuation_summary_mem >>
          simp[unop_result_gas_obs] >>
          rewrite_tac[gas_summary_at_def] >> strip_tac >>
          qexistsl_tac [`res`,`es_end'`,`r`] >>
          (conj_tac
           >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                      |> REWRITE_RULE [APPEND_NIL]) >>
               qexistsl_tac [`es_end`,`t`,`v`] >> gvs[]) >>
           gvs[])) >>
      Cases_on `res` >- gvs[] >>
      simp[gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >>
      simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      gvs[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule unop_exempt_cert >> simp[]
QED

(* not on a bool, uint256, bytes32 or flag operand (exprSimOperators'
   compile_not_case) for expr_sim_mem. *)
Theorem compile_not_sim_mem:
  !ctx func cenv cx env ty e es.
    (is_bool_type (expr_type e) \/ is_uint256_type (expr_type e) \/
     is_bytes32_type (expr_type e) \/ is_flag_type (expr_type e)) /\
    expr_body_pre cenv cx env e es /\
    expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
    expr_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `is_word_type (expr_type e)` by
    (qpat_x_assum `_ \/ _` (strip_assume_tac o MATCH_MP not_type_cases) >>
     gvs[is_word_type_def]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `expr_type e`, `Not`,
               `e`, `expr_type e`,
               `\x. if expr_type e = BaseT BoolT then emit_op ISZERO [x]
                    else compile_invert x (expr_type e) cenv`, `es`]
    mp_tac compile_unop_sim_mem >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[]
    >- simp[]
    >- (rpt strip_tac >> drule lower_value_not >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
    >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
        simp[straight_fresh_not])
    >- simp[] >>
    rpt strip_tac >>
    qspecl_then [`cenv`, `cx`, `env`, `e`, `es with gas_obs := gs1`, `v1`, `es1`]
      mp_tac expr_body_pre_word_value >>
    simp[] >> strip_tac >> gvs[] >>
    irule_at Any compile_not_frag_mem >> gvs[] >>
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
    simp[expr_body_pre_def, expr_sim_inv_def] >> rpt strip_tac >>
    first_x_assum irule >>
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  simp[]
QED

Theorem compile_not_vv_sim_mem:
  !ctx func cenv cx env ty e es.
    (is_bool_type (expr_type e) \/ is_uint256_type (expr_type e) \/
     is_bytes32_type (expr_type e) \/ is_flag_type (expr_type e)) /\
    expr_body_pre cenv cx env e es /\
    expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `is_word_type (expr_type (Builtin (expr_type e) Not [e]))` by
    (simp[vyperASTTheory.expr_type_def] >>
      qpat_x_assum `_ \/ _` (strip_assume_tac o MATCH_MP not_type_cases) >>
      gvs[is_word_type_def]) >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  rpt conj_tac
  >~ [`compile_expr`] >- simp[compile_not_abs_stack]
  >~ [`eval_expr`] >- metis_tac[eval_expr_builtin_value] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `ty`, `e`, `es`]
    mp_tac compile_not_sim_mem >>
  metis_tac[]
QED
