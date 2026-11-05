(* Memory-checked binary operators: binop_frag_words (exprBopSimDefs) on a
   memory-checked path, and the counted composition of exprSimBopTyped for
   expr_sim_mem. *)
Theory bodyBinopFragMemory
Ancestors
  bodyUnopFragMemory
  exprBopSimDefs exprBopSimProps exprSimBopTyped exprBopStraight
  exprSimMemDefs gasNormalPrefix
  gasContext gasSummary gasOutcome gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath fragGasPathMem fragGasSeqMem
  fragGasSeqAbort fragGasFresh fragExecMem allocaHistory allocaHistoryFragment
  exprSimProps exprSimDefs loweringPosts
  list rich_list
  fragExec varsExt freshWrites
  exprBopLowering loweringSlice localPtrsProps
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState valueEncoding venomExecSemantics venomInst
  venomState vyperValue
Libs
  pairLib

(* binop_frag_words on a memory-checked path: the operator's fragment from
   operands x and y holding w1 and w2 runs memory-safely and keeps the
   allocation history. *)
Definition binop_frag_mem_def:
  binop_frag_mem ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0 <=>
    !sa sb x y op s0.
      compile_binop bop x y ty bl el sa = (op, sb) /\
      expr_res_ok (bop_result cx ann bop tys v1 v2 es0) /\
      (!z. x = Var z ==> not_fresh_at sa z) /\
      (!z. y = Var z ==> not_fresh_at sa z) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es0 s0 /\ alloca_history func s0 /\
      eval_operand x s0 = SOME w1 /\ eval_operand y s0 = SOME w2 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?r. gas_marked_path T ctx func s0 0 r /\
        ((?s v. r = OK s /\
                 bop_result cx ann bop tys v1 v2 es0 = INL v /\
                 word_value v /\
                 stmt_state_rel ctx func cenv cx es0 s /\
                 eval_operand op s = SOME (val_to_w256 v) /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
                 s.vs_current_bb = sb.cs_current_bb /\
                 s.vs_inst_idx = LENGTH sb.cs_current_insts /\
                 alloca_history func s /\
                 s0.vs_alloca_next <= s.vs_alloca_next) \/
         (exit_result r /\ expr_exit (bop_result cx ann bop tys v1 v2 es0) r))
End

(* binop_frag_straight (exprBopStraight) for the memory-checked path, at
   any operand words.  A straight_fresh fragment writes only through
   fresh_write_op opcodes, so it passes the memory checks from any state
   and leaves the allocations as they were. *)
Theorem binop_frag_mem_straight:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0.
    (!x y. straight_fresh (compile_binop bop x y ty bl el)) /\
    (expr_res_ok (bop_result cx ann bop tys v1 v2 es0) ==>
     (?v. bop_result cx ann bop tys v1 v2 es0 = INL v /\ word_value v /\
          !x y sa sb op ss.
            compile_binop bop x y ty bl el sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME w1 /\ eval_operand y ss = SOME w2 ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                  eval_operand op ss' = SOME (val_to_w256 v)) \/
     (?m. bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError m)) /\
          !x y sa sb op ss.
            compile_binop bop x y ty bl el sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME w1 /\ eval_operand y ss = SOME w2 ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss =
                    Abort Revert_abort ss')) ==>
    binop_frag_mem ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0
Proof
  rpt gen_tac >> strip_tac >> simp[binop_frag_mem_def] >> rpt gen_tac >>
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s0) = SOME w1 /\
   eval_operand y (drop_fresh sa s0) = SOME w2` by
    metis_tac[eval_operand_drop_fresh] >>
  `straight_fresh (compile_binop bop x y ty bl el)` by simp[] >>
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
  >- (qpat_x_assum `!x y sa sb op ss. _`
        (qspecl_then [`x`, `y`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
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
      gvs[gas_marked_path_def] >> metis_tac[]) >>
  qpat_x_assum `!x y sa sb op ss. _`
    (qspecl_then [`x`, `y`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
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

(* bop_normal_prefix_summary (exprBopSimProps) on the memory-checked path,
   carrying the allocation history. *)
Theorem bop_normal_prefix_summary_mem:
  gas_value_prefix T (ctx, func, cenv, cx) (expr_type e1, e1)
    (sa, s1, x) (es, s0) left (v1, mid, t) /\
  gas_value_prefix T (ctx, func, cenv, cx) (expr_type e1, e2)
    (s1, s2, y) (mid with gas_obs := [], t) right (v2, fin, u) /\
  gas_admissible
    (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx r od) expr_res_ok es /\
  compile_binop bop x y (expr_type e1) bl el s2 = (op, sb) /\
  fn_has_code s2 sb func /\ is_word_type ann /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\
  binop_frag_mem ctx func cenv cx bop (expr_type e1) ann bl el
    [expr_type e1; expr_type e2] v1 v2
    (typed_val_to_w256 tv1 v1) (typed_val_to_w256 tv2 v2)
    (fin with gas_obs := []) ==>
  gas_summary_at T (ctx, func) (left ++ right)
    (do r <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx r od) (es, s0)
    (\res ee ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
        es sa sb s0 ee v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_value_prefix _ _ _ (sa, s1, x) _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [gas_value_prefix_def]) >>
  qpat_x_assum `gas_value_prefix _ _ _ (s1, s2, y) _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [gas_value_prefix_def]) >>
  `expr_res_ok (bop_result cx ann bop [expr_type e1; expr_type e2]
     v1 v2 (fin with gas_obs := []))` by
    metis_tac[bop_result_admissible] >>
  `eval_operand x t = SOME (typed_val_to_w256 tv1 v1) /\
   eval_operand y u = SOME (typed_val_to_w256 tv2 v2)` by
    (conj_tac >> irule expr_val_rel_typed >>
     gvs[expr_post_def] >> metis_tac[]) >>
  `eval_operand x u = SOME (typed_val_to_w256 tv1 v1)` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`s1`, `t`] >>
     gvs[expr_post_def]) >>
  `(!z. x = Var z ==> not_fresh_at s2 z) /\
   local_ptrs_reserved cenv s2` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (fin with gas_obs := []) u` by
    gvs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_mem_def]) >>
  disch_then (qspecl_then [`s2`, `sb`, `x`, `y`, `op`, `u`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `gas_marked_exec T (ctx, func)
     (do result <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
         read_result cx result od)
     (es, s0) (left ++ right)
     (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 fin) fin r` by
    metis_tac[bop_marked_exec_normal] >>
  simp[gas_summary_at_def] >>
  goal_assum (drule_at Any) >> simp[]
  >- (disj1_tac >> simp[] >>
      `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
        metis_tac[bop_marked_scopes_dom] >>
      qexists_tac `v` >> gvs[] >>
      irule expr_post_bop >>
      qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[]) >>
  metis_tac[bop_result_gas_obs]
QED

(* compile_bop_typed_sim (exprSimBopTyped) for expr_sim_mem. *)
Theorem compile_bop_typed_sim_mem:
  !ctx func cenv cx ty ann bop e1 e2 es tv1 tv2.
    ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
    ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
    is_word_type ann /\
    is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    is_word_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e2 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!x y sa sb op.
       compile_binop bop x y (expr_type e1)
         (if bop = Exp then expr_int_literal e1 else NONE)
         (if bop = Exp then expr_int_literal e2 else NONE) sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim_mem ctx func cenv cx (expr_type e1) e1 es /\
    (!gs1 v1 es1. (do result <- eval_expr cx e1; read_result cx result od)
        (es with gas_obs := gs1) = (INL v1, es1) ==>
       expr_sim_mem ctx func cenv cx (expr_type e1) e2 es1 /\
       !gs2 v2 es2. (do result <- eval_expr cx e2; read_result cx result od)
         (es1 with gas_obs := gs2) = (INL v2, es2) ==>
         binop_frag_mem ctx func cenv cx bop (expr_type e1) ann
           (if bop = Exp then expr_int_literal e1 else NONE)
           (if bop = Exp then expr_int_literal e2 else NONE)
           [expr_type e1; expr_type e2] v1 v2
           (typed_val_to_w256 tv1 v1) (typed_val_to_w256 tv2 v2) es2) ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- simp[vyperASTTheory.expr_type_def] >>
    drule_all lower_value_bop >> strip_tac >>
  qpat_x_assum `!sa sb op. lower_value _ _ _ e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ _ e2 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x y sa sb op. compile_binop _ _ _ _ _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `cs_extends s1 sb /\ cs_extends sa s2` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func`
    by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[bop_first_admissible] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "left_normal"
      >> suspend "left_exit") >>
  suspend "left_exempt"
QED

Resume compile_bop_typed_sim_mem[left_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >> rename1 `expr_post _ _ _ _ e1 _ _ _ _ _ v1 _ t` >>
  `gas_value_prefix T (ctx, func, cenv, cx) (expr_type e1, e1)
     (sa, s1, x) (es, s0) marks (v1, es_end, t)` by
    simp[gas_value_prefix_def] >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` mp_tac) >>
  strip_tac >>
  qpat_x_assum `!gs1 v1 es1. _`
    (mp_tac o REWRITE_RULE [ETA_AX]) >>
  disch_then drule >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx))
     expr_res_ok (es_end with gas_obs := [])` by
    metis_tac[bop_second_admissible] >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    gvs[expr_post_def] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `y`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "right_normal"
      >> suspend "right_exit") >>
  suspend "right_exempt"
QED
Resume compile_bop_typed_sim_mem[left_exit]:
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >>
  conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gnvs[]
QED
Resume compile_bop_typed_sim_mem[left_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  drule (REWRITE_RULE [ETA_AX] bop_first_exempt_cert) >> metis_tac[]
QED
Resume compile_bop_typed_sim_mem[right_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >> rename1 `expr_post _ _ _ _ e2 _ _ _ _ _ v2 _ u` >>
  `gas_value_prefix T (ctx, func, cenv, cx) (expr_type e1, e2)
     (s1, s2, y) (es_end with gas_obs := [], t) marks' (v2, es_end', u)` by
    simp[gas_value_prefix_def] >>
  qpat_assum `gas_marked_exec _ _ _ _ _ (INL v2) _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `!gs2 v2 es2. _` drule >> strip_tac >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  pure_rewrite_tac[ETA_AX] >>
  irule (REWRITE_RULE [ETA_AX] bop_normal_prefix_summary_mem) >>
  qpat_assum `gas_value_prefix _ _ _ (sa, s1, x) _ _ _` (irule_at Any) >>
  qpat_assum `gas_value_prefix _ _ _ (s1, s2, y) _ _ _` (irule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED
Resume compile_bop_typed_sim_mem[right_exit]:
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >>
  conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v1) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gnvs[]
QED
Resume compile_bop_typed_sim_mem[right_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any (REWRITE_RULE [ETA_AX] bop_second_exempt_cert) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Finalise compile_bop_typed_sim_mem

(* compile_bop_sim (exprSimBopTyped) for expr_sim_mem: operands of word
   values, held in their plain words. *)
Theorem compile_bop_sim_mem:
  !ctx func cenv cx ty ann bop e1 e2 es.
    ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
    ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
    is_word_type ann /\
    is_word_type (expr_type e1) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
    is_word_type (expr_type e2) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e2)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!sa sb op.
       lower_value compile_expr cenv (expr_type e1) e2 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) /\
    (!x y sa sb op.
       compile_binop bop x y (expr_type e1)
         (if bop = Exp then expr_int_literal e1 else NONE)
         (if bop = Exp then expr_int_literal e2 else NONE) sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim_mem ctx func cenv cx (expr_type e1) e1 es /\
    (!gs1 v1 es1. (do result <- eval_expr cx e1; read_result cx result od)
       (es with gas_obs := gs1) = (INL v1, es1) ==>
       word_value v1 /\
       expr_sim_mem ctx func cenv cx (expr_type e1) e2 es1 /\
       !gs2 v2 es2. (do result <- eval_expr cx e2; read_result cx result od)
         (es1 with gas_obs := gs2) = (INL v2, es2) ==>
         word_value v2 /\
         binop_frag_mem ctx func cenv cx bop (expr_type e1) ann
           (if bop = Exp then expr_int_literal e1 else NONE)
           (if bop = Exp then expr_int_literal e2 else NONE)
           [expr_type e1; expr_type e2] v1 v2
           (val_to_w256 v1) (val_to_w256 v2) es2) ==>
    expr_sim_mem ctx func cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `IS_SOME (evaluate_type _ (expr_type e1))`
    (qx_choose_then `t1` assume_tac o
     REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ (expr_type e2))`
    (qx_choose_then `t2` assume_tac o
     REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule compile_bop_typed_sim_mem >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t1`, `t2`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs1 v1 es1. _ ==> word_value v1 /\ _` drule >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs2 v2 es2. _ ==> word_value v2 /\ _` drule >> strip_tac >>
  gvs[typed_val_to_w256_word_value]
QED
