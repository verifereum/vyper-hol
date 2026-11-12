(* Forced RHS and arithmetic execution, with constructor storage abstracted
   by a callback at the actual post-RHS source state. *)
Theory immutableAugAssignContinuation
Ancestors
  augAssignPlaceRhsContinuation exprSimWordArgs
  bodyBinopFamiliesMemory bodyBinopFragMemory stmtSimAugAssignPlaceMemory
  gasOutcome gasSummary loweringPosts exprLowering vyperState

Theorem immutable_augassign_operator_mem[local]:
  bop <> In /\ bop <> NotIn /\ word_value cur /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE el
    [ty;expr_type e] cur rhs ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
  (!z. x = Var z ==> not_fresh_at s2 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  (!z. dst = Var z ==> not_fresh_at s2 z) /\
  fn_has_code s2 s3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s2 /\
  stmt_state_rel ctx func cenv cx ee s /\ alloca_history func s /\
  eval_operand x s = SOME (val_to_w256 cur) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  eval_operand dst s = SOME w /\ w2n w + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\
  (!v t. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v /\
    word_value v /\ stmt_state_rel ctx func cenv cx ee t /\
    eval_operand op t = SOME (val_to_w256 v) /\ eval_operand dst t = SOME w /\
    w2n w + 32 <= t.vs_alloca_next /\ alloca_history func t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
    (!z u. not_fresh_at s2 z /\ lookup_var z s = SOME u ==> lookup_var z t = SOME u) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = s3.cs_current_bb /\
    t.vs_inst_idx = LENGTH s3.cs_current_insts ==>
    ?ff u. (!tail. write_place cx (ImmutablePlace mid id path) v
                    (ee with gas_obs := tail) = (INL (),ff with gas_obs := tail)) /\
      gas_marked_path T ctx func t 0 (OK u) /\
      stmt_post ctx func cx lctx cenv cenv sa sf es_entry s_entry (INL ())
        (ff with gas_obs := []) u /\ alloca_history func u /\
      s_entry.vs_alloca_next <= u.vs_alloca_next) ==>
  ?res ff r.
    (!tail. bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (ImmutablePlace mid id path))
      (ee with gas_obs := tail) = (res,ff with gas_obs := tail)) /\
    gas_marked_path T ctx func s 0 r /\
    ((?u. r = OK u /\ res = INL () /\
      stmt_post ctx func cx lctx cenv cenv sa sf es_entry s_entry res
        (ff with gas_obs := []) u /\ alloca_history func u /\
      s_entry.vs_alloca_next <= u.vs_alloca_next) \/
     (exit_result r /\ !tail. stmt_exit RetQ (ff with gas_obs := tail) res r))
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule stmtSimAugAssignTheory.bop_result_augassign >> simp[] >>
     metis_tac[stmtSimAugAssignTheory.word_value_not_bytes]) >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_val_mem_def, binop_frag_mem_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `x`, `y`, `op`, `s`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (gvs[] >> rename1 `stmt_state_rel ctx func cenv cx ee t` >>
      `eval_operand dst t = SOME w` by
        (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_saved_operand >>
         qexistsl_tac [`s2`, `ctx`, `func`, `T`, `0`, `s`] >> simp[]) >>
      `w2n w + 32 <= t.vs_alloca_next` by
        metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
      qpat_x_assum `!t. stmt_state_rel _ _ _ _ _ t /\ _ ==> _`
        (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
      `gas_marked_path T ctx func s 0 (OK u)` by
        (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
      qexistsl_tac [`INL ()`, `ff`, `OK u`] >> simp[] >>
      Cases_on `evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        ptv bop cur rhs` >>
      gvs[bind_def, lift_sum_def, return_def, raise_def]) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
    ptv bop cur rhs`
  >- gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `_ = INR err` >>
  qexistsl_tac [`INR (Error err)`, `ee`, `r`] >>
  simp[bind_def, lift_sum_def, return_def, raise_def] >>
  gen_tac >> simp[stmtSimDefsTheory.stmt_exit_def] >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
    stmtSimPropsTheory.expr_exit_INR_type] >> gvs[]
QED

Theorem immutable_augassign_rhs_mem:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e s1 = (y,s2) /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
  fn_inst_ids_distinct func /\ bop <> In /\ bop <> NotIn /\ word_value cur /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  (!z. dst = Var z ==> not_fresh_at s1 z) /\
  (!z. not_fresh_at s1 z ==> not_fresh_at s2 z) /\
  (!l. x <> Label l /\ dst <> Label l) /\
  eval_operand x s0 = SOME (val_to_w256 cur) /\ eval_operand dst s0 = SOME w /\
  w2n w + 32 <= s0.vs_alloca_next /\
  is_word_type (expr_type e) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = s1.cs_current_bb /\
  s0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  (!rhs ee. ee.gas_obs = [] /\
     (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
           (INL rhs,ee)) ==>
     word_value rhs /\
     binop_frag_val_mem ctx func cenv cx bop ty ty NONE el
       [ty;expr_type e] cur rhs ee /\
     expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee)) /\
  (!rhs ee s v t.
    expr_post ctx func cenv cx e es s1 s2 s0 ee rhs y s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ee.gas_obs = [] /\
    (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
          (INL rhs,ee)) /\
    bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v /\
    word_value v /\ stmt_state_rel ctx func cenv cx ee t /\
    eval_operand op t = SOME (val_to_w256 v) /\ eval_operand dst t = SOME w /\
    w2n w + 32 <= t.vs_alloca_next /\ alloca_history func t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
    (!z u. not_fresh_at s2 z /\ lookup_var z s = SOME u ==> lookup_var z t = SOME u) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = s3.cs_current_bb /\
    t.vs_inst_idx = LENGTH s3.cs_current_insts ==>
    ?ff u. (!tail. write_place cx (ImmutablePlace mid id path) v
                    (ee with gas_obs := tail) = (INL (),ff with gas_obs := tail)) /\
      gas_marked_path T ctx func t 0 (OK u) /\
      stmt_post ctx func cx lctx cenv cenv sa sf es_entry s_entry (INL ())
        (ff with gas_obs := []) u /\ alloca_history func u /\
      s_entry.vs_alloca_next <= u.vs_alloca_next) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx (ImmutablePlace mid id path)))) (es,s0)
    (\res ff u. res = INL () /\
      stmt_post ctx func cx lctx cenv cenv sa sf es_entry s_entry res ff u /\
      alloca_history func u /\ s_entry.vs_alloca_next <= u.vs_alloca_next)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)
Proof
  strip_tac >> irule aug_place_rhs_mem_continuation >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> simp[stmtSimDefsTheory.stmt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
        stmtSimPropsTheory.expr_exit_INR_type] >> simp[]) >>
  qexistsl_tac [`cenv`, `y`, `s1`, `s2`, `ty`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!rhs ee. _ ==> _`
    (qspecl_then [`v`, `ee`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `eval_operand y t = SOME (val_to_w256 v)` by
    (drule_all expr_post_word_operand >> simp[]) >>
  `eval_operand x t = SOME (val_to_w256 cur) /\ eval_operand dst t = SOME w` by
    (conj_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`s1`, `s0`] >> gvs[expr_post_def]) >>
  `w2n w + 32 <= t.vs_alloca_next` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `!z. y = Var z ==> not_fresh_at s2 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `(!z. x = Var z ==> not_fresh_at s2 z) /\
   (!z. dst = Var z ==> not_fresh_at s2 z)` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[expr_post_def] >>
  irule immutable_augassign_operator_mem >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`e`, `el`, `op`, `s3`, `x`, `y`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`v`, `t`] >> simp[] >> metis_tac[]
QED
