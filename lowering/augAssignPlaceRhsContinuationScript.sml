(* Counted forced-RHS execution with a memory-safe zero-observation suffix. *)
Theory augAssignPlaceRhsContinuation
Ancestors
  augAssignPlaceSuffixMemory exprSimMemDefs stmtSimForced
  gasOutcome gasSummary loweringPosts exprLowering
  bodyBinopFamiliesMemory bodyBinopFragMemory stmtSimAugAssignPlaceMemory
  vyperState exprSimWordArgs

Theorem aug_place_rhs_mem_continuation[local]:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v ee t. expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
           (INL v,ee)) ==>
     ?res ff r.
       (!tail. k v (ee with gas_obs := tail) = (res,ff with gas_obs := tail)) /\
       gas_marked_path T ctx func t 0 r /\
       ((?u. r = OK u /\ Q res (ff with gas_obs := []) u) \/
        (exit_result r /\ R res (ff with gas_obs := []) r))) /\
  (!ex ee r. expr_exit (INR ex : value + exception) r ==>
             R (INR ex) ee r) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `s0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  irule forced_then_outcome >> conj_tac >- simp[] >>
  qexists `\v ee t. expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  simp[]
QED

(* Concrete, observation-free operator/write suffix.  Write success and its
   source replay are established by the memory or storage branch. *)
Theorem aug_place_operator_write_path_mem[local]:
  bop <> In /\ bop <> NotIn /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst;op] s3 = ((),sf) /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE el
    [ty;expr_type e] cur rhs ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
  (!z. x = Var z ==> not_fresh_at s2 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  (!z. dst = Var z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at s2 z) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\
  stmt_state_rel ctx func cenv cx ee s /\ alloca_history func s /\
  s_entry.vs_alloca_next <= s.vs_alloca_next /\
  eval_operand x s = SOME (val_to_w256 cur) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type ty) /\
  (loc = LocMemory ==> w2n w + 32 <= s.vs_alloca_next) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ storage_place_region cx p /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    value_has_type dtv v /\ ?ff. write_place cx p v ee = (INL (),ff) /\
      !tail. write_place cx p v (ee with gas_obs := tail) =
        (INL (),ff with gas_obs := tail)) /\
  ~s.vs_halted /\ s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\ ~block_is_terminated sf /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z s = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) ==>
  ?res ff r.
    (!tail. bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx p) (ee with gas_obs := tail) =
        (res,ff with gas_obs := tail)) /\
    gas_marked_path T ctx func s 0 r /\
    ((?u. r = OK u /\ res = INL () /\
      stmt_post ctx func cx lctx cenv cenv sa sf s_entry
        res (ff with gas_obs := []) u /\ alloca_history func u /\
      s_entry.vs_alloca_next <= u.vs_alloca_next) \/
     (exit_result r /\ !tail. stmt_exit RetQ (ff with gas_obs := tail) res r))
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule stmtSimAugAssignTheory.bop_result_augassign >> simp[]) >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_val_mem_def, binop_frag_mem_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `x`, `y`, `op`, `s`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (gvs[] >>
      rename1 `eval_operand op t = SOME (val_to_w256 v)` >>
      drule_all aug_place_word_store_after_operator_mem >> strip_tac >>
      `gas_marked_path T ctx func s 0 (OK u)` by
        (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
      qexistsl_tac [`INL ()`, `ff`, `OK u`] >>
      conj_tac >- (Cases_on `evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        ptv bop cur rhs` >>
        gvs[vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
            vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
      simp[] >> disj1_tac >> irule aug_place_normal_post >>
      simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >> metis_tac[]) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
    ptv bop cur rhs`
  >- gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `_ = INR err` >>
  qexistsl_tac [`INR (Error err)`, `ee`, `r`] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  gen_tac >> simp[stmtSimDefsTheory.stmt_exit_def] >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type] >>
  gvs[]
QED

Theorem aug_place_rhs_operator_write_mem:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e s1 = (y,s2) /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst;op] s3 = ((),sf) /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ bop <> In /\ bop <> NotIn /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  (!z. dst = Var z ==> not_fresh_at s1 z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at s1 z) /\
  (!z. not_fresh_at s1 z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  (!l. x <> Label l /\ dst <> Label l) /\
  eval_operand x s0 = SOME (val_to_w256 cur) /\ eval_operand dst s0 = SOME w /\
  place_ptr_rel cenv cx s0 (PlaceR p) w (SOME loc) (Type ty) /\
  (loc = LocMemory ==> w2n w + 32 <= s0.vs_alloca_next) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  is_word_type (expr_type e) /\ IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ storage_place_region cx p /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  s_entry.vs_alloca_next <= s0.vs_alloca_next /\
  ~s0.vs_halted /\ s0.vs_current_bb = s1.cs_current_bb /\
  s0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~block_is_terminated sf /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z s0 = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP s0.vs_allocas aid = SOME b) /\
  (!rhs ee. ee.gas_obs = [] /\
     (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
           (INL rhs,ee)) ==>
     word_value rhs /\ expr_sim_inv cenv cx env ee /\
     binop_frag_val_mem ctx func cenv cx bop ty ty NONE el
       [ty;expr_type e] cur rhs ee /\
     expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
     (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
       value_has_type dtv v /\ ?ff. write_place cx p v ee = (INL (),ff) /\
         !tail. write_place cx p v (ee with gas_obs := tail) =
           (INL (),ff with gas_obs := tail))) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p))) (es,s0)
    (\res ff u. res = INL () /\
      stmt_post ctx func cx lctx cenv cenv sa sf s_entry res ff u /\
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
  `place_ptr_rel cenv cx t (PlaceR p) w (SOME loc) (Type ty)` by
    (Cases_on `p`
     >- fs[place_ptr_rel_def]
     >- (irule aug_place_memory_ptr_frame >> goal_assum (drule_at Any) >>
         gvs[expr_post_def] >> goal_assum (drule_at Any) >> simp[])
     >> fs[place_ptr_rel_def]) >>
  `loc = LocMemory ==> w2n w + 32 <= t.vs_alloca_next` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `!z. y = Var z ==> not_fresh_at s2 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `(!z. x = Var z ==> not_fresh_at s2 z) /\
   (!z. dst = Var z ==> not_fresh_at s2 z) /\
   (!z. not_fresh_at sa z ==> not_fresh_at s2 z)` by metis_tac[] >>
  `(!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
          lookup_var z t = SOME u) /\
   (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
            FLOOKUP t.vs_allocas aid = SOME b)` by
    (gvs[expr_post_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[expr_post_def] >>
  `s_entry.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  drule_all (Q.INST [`sa` |-> `sa`, `s_entry` |-> `s_entry`]
    aug_place_operator_write_path_mem) >> simp[]
QED
