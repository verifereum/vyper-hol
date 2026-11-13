(*
 * Statement simulation: a condition and the jump on it (#637)
 *
 * A condition's fragment and its JNZ, as a counted outcome of the
 * condition's source action.  If, Raise and Assert themselves are in
 * stmtSimIfCounted, stmtSimRaise and stmtSimAssert.
 *
 * TOP-LEVEL:
 *   cond_jump_frag        — a condition and the jump on it
 *)

Theory stmtSimIf
Ancestors
  stmtSimProps stmtSimIfProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  gasOutcome gasSummary gasContext gasCount fragGasPath fragGasMode
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* ===== A condition and its JNZ ===== *)

(* A boolean condition lowered from sa to s1 and a JNZ on it right after,
   in a block that fn holds as finished, as a counted outcome of the
   condition's action at every reading: on a value, b, the path goes on
   through the JNZ to its target for b, from a state related at the
   source state after the condition, with the variables handed out
   before sa and the allocations kept; on an error it exits as expr_exit
   allows. *)
Theorem cond_jump_frag:
  !ctx func cx cenv e es sa op s1 s3 s4 lt lf s0.
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    expr_type e = BaseT BoolT /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op, s1) /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    gas_admissible (bind (eval_expr cx e) (read_result cx))
      (\r. !v. r = INL v ==> ?b. v = BoolV b) es /\
    s3.cs_current_bb = s1.cs_current_bb /\
    s3.cs_current_insts = s1.cs_current_insts /\
    emit_inst JNZ [op; Label lt; Label lf] [] s3 = ((), s4) /\
    lookup_block s4.cs_current_bb func.fn_blocks =
      SOME <| bb_label := s4.cs_current_bb;
              bb_instructions := s4.cs_current_insts |> /\
    fn_has_code sa s1 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (bind (eval_expr cx e) (read_result cx)) (es, s0)
      (\res ee t. ?b s.
         res = INL (BoolV b) /\ t = jump_to (if b then lt else lf) s /\
         stmt_state_rel ctx func cenv cx ee s /\ ~s.vs_halted /\
         (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                lookup_var x s = SOME w) /\
         (!aid bnd. FLOOKUP s0.vs_allocas aid = SOME bnd ==>
                    FLOOKUP s.vs_allocas aid = SOME bnd))
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "path"
  >- (qexists_tac `marks` >> disj1_tac >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Resume cond_jump_frag[path]:
  gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
   (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `?b. v = BoolV b` by
    (qpat_x_assum `gas_admissible _ (\r. _) _` mp_tac >>
     rewrite_tac[gas_admissible_def] >> disch_then drule >> simp[]) >>
  gvs[] >>
  `gas_marked_path F ctx func s0 (LENGTH marks) (OK t)` by
    fs[gas_marked_exec_def] >>
  `~t.vs_halted` by
    (fs[gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (drule_all if_condition_operand >> Cases_on `b` >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  drule emit_inst_extends >> strip_tac >>
  `fn_has_code s3 s4 func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  `gas_path ctx func t 0 (OK (jump_to (if b then lt else lf) t))` by
    (irule assert_jnz_zero_path >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> gvs[]) >>
  `gas_marked_path F ctx func s0 (LENGTH marks)
     (OK (jump_to (if b then lt else lf) t))` by
    (`LENGTH marks = LENGTH marks + 0` by simp[] >>
     pop_assum SUBST1_TAC >> irule gas_marked_path_then >>
     simp[gas_marked_path_def] >> metis_tac[gas_marked_path_def]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL (BoolV b)`, `es_end`,
                `OK (jump_to (if b then lt else lf) t)`] >>
  conj_tac >- fs[gas_marked_exec_def] >>
  disj1_tac >> simp[] >> qexists_tac `t` >> fs[expr_post_def]
QED

Finalise cond_jump_frag
