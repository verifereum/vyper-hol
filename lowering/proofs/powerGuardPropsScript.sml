(* Execution interfaces for the checks emitted by safe_pow. *)
Theory powerGuardProps
Ancestors
  powerRunProps exprLowering
  exprLoweringProps emitHelper emitHelperProps compileEnv venomExecSemantics
  venomState venomInst words integer_word integer list
Libs
  wordsLib

(* Forward operand observations through the fresh writes of a check. *)
fun forward_evals (asl, g) =
  let
    fun pres t =
      let val (vs,b) = strip_forall t
          val (a,_) = dest_imp b
      in length vs = 2 andalso
         fst (dest_const (fst (strip_comb (lhs a)))) = "eval_operand" end
      handle _ => false
    fun ev t = not (is_forall t) andalso
      fst (dest_const (fst (strip_comb (lhs t)))) = "eval_operand"
      handle _ => false
    fun forward p (asl,g) =
      EVERY (map (fn a =>
        TRY (fn goal => assume_tac (MATCH_MP (SPEC_ALL (ASSUME p)) (ASSUME a)) goal))
        (List.filter ev asl)) (asl,g)
  in EVERY (map forward (rev (List.filter pres asl))) (asl,g) end;

fun literal_second th =
  th |> SPEC_ALL |> Q.INST [`op2` |-> `Lit v2`]
     |> SIMP_RULE (srw_ss()) [eval_operand_lit];

fun check_step th =
  forward_evals >> drule_all th >> strip_tac >>
  TRY (imp_res_tac emit_op_extends >>
       drule_all run_inst_seq_chain >> strip_tac >>
       qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _`
         (fn eq => first_assum (fn th =>
           assume_tac (TRANS eq th))));

Theorem power_assert_exp_run:
  (do emit_void ASSERT [ok]; emit_op Exp [x;y] od) st = (op,st') /\
  eval_operand ok ss = SOME c /\ eval_operand x ss = SOME a /\
  eval_operand y ss = SOME b /\ fresh_vars_wrt st ss ==>
  (c <> 0w ==> ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
                      eval_operand op ss' = SOME (word_exp a b)) /\
  (c = 0w ==> ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> gvs[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> conj_tac >> strip_tac
  >- (drule_all emit_void_ASSERT_ok_full >> strip_tac >> gvs[] >>
      drule_all emit_op_Exp_correct >> strip_tac >>
      imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
      drule_all run_inst_seq_chain >> strip_tac >> gvs[]) >>
  gvs[] >> drule_all emit_void_ASSERT_revert >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all run_inst_seq_abort_extends >> gvs[]
QED

(* A prefix of pure checks supplies the final ASSERT condition. *)
Theorem power_check_exp_run:
  prefix st = (ok,st1) /\
  (do c <- prefix; emit_void ASSERT [c]; emit_op Exp [x;y] od) st = (op,st') /\
  run_inst_seq (emitted_insts st st1) ss = OK ss1 /\
  st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 /\
  inst_extends st1 st' /\
  fresh_vars_wrt st1 ss1 /\ eval_operand ok ss1 = SOME c /\
  eval_operand x ss1 = SOME a /\ eval_operand y ss1 = SOME b ==>
  (c <> 0w ==> ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
                      eval_operand op ss' = SOME (word_exp a b)) /\
  (c = 0w ==> ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >>
  `(do emit_void ASSERT [ok]; emit_op Exp [x;y] od) st1 = (op,st')`
    by gvs[comp_bind_def] >>
  drule_all power_assert_exp_run >> strip_tac >>
  fs[inst_extends_def] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  conj_tac >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem power_nonnegative_exp_run:
  (do negative <- emit_op SLT [y; Lit 0w];
      ok <- emit_op ISZERO [negative];
      emit_void ASSERT [ok]; emit_op Exp [x;y] od) st = (op,st') /\
  eval_operand x ss = SOME a /\ eval_operand y ss = SOME b /\
  fresh_vars_wrt st ss ==>
  (~(b < 0w) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (word_exp a b)) /\
  (b < 0w ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> gvs[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  check_step (literal_second emit_op_SLT_correct) >>
  check_step emit_op_ISZERO_correct >> forward_evals >>
  rename1 `emit_void ASSERT [ok] st2 = ((),st3)` >>
  rename1 `fresh_vars_wrt st2 ss2` >>
  `(do emit_void ASSERT [ok]; emit_op Exp [x;y] od) st2 = (op,st')`
    by simp[comp_bind_def, comp_ignore_bind_def] >>
  drule_all power_assert_exp_run >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `st'.cs_current_insts = st2.cs_current_insts ++ emitted_insts st2 st'`
    by (imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
        metis_tac[inst_extends_trans, inst_extends_def]) >>
  mp_tac (Q.SPECL [`st`, `st2`, `st'`, `ss`, `ss2`] run_inst_seq_chain) >>
  (impl_tac >- simp[]) >> strip_tac >>
  conj_tac >> strip_tac >> fs[bool_to_word_def] >> gvs[]
QED

Theorem power_signed_range_run:
  (do below <- emit_op SLT [x; Lit lo];
      ge <- emit_op ISZERO [below];
      above <- emit_op SGT [x; Lit hi];
      le <- emit_op ISZERO [above];
      ok <- emit_op AND [ge;le];
      emit_void ASSERT [ok]; emit_op Exp [x;y] od) st = (op,st') /\
  eval_operand x ss = SOME a /\ eval_operand y ss = SOME b /\
  fresh_vars_wrt st ss ==>
  (~(a < lo) /\ ~(a > hi) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (word_exp a b)) /\
  (a < lo \/ a > hi ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> gvs[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  check_step (literal_second emit_op_SLT_correct) >>
  check_step emit_op_ISZERO_correct >>
  check_step (literal_second emit_op_SGT_correct) >>
  check_step emit_op_ISZERO_correct >>
  check_step emit_op_AND_correct >> forward_evals >>
  rename1 `emit_void ASSERT [ok] st5 = ((),st6)` >>
  rename1 `fresh_vars_wrt st5 ss5` >>
  `(do emit_void ASSERT [ok]; emit_op Exp [x;y] od) st5 = (op,st')`
    by simp[comp_bind_def, comp_ignore_bind_def] >>
  drule_all power_assert_exp_run >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `st'.cs_current_insts = st5.cs_current_insts ++ emitted_insts st5 st'`
    by (imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
        metis_tac[inst_extends_trans, inst_extends_def]) >>
  mp_tac (Q.SPECL [`st`, `st5`, `st'`, `ss`, `ss5`] run_inst_seq_chain) >>
  (impl_tac >- simp[]) >> strip_tac >>
  conj_tac >> strip_tac >>
  fs[bool_to_word_def] >> gvs[]
QED
