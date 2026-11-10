(* Ordinary unary expression simulation composition. *)
Theory exprUnopStraight
Ancestors
  exprUnopSimDefs exprSimUnopProps
  fragGasFresh fragGasSeqAbort gasSummary
  exprSimProps
  exprSimDefs
  loweringPosts
  arithmetic list integer words integer_word byte
  fragExec varsExt  freshWrites
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  builtinSimple builtinProps arithmeticProps vyperArith
  compileEnv vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation valueEncoding venomExecSemantics venomInst venomState
  vyperTyping vyperTypeSystem
Libs
  intLib pairLib


Theorem unop_frag_straight:
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
    unop_frag ctx func cenv cx f w1 t res es0
Proof
  rpt gen_tac >> strip_tac >> simp[unop_frag_def] >> rpt gen_tac >>
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s0) = SOME w1` by
    metis_tac[eval_operand_drop_fresh] >>
  qpat_x_assum `!x. straight_fresh (f x)`
    (qspec_then `x` assume_tac) >>
  qpat_x_assum `expr_res_ok _ ==> _` drule >> strip_tac
  >- (qpat_x_assum `!x sa sb op ss. _`
        (qspecl_then [`x`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
      simp[] >> strip_tac >>
      drule_all straight_fresh_clean_success_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      drule_all straight_fresh_run_post >> strip_tac >>
      qmatch_asmsub_rename_tac `vars_ext ss' target` >>
      qexists_tac `OK (target with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
      simp[] >> simp[expr_val_rel_def] >> metis_tac[]) >>
  qpat_x_assum `!x sa sb op ss. _`
    (qspecl_then [`x`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_rename_tac
    `gas_marked_path F ctx func s0 0 (Abort Revert_abort endpoint)` >>
  qexists_tac `Abort Revert_abort endpoint` >>
  simp[exit_result_def, expr_exit_def]
QED
