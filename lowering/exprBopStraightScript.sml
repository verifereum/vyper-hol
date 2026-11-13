(* Actual counted paths for straight-line binary operators. *)
Theory exprBopStraight
Ancestors
  exprBopSimDefs exprBopSimProps exprSimBopTyped
  exprSimProps
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragGasFresh fragGasMode fragGasSeq fragGasSeqAbort fragExec varsExt  freshWrites exprBopLowering loweringSlice
  localPtrsProps vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding venomExecSemantics venomInst venomState
  vyperValue integer integer_word int_bitwise words intBits vyperTyping
Libs
  pairLib

Theorem binop_frag_straight:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0.
    (!x y. straight_fresh (compile_binop bop x y ty bl el)) /\
    (expr_res_ok (bop_result cx ann bop tys v1 v2 es0) ==>
     (?v. bop_result cx ann bop tys v1 v2 es0 = INL v /\ word_value v /\
          !x y sa sb op ss.
            compile_binop bop x y ty bl el sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME (val_to_w256 v1) /\
            eval_operand y ss = SOME (val_to_w256 v2) ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                  eval_operand op ss' = SOME (val_to_w256 v)) \/
     (?m. bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError m)) /\
          !x y sa sb op ss.
            compile_binop bop x y ty bl el sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME (val_to_w256 v1) /\
            eval_operand y ss = SOME (val_to_w256 v2) ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss =
                    Abort Revert_abort ss')) ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> simp[binop_frag_def, binop_frag_words_def] >> rpt gen_tac >>
  strip_tac >>
  `straight_fresh (compile_binop bop x y ty bl el)` by simp[] >>
  qpat_x_assum `expr_res_ok _ ==> _` drule >> strip_tac
  >- (`eval_operand x (drop_fresh sa s0) = SOME (val_to_w256 v1) /\
       eval_operand y (drop_fresh sa s0) = SOME (val_to_w256 v2)` by
        simp[eval_operand_drop_fresh] >>
      qpat_x_assum `!x y sa sb op ss. _`
        (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      disch_then (qspec_then `drop_fresh sa s0` mp_tac) >>
      simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
      drule_all straight_fresh_clean_success_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      drule_all straight_fresh_run_post >> strip_tac >>
      qexists_tac `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
      simp[]) >>
  `eval_operand x (drop_fresh sa s0) = SOME (val_to_w256 v1) /\
   eval_operand y (drop_fresh sa s0) = SOME (val_to_w256 v2)` by
    simp[eval_operand_drop_fresh] >>
  qpat_x_assum `!x y sa sb op ss. _`
    (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `drop_fresh sa s0` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `Abort Revert_abort (t with vs_inst_idx := j)` >>
  simp[exit_result_def, expr_exit_def]
QED

