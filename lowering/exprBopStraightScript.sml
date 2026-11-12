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
      qmatch_asmsub_rename_tac `vars_ext ss' target` >>
      `!H. valid_horizon cx st0 H es0.storage_trace ==>
           stmt_state_rel H ctx func cenv cx es0
             (target with vs_inst_idx := LENGTH sb.cs_current_insts)` by
        (rpt strip_tac >>
         qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
         drule_all straight_fresh_run_post >> simp[]) >>
      `writes_fresh sa (emitted_insts sa sb) /\
       sb.cs_current_bb = sa.cs_current_bb` by
        metis_tac[straight_fresh_def] >>
      qspecl_then [`emitted_insts sa sb`, `sa`, `s0`, `target`] mp_tac
        run_inst_seq_writes_fresh >>
      (impl_tac >- simp[]) >> strip_tac >>
      `eval_operand op target = SOME (val_to_w256 v)` by
        (fs[vars_ext_def] >>
         qpat_x_assum `target = ss' with vs_vars := _` SUBST1_TAC >>
         simp[eval_operand_vars_ext]) >>
      `eval_operand op
         (target with vs_inst_idx := LENGTH sb.cs_current_insts) =
       SOME (val_to_w256 v)` by
        (Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]) >>
      `target.vs_allocas = s0.vs_allocas /\ target.vs_memory = s0.vs_memory /\
       target.vs_halted = s0.vs_halted /\
       target.vs_current_bb = s0.vs_current_bb` by
        (qpat_x_assum `target = s0 with vs_vars := _`
           (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
      qpat_x_assum `target = s0 with vs_vars := _` kall_tac >>
      qexists_tac `OK (target with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
      simp[] >> simp[lookup_var_def] >> metis_tac[]) >>
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

