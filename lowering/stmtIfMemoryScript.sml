(* Actual-source counted conditional statement simulation. *)
Theory stmtIfMemory
Ancestors
  exprSimMemDefs bodyMemoryDefs fragGasPathMem stmtSimIfCounted
  stmtSimDefs stmtSimProps stmtSimIfProps exprSimDefs exprSimProps loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasMode
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

Theorem compile_if_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty c ss1 ss2 es.
    expr_type c = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!gs b es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL (BoolV b), es1) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (If c ss1 ss2))
      (eval_stmt cx (If c ss1 ss2)) es
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (If c ss1 ss2) sa` >>
  rename1 `_ = (u, sm)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule_all compile_if_layout_mem >> strip_tac >>
  imp_res_tac new_block_props >>
  qpat_x_assum `eval_stmt _ _ _ = _`
    (strip_assume_tac o MATCH_MP eval_stmt_if_all_mem)
  >- (fs[] >>
      `expr_res_ok r1` by
        (gvs[] >>
         qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
         simp[bind_def] >> Cases_on `eval_expr cx c es` >>
         rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
         imp_res_tac read_result_no_control >>
         imp_res_tac (cj 1 eval_expr_no_control) >>
         gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
      gvs[] >>
      `!v. INR ex = INL v ==> ?b. v = BoolV b` by simp[] >>
      `INR ex <> (INR (Error (RuntimeError "convert empty bytes to signed")) : value + exception)` by simp[] >>
      drule_all cond_jump_frag_mem >> strip_tac >> fs[] >>
      disj2_tac >> qexists_tac `fuel` >> gvs[stmt_exit_def] >> disj1_tac >>
      metis_tac[expr_exit_INR_type])
  >- gvs[stmt_res_ok_def] >>
  gvs[] >>
  `expr_res_ok (INL (BoolV b)) /\
   (!v. (INL (BoolV b) : value + exception) = INL v ==> ?b. v = BoolV b)` by
    simp[expr_res_ok_def] >>
  `INL (BoolV b) <> (INR (Error (RuntimeError "convert empty bytes to signed")) : value + exception)` by simp[] >>
  drule_all cond_jump_frag_mem >> strip_tac >> fs[] >>
  gvs[] >> rename1 `stmt_state_rel ctx func cenv cx es1 sv` >>
  `!st l. sa.cs_next_var <= st.cs_next_var ==>
          ret_pc_ok cenv st (jump_to l sv) /\
          return_buf_frame d cenv st (jump_to l sv)` by
    (rpt gen_tac >> disch_tac >>
     simp[ret_pc_ok_jump_to, return_buf_frame_jump_to] >>
     conj_tac
     >- (irule ret_pc_ok_frame >> metis_tac[]) >>
     irule return_buf_frame_frame >> metis_tac[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!sa' op sb'. _` kall_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `lookup_block _ _ = _` kall_tac >>
  rpt (qpat_x_assum `_.cs_blocks = _` kall_tac) >>
  qabbrev_tac `si = if b then s6 else s9` >>
  qabbrev_tac `se = jump_to si.cs_current_bb sv` >>
  `(?s. stmt_lands lctx sb res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated (if b then s7 else s10)) /\
         stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s /\
         alloca_history func s /\
         (!x w. not_fresh_at si x /\ lookup_var x se = SOME w ==>
                lookup_var x s = SOME w) /\
         (!aid bnd. FLOOKUP se.vs_allocas aid = SOME bnd ==>
                    FLOOKUP s.vs_allocas aid = SOME bnd) /\
         return_buf_frame d cenv sb s /\ se.vs_alloca_next <= s.vs_alloca_next /\
         !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func se = r /\
                    (mem_safe_run fuel ctx func s ==> mem_safe_run fuel' ctx func se)) \/
    (?fuel r. run_from fuel ctx func se = r /\ exit_result r /\
              stmt_exit RetQ (es2 with scopes := rest) res r /\
              mem_safe_run fuel ctx func se)` by
    (Cases_on `b` >> (fs[Abbr `si`, Abbr `se`] >>
     irule (SRULE [] if_branch_frag_mem_join) >>
     simp[stmt_state_rel_jump_to, stmt_state_rel_push_scope] >>
     conj_tac >- simp[jump_to_def] >>
     conj_tac >- simp[jump_to_def] >>
     conj_tac >- simp[jump_to_def] >>
     conj_tac
     >- (strip_tac >>
         `?x11. new_block le s11 = (x11, sb)` by metis_tac[] >>
         imp_res_tac new_block_props >> fs[] >> metis_tac[]) >>
     conj_tac >- gvs[allocaHistoryTheory.alloca_history_def, jump_to_def] >>
     conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[]) >>
     qexists_tac `es1 with scopes := FEMPTY :: es1.scopes` >>
     goal_assum (drule_at Any) >>
     simp[stmt_state_rel_push_scope]))
  >- (disj1_tac >> qexistsl_tac [`s`, `cenv`] >>
      simp[cenv_top_ext_refl] >>
      conj_tac
      >- (strip_tac >>
          `?x11. new_block le s11 = (x11, sb)` by
            (Cases_on `b` >> fs[] >> metis_tac[]) >>
          imp_res_tac new_block_props >> fs[block_is_terminated_def]) >>
      conj_tac
      >- (rpt strip_tac >>
          `lookup_var x sv = SOME w` by metis_tac[] >>
          qpat_x_assum `!x w. not_fresh_at si x /\ _ ==> _` irule >>
          fs[Abbr `se`, lookup_var_def, jump_to_def] >>
          irule freshWritesTheory.not_fresh_at_mono >>
          qexists_tac `sa` >> Cases_on `b` >> fs[Abbr `si`]) >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!aid bnd. FLOOKUP se.vs_allocas aid = SOME bnd ==> _` irule >>
          simp[Abbr `se`, jump_to_def] >> metis_tac[]) >>
      conj_tac >- (fs[Abbr `se`, jump_to_def] >> decide_tac) >>
      rpt strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx func s = r /\ _ ==> _`
        (qspecl_then [`fuel`, `run_from fuel ctx func s`] mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >>
      fs[Abbr `se`, Abbr `si`] >>
      (impl_tac >- (Cases_on `b` >> gvs[])) >>
      strip_tac >> qexists_tac `fuel''` >> Cases_on `b` >> gvs[]) >>
  disj2_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
    (qspec_then `fuel` mp_tac) >>
  fs[Abbr `se`, Abbr `si`] >>
  (impl_tac >- (Cases_on `b` >> gvs[] >> metis_tac[exit_result_not_error])) >>
  strip_tac >> qexists_tac `fuel'` >> Cases_on `b` >> gvs[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag compile_if_stmt_frag_mem)
  in if null axioms andalso null (Thm.hyp compile_if_stmt_frag_mem) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "IF_MEMORY_KERNEL_AUDIT OK\n"
     else raise Fail "if memory inherited admission"
  end;
