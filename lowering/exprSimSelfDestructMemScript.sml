(*
 * selfdestruct(to) in the memory tower: the base proof with memory-checked
 * paths.  The one SELFDESTRUCT reads and writes no memory, so its edge
 * passes the memory check; the operand's run carries the alloca facts the
 * exempt overflow origin needs.
 *)

Theory exprSimSelfDestructMem
Ancestors
  exprSimSelfDestruct exprSimAbortMemory exprSimMemDefs
  selfdestructHalt gasExemptOrigin
  exprSimSource exprSimHypsDefs exprSimDefs exprSimSend exprSimAccounts
  loweringPosts gasContext gasSummary gasOutcome gasSummaryCompose
  gasExemptCert gasNormalPrefix fragGasMode fragGasPath fragGasPathMem
  instMemFrontier memSafeRun fragGasSeq gasCount
  fragExec exprLowering exprLoweringProps exprOperandVar emitHelper
  emitHelperProps builtinSystem compileEnv loweringStateRelDefs
  vyperAST vyperInterpreter vyperState vyperValue vyperTypeSystem
  venomExecSemantics venomExecProps venomInst
  venomState venomInstProofs list rich_list arithmetic finite_map
Libs
  pairLib

Theorem selfdestruct_tail_path_mem:
  !ctx func cx vs to_op sm u sb t w.
    compile_selfdestruct to_op sm = (u,sb) /\ fn_has_code sm sb func /\
    eval_operand to_op t = SOME w /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    halt_rel cx vs t /\ t.vs_call_ctx.cc_address = cx.txn.target /\
    t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
    ~t.vs_call_ctx.cc_static ==>
    ?s'. gas_path_mem ctx func t 0 (Halt s') /\ s'.vs_returndata = [] /\
         halt_rel cx (selfdestruct_final cx (w2w w) vs) s'
Proof
  rpt strip_tac >> drule selfdestruct_tail_layout >> strip_tac >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
        !i. i < LENGTH [mk_inst sm.cs_next_id SELFDESTRUCT [to_op] []] ==>
            get_instruction bb (LENGTH sm.cs_current_insts + i) =
            SOME (EL i [mk_inst sm.cs_next_id SELFDESTRUCT [to_op] []])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >>
     gvs[same_blocks_def]) >>
  `get_instruction bb (LENGTH sm.cs_current_insts) =
     SOME (mk_inst sm.cs_next_id SELFDESTRUCT [to_op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all step_selfdestruct_halt_rel >>
  disch_then (qspec_then `sm.cs_next_id` strip_assume_tac) >>
  qexists_tac `s'` >> simp[] >>
  `step_inst 0 ctx (mk_inst sm.cs_next_id SELFDESTRUCT [to_op] []) t =
     Halt s'` by simp[step_inst_non_invoke, mk_inst_def] >>
  `gas_count_step 0 ctx (mk_inst sm.cs_next_id SELFDESTRUCT [to_op] []) t = 0`
    by simp[gas_count_step_def, mk_inst_def] >>
  `mem_safe_step 0 ctx (mk_inst sm.cs_next_id SELFDESTRUCT [to_op] []) t` by
    simp[mem_safe_step_non_invoke, mk_inst_def, below_frontier_no_ranges] >>
  `gas_path_mem_edge ctx func t 0 (Halt s')` by
    (rewrite_tac[gas_path_mem_edge_def] >> simp[exit_result_def] >>
     qexists_tac `0` >> simp[exit_result_def] >> gvs[mk_inst_def]) >>
  irule (cj 3 gas_path_mem_rules) >> simp[exit_result_def]
QED

Theorem ignore_bind_bind_unit[local]:
  ignore_bind (vyperState$bind a k) (return ()) =
  vyperState$bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[FUN_EQ_THM, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def] >> gen_tac >>
  Cases_on `a x` >> Cases_on `q` >> simp[]
QED

Theorem selfdestruct_vv_sim_mem:
  !ctx func cenv cx ty ann e dflt es.
    expr_type e = BaseT AddressT /\
    expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Call ann SelfDestructTarget [e] dflt) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule selfdestruct_compile >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[selfdestruct_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx))
     expr_res_ok es` by
    (rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
     qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `INR y`, `ee`] mp_tac) >>
     simp[eval_selfdestruct_action] >>
     qpat_x_assum `vyperState$bind _ _ _ = _`
       (fn th => simp[Once vyperStateTheory.bind_def, th]) >>
     simp[expr_vv_res_ok_def, expr_res_ok_def]) >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx))
     (\r. !v. r = INL v ==> ?a. dest_AddressV v = SOME a) es` by
    (rw[gas_admissible_def] >> Cases_on `dest_AddressV v` >> simp[] >>
     qpat_x_assum `gas_admissible (eval_expr _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then
       [`gs`, `INR (Error (TypeError "selfdestruct target"))`, `ee`] mp_tac) >>
     simp[eval_selfdestruct_action] >>
     qpat_x_assum `vyperState$bind _ _ _ = _`
       (fn th => simp[Once vyperStateTheory.bind_def, th]) >>
     simp[selfdestruct_tail_def, vyperStateTheory.lift_option_type_def,
          vyperStateTheory.raise_def, vyperStateTheory.bind_def,
          expr_vv_res_ok_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `to_op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- ((* the operand is an address *)
          `?a. dest_AddressV v = SOME a` by
            (qpat_x_assum `gas_admissible (vyperState$bind _ _) (\r. _) _`
               (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
             qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             metis_tac[]) >>
          `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t /\
           ?w. eval_operand to_op t = SOME w /\
               w = typed_val_to_w256 (BaseTV AddressT) v` by
            (gvs[expr_post_def, expr_val_rel_def, evaluate_type_def,
                 is_word_type_def] >>
             metis_tac[]) >>
          `a = w2w w` by metis_tac[address_dest_word] >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec,
                      gas_path_normal] >>
          Cases_on `selfdestruct_overflows cx a es_end.accounts`
          >- ((* exempt: the recipient's balance would overflow *)
              qexists_tac `marks` >> disj2_tac >>
              qexistsl_tac [`RuntimeError "transfer_value recipient overflow"`,
                            `es_end`, `func`, `t`] >>
              irule gas_exempt_cert_origin >>
              simp[gas_exempt_origin_def] >>
              qexistsl_tac [`cenv`, `cx`, `ty`, `ann`, `e`, `dflt`, `sa`,
                            `sb`, `sm`, `vv`, `to_op`, `v`, `a`] >>
              fs[gas_value_prefix_def]) >>
          (* the halt *)
          `state_rel func cenv cx (es_end with gas_obs := []) t` by
            fs[stmt_state_rel_def, state_rel_gas_obs] >>
          `halt_rel cx (es_end with gas_obs := []) t` by
            metis_tac[state_rel_halt_rel] >>
          `t.vs_call_ctx.cc_address = cx.txn.target /\
           t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
           ~t.vs_call_ctx.cc_static` by
            fs[state_rel_def, call_ctx_rel_def] >>
          drule_all selfdestruct_tail_path_mem >>
          disch_then (qspec_then `ctx` strip_assume_tac) >>
          `!tail. selfdestruct_tail cx v (es_end with gas_obs := tail) =
                  (INR HaltException : eval_result + exception,
                   selfdestruct_final cx a es_end with gas_obs := tail)` by
            (gen_tac >>
             qspecl_then [`cx`, `v`, `a`, `es_end with gas_obs := tail`]
               mp_tac selfdestruct_tail_halt >>
             impl_tac
             >- (simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
             simp_tac (srw_ss()) []) >>
          `gas_marked_exec T (ctx,func)
             (vyperState$bind
                (vyperState$bind (eval_expr cx e) (read_result cx))
                (selfdestruct_tail cx))
             (es,s0) marks (INR HaltException : eval_result + exception)
             (selfdestruct_final cx a es_end) (Halt s')` by
            (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                    |> REWRITE_RULE [APPEND_NIL]) >>
             qexistsl_tac [`es_end`, `t`, `v`] >> simp[] >>
             gvs[gas_marked_exec_def, gas_marked_path_def,
                 gas_explicit_def]) >>
          qexists_tac `marks` >> disj1_tac >>
          rewrite_tac[eval_selfdestruct_action] >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INR HaltException`,
                        `selfdestruct_final cx a es_end`, `Halt s'`] >>
          qpat_assum `gas_marked_exec T _ (vyperState$bind (vyperState$bind _ _) _) _ _ (INR _) _ _`
            (fn th => rewrite_tac[th]) >>
          gvs[exit_result_def, expr_exit_def, halt_exit_def]) >>
      (* the operand exits *)
      Cases_on `res` >> gvs[] >>
      qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_selfdestruct_action] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_selfdestruct_action, ignore_bind_bind_unit] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem eval_selfdestruct_raises:
  !cx ann e dflt st v st'.
    eval_expr cx (Call ann SelfDestructTarget [e] dflt) st <> (INL v, st')
Proof
  rpt gen_tac >> rewrite_tac[eval_selfdestruct_action] >> CCONTR_TAC >>
  gvs[vyperStateTheory.bind_def, AllCaseEqs()] >>
  qpat_x_assum `selfdestruct_tail _ _ _ = _` mp_tac >>
  qmatch_goalsub_rename_tac `selfdestruct_tail _ xx ss` >>
  qspecl_then [`cx`, `xx`, `ss`] strip_assume_tac selfdestruct_tail_raises >>
  simp[]
QED
