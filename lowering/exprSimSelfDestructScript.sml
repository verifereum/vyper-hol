(*
 * selfdestruct(to) simulates for any operand that simulates.
 *
 * The lowering evaluates the address operand with lower_value, then emits
 * one SELFDESTRUCT.  The source evaluates the operand, transfers the
 * running account's balance to it and raises HaltException; Venom's
 * SELFDESTRUCT makes the same moves and halts with empty returndata, so the
 * two halts are halt-related.  When the recipient's balance would
 * overflow, the source raises a RuntimeError that the target does not:
 * that run is an exempt origin.  An operand exit is the expression's exit.
 *)

Theory exprSimSelfDestruct
Ancestors
  selfdestructHalt gasExemptOrigin
  exprSimSource exprSimHypsDefs exprSimDefs exprSimSend exprSimAccounts
  loweringPosts gasContext gasSummary gasOutcome gasSummaryCompose
  gasExemptCert gasNormalPrefix fragGasMode fragGasPath fragGasSeq gasCount
  fragExec exprLowering exprLoweringProps exprOperandVar emitHelper
  emitHelperProps builtinSystem compileEnv loweringStateRelDefs
  vyperAST vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperTypeCallGraph allocLimits venomExecSemantics venomExecProps venomInst
  venomState venomInstProofs list rich_list arithmetic finite_map
Libs
  pairLib

(* ===== Source ===== *)

Theorem expr_body_pre_selfdestruct_arg:
  !cenv cx env ann args dflt e es es'.
    expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM]
  >~ [`well_typed_expr _ _`] >- metis_tac[well_typed_exprs_member]
  >~ [`byte_widths_expr _`] >- metis_tac[byte_widths_exprs_mem]
  >~ [`alloc_limits_expr _ _`] >- metis_tac[alloc_limits_exprs_mem]
  >~ [`call_evaluation_safe _ _`]
  >- metis_tac[call_evaluation_safe_exprs_mem]
  >~ [`EVERY _ (int_calls_expr _)`]
  >- metis_tac[int_calls_exprs_every_mem] >>
  metis_tac[]
QED

Theorem selfdestruct_pre_arg:
  !cenv cx env ann args dflt es.
    expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    ?e. args = [e] /\ expr_type e = BaseT AddressT /\
        expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `?e. args = [e] /\ expr_type e = BaseT AddressT` by
    (gvs[expr_body_pre_def, well_typed_expr_def, LENGTH_EQ_NUM_compute]) >>
  gvs[] >> irule expr_body_pre_selfdestruct_arg >>
  gvs[expr_body_pre_def] >> metis_tac[MEM]
QED

Theorem address_dest_word:
  !v a. dest_AddressV v = SOME a ==>
        a = w2w (typed_val_to_w256 (BaseTV AddressT) v)
Proof
  Cases >> rw[dest_AddressV_def] >> simp[address_word_w2w]
QED

(* ===== Compile ===== *)

Theorem compile_expr_selfdestruct_arg:
  !cenv ty ann e dflt st.
    compile_expr cenv ty (Call ann SelfDestructTarget [e] dflt) st =
    let (to_op, st1) = lower_value compile_expr cenv (BaseT AddressT) e st in
    let (_, st2) = compile_selfdestruct to_op st1 in
    (StackValue ann (Lit 0w), st2)
Proof
  simp[compile_expr_call, compile_call_def]
QED

Theorem selfdestruct_compile:
  !cenv ty ann e dflt sa vv sb.
    compile_expr cenv ty (Call ann SelfDestructTarget [e] dflt) sa = (vv,sb) ==>
    ?to_op sm.
      lower_value compile_expr cenv (BaseT AddressT) e sa = (to_op,sm) /\
      compile_selfdestruct to_op sm = ((),sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_selfdestruct_arg] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `compile_selfdestruct to_op st1 = (u,_)` >> Cases_on `u` >> simp[]
QED

Theorem selfdestruct_tail_layout:
  !to_op sa u sb.
    compile_selfdestruct to_op sa = (u,sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id SELFDESTRUCT [to_op] []]
Proof
  simp[compile_selfdestruct_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def,
       same_blocks_def, APPEND_ASSOC]
QED

Theorem selfdestruct_extends:
  !to_op sa u sb.
    compile_selfdestruct to_op sa = (u,sb) ==> cs_extends sa sb
Proof
  rpt strip_tac >> drule selfdestruct_tail_layout >> strip_tac >>
  simp[cs_extends_def] >> qexists_tac `[]` >>
  gvs[same_blocks_def, IS_PREFIX_APPEND]
QED

(* ===== Target tail ===== *)

(* The one SELFDESTRUCT, from a state halt-related to the source's, halts
   in a state halt-related to the source's halt; it reads no GAS. *)
Theorem selfdestruct_tail_path:
  !ctx func cx vs to_op sm u sb t w.
    compile_selfdestruct to_op sm = (u,sb) /\ fn_has_code sm sb func /\
    eval_operand to_op t = SOME w /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    halt_rel cx vs t /\ t.vs_call_ctx.cc_address = cx.txn.target /\
    t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
    ~t.vs_call_ctx.cc_static ==>
    ?s'. gas_path ctx func t 0 (Halt s') /\ s'.vs_returndata = [] /\
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
  `gas_path_edge ctx func t 0 (Halt s')` by
    (rewrite_tac[gas_path_edge_def] >> simp[exit_result_def] >>
     qexists_tac `0` >> simp[exit_result_def] >> gvs[mk_inst_def]) >>
  irule (cj 3 gas_path_rules) >> simp[exit_result_def]
QED

(* ===== Composition ===== *)

Theorem ignore_bind_bind_unit[local]:
  ignore_bind (vyperState$bind a k) (return ()) =
  vyperState$bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[FUN_EQ_THM, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def] >> gen_tac >>
  Cases_on `a x` >> Cases_on `q` >> simp[]
QED

Theorem selfdestruct_vv_sim:
  !ctx func cenv cx ty ann e dflt es.
    expr_type e = BaseT AddressT /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    expr_vv_sim ctx func cenv cx ty (Call ann SelfDestructTarget [e] dflt) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
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
  qpat_x_assum `expr_sim _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
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
          drule_all selfdestruct_tail_path >>
          disch_then (qspec_then `ctx` strip_assume_tac) >>
          `!tail. selfdestruct_tail cx v (es_end with gas_obs := tail) =
                  (INR HaltException,
                   selfdestruct_final cx a es_end with gas_obs := tail)` by
            (gen_tac >>
             qspecl_then [`cx`, `v`, `a`, `es_end with gas_obs := tail`]
               mp_tac selfdestruct_tail_halt >>
             impl_tac
             >- (simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
             simp_tac (srw_ss()) []) >>
          `gas_marked_exec F (ctx,func)
             (vyperState$bind
                (vyperState$bind (eval_expr cx e) (read_result cx))
                (selfdestruct_tail cx))
             (es,s0) marks (INR HaltException)
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
          qpat_assum `gas_marked_exec F _ (vyperState$bind (vyperState$bind _ _) _) _ _ (INR _) _ _`
            (fn th => rewrite_tac[th]) >>
          simp[exit_result_def, expr_exit_def, halt_exit_def]) >>
      (* the operand exits *)
      Cases_on `res` >> gvs[] >>
      qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_selfdestruct_action] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_selfdestruct_action, ignore_bind_bind_unit] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem selfdestruct_expr_vv_ok:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann SelfDestructTarget args dflt)) ==>
    expr_vv_ok cenv (Call ann SelfDestructTarget args dflt)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es /\
   int_calls_expr (Call ann SelfDestructTarget args dflt) = []` by
    metis_tac[expr_sim_pre_body] >>
  drule selfdestruct_pre_arg >> strip_tac >> gvs[] >>
  irule selfdestruct_vv_sim >> simp[] >>
  `expr_sim_pre cenv cx env e es` by
    gvs[expr_sim_pre_body, int_calls_expr_def] >>
  gvs[expr_sim_below_def] >>
  first_x_assum (qspec_then `e` mp_tac) >>
  simp[expr_size_def, expr_ok_def, expr_sim_ok_def] >> metis_tac[]
QED
