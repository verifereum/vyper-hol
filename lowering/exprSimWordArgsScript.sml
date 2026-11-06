(*
 * Expression simulation: builtins on word operands (#636)
 *
 * A builtin whose operands are words lowers each operand with lower_value,
 * left to right (lower_word_args), then a straight-line fragment on the
 * operands.  compile_word_builtin_sim builds expr_sim of the whole from the
 * operands' expr_sim and word_builtin_frag, the fragment from the operands'
 * values to the source's builtin_result.  It is exprSimOps' compile_bop_sim
 * for any number of word operands.
 *
 * TOP-LEVEL:
 *   builtin_result, eval_expr_builtin_cases — the source side
 *   word_builtin_frag      — the builtin's fragment, from the operands'
 *                            values; word_builtin_frag_success and
 *                            word_builtin_frag_revert from the run facts
 *                            of straight-line code
 *   lower_word_args        — the operands' lowering
 *   wb_args_ready, wb_args_shape — what the composition needs of each
 *                            operand: its expr_sim, and that its lowering
 *                            only appends and hands out a variable or a
 *                            literal
 *   compile_word_builtin_sim — the composition
 *
 * Helper:
 *   eval_exprs_cons_cases, wb_args_cons_cases — the source's left-to-right
 *                            evaluation of the operands
 *   forced_eval_expr_preserves_scopes_dom — forced evaluation keeps scope domains
 *   lower_word_args_sim    — the operands' fragments, run in sequence
 *   wb_frame, wb_args_post, wb_args_exit — what holds after them
 *   expr_post_word_builtin — expr_post of the whole from the last
 *                            operand's and the fragment's facts
 *
 * Its operands and result are word_values and its fragment leaves memory
 * alone, so a bytesN or address operand or result, or a fragment that
 * writes a buffer, is out of its reach.
 *)

Theory exprSimWordArgs
Ancestors
  exprBopSimProps exprSimBopTyped
  exprSimSource
  exprSimProps
  exprSimDefs gasContext gasSummary gasOutcome gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath fragGasFresh
  loweringPosts
  list  exprSimHyps exprSimOps loweringSlice exprLowering
  exprLoweringProps vyperEvalExprPreservesScopesDom vyperInterpreter
  vyperState vyperContext vyperTyping compileEnv freshWrites fragExec varsExt
  venomExecSemantics venomState emitHelper emitHelperProps venomInst

(* Keep the account parameter: this boundary is valid for every non-Len
   builtin, not only the account-independent arithmetic cases. *)
Definition builtin_result_def:
  builtin_result cx acc ty bt ts vs =
    case evaluate_builtin cx acc ty bt ts vs of
      INL v => INL v
    | INR err => INR (Error err)
End

Theorem eval_expr_builtin_cases:
  !cx ann bt args es res es'.
    bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
    builtin_args_length_ok bt (LENGTH args) /\
    (do r <- eval_expr cx (Builtin ann bt args); read_result cx r od) es = (res, es') ==>
    (?exc. eval_exprs cx args es = (INR exc, es') /\ res = INR exc) \/
    ?vs. eval_exprs cx args es = (INL vs, es') /\
         res = builtin_result cx es'.accounts ann bt (MAP expr_type args) vs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx args es` >> rename1 `eval_exprs cx args es = (rr, es1)` >>
  Cases_on `rr` >> simp[get_accounts_def, bind_def, return_def,
                          lift_sum_def, builtin_result_def] >>
  rename1 `evaluate_builtin cx _ ann bt _ vs` >>
  Cases_on `evaluate_builtin cx es1.accounts ann bt (MAP expr_type args) vs` >>
  simp[bind_def, return_def, raise_def, read_result_def] >> rw[] >> gvs[]
QED

(* Argument evaluation forces each head before evaluating the tail. *)
Theorem eval_exprs_cons_cases:
  !cx e args es res es'.
    eval_exprs cx (e::args) es = (res, es') ==>
    (?exc. (do r <- eval_expr cx e; read_result cx r od) es = (INR exc, es') /\ res = INR exc) \/
    ?v es1 rr. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
      eval_exprs cx args es1 = (rr, es') /\
      res = (case rr of INL vs => INL (v::vs) | INR exc => INR exc)
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >>
  rename1 `eval_expr cx e es = (rr, es1)` >>
  Cases_on `rr` >> simp[] >>
  rename1 `read_result cx tv es1` >>
  Cases_on `read_result cx tv es1` >>
  rename1 `read_result cx tv es1 = (rv, es2)` >>
  Cases_on `rv` >> simp[] >>
  Cases_on `eval_exprs cx args es2` >>
  rename1 `eval_exprs cx args es2 = (rr, es3)` >>
  Cases_on `rr` >> simp[] >> rw[] >> gvs[]
QED

Theorem eval_exprs_cons_action:
  eval_exprs cx (e::args) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))
Proof
  pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx (e::args) x` >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[bind_def, return_def] >>
  Cases_on `rr` >> simp[]
QED

Theorem eval_expr_builtin_action:
  bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
  builtin_args_length_ok bt (LENGTH args) ==>
  bind (eval_expr cx (Builtin ann bt args)) (read_result cx) =
  bind (eval_exprs cx args)
    (\vs ee. (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs,ee))
Proof
  strip_tac >> pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bind (eval_expr cx (Builtin ann bt args)) (read_result cx) x` >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_builtin_cases) >>
  strip_tac >> gvs[bind_def]
QED

(* ===== A list-indexed word fragment interface ===== *)
Definition word_builtin_frag_def:
  word_builtin_frag ctx func cenv cx code res vs es0 <=>
    !sa sb xs op s0.
      code xs sa = (op, sb) /\ expr_res_ok res /\
      EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      stmt_state_rel ctx func cenv cx es0 s0 /\
      LIST_REL (\x v. eval_operand x s0 = SOME (val_to_w256 v)) xs vs /\
      ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?r. gas_marked_path F ctx func s0 0 r /\
        ((?s v. r = OK s /\ res = INL v /\ word_value v /\
                stmt_state_rel ctx func cenv cx es0 s /\
                eval_operand op s = SOME (val_to_w256 v) /\
                (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                       lookup_var z s = SOME w) /\
                (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                         FLOOKUP s.vs_allocas aid = SOME b) /\
                s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
                s.vs_current_bb = sb.cs_current_bb /\
                s.vs_inst_idx = LENGTH sb.cs_current_insts) \/
         (exit_result r /\ expr_exit res r))
End

Theorem word_operands_drop_fresh:
  !xs vs sa ss.
    EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs ==>
    (LIST_REL (\x v. eval_operand x (drop_fresh sa ss) = SOME (val_to_w256 v)) xs vs <=>
     LIST_REL (\x v. eval_operand x ss = SOME (val_to_w256 v)) xs vs)
Proof
  Induct >> Cases_on `vs` >> simp[] >> rpt strip_tac >>
  drule eval_operand_drop_fresh >> simp[]
QED

Theorem word_builtin_frag_success:
  !ctx func cenv cx code res vs es0 v.
    res = INL v /\ word_value v /\
    (!xs. straight_fresh (code xs)) /\
    (!xs sa sb op ss.
       code xs sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       LIST_REL (\x v. eval_operand x ss = SOME (val_to_w256 v)) xs vs ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
             eval_operand op ss' = SOME (val_to_w256 v)) ==>
    word_builtin_frag ctx func cenv cx code res vs es0
Proof
  rpt gen_tac >> strip_tac >>
  simp[word_builtin_frag_def] >> rpt gen_tac >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  `LIST_REL (\x v. eval_operand x (drop_fresh sa s0) = SOME (val_to_w256 v)) xs vs` by
    (drule word_operands_drop_fresh >> simp[]) >>
  qpat_x_assum `!xs sa sb op ss. _`
    (qspecl_then [`xs`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!xs. straight_fresh (code xs)` (qspec_then `xs` assume_tac) >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  qexists_tac `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  simp[]
QED

Theorem word_builtin_frag_revert:
  !ctx func cenv cx code res vs es0 msg.
    res = INR (Error (RuntimeError msg)) /\
    (!xs. straight_fresh (code xs)) /\
    (!xs sa sb op ss.
       code xs sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       LIST_REL (\x v. eval_operand x ss = SOME (val_to_w256 v)) xs vs ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss') ==>
    word_builtin_frag ctx func cenv cx code res vs es0
Proof
  rpt gen_tac >> strip_tac >>
  simp[word_builtin_frag_def] >> rpt gen_tac >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  `LIST_REL (\x v. eval_operand x (drop_fresh sa s0) = SOME (val_to_w256 v)) xs vs` by
    (drule word_operands_drop_fresh >> simp[]) >>
  qpat_x_assum `!xs sa sb op ss. _`
    (qspecl_then [`xs`, `sa`, `sb`, `op`, `drop_fresh sa s0`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!xs. straight_fresh (code xs)` (qspec_then `xs` assume_tac) >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_rename_tac
    `gas_marked_path F ctx func s0 0 (Abort Revert_abort endpoint)` >>
  qexists_tac `Abort Revert_abort endpoint` >>
  simp[exit_result_def, expr_exit_def]
QED

(* ===== Left-to-right word argument lowering ===== *)
Definition lower_word_args_def:
  (lower_word_args cenv arg_ty [] = comp_return []) /\
  (lower_word_args cenv arg_ty (e::es) =
     do x <- lower_value compile_expr cenv (arg_ty e) e;
        xs <- lower_word_args cenv arg_ty es;
        comp_return (x::xs)
     od)
End

Theorem lower_word_args_nil:
  !cenv arg_ty sa. lower_word_args cenv arg_ty [] sa = ([], sa)
Proof
  simp[lower_word_args_def, comp_return_def]
QED

Theorem lower_word_args_cons:
  !cenv arg_ty e es sa xs sb.
    lower_word_args cenv arg_ty (e::es) sa = (xs, sb) <=>
    ?x s1 ys. lower_value compile_expr cenv (arg_ty e) e sa = (x, s1) /\
      lower_word_args cenv arg_ty es s1 = (ys, sb) /\ xs = x::ys
Proof
  rpt gen_tac >> simp[lower_word_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[] >> metis_tac[]
QED

Theorem lower_word_args_shape:
  !args cenv arg_ty.
    (!e sa sb x. MEM e args /\
       lower_value compile_expr cenv (arg_ty e) e sa = (x, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. x = Var z ==> not_fresh_at sb z) /\ (!l. x <> Label l)) ==>
    !sa sb xs. lower_word_args cenv arg_ty args sa = (xs, sb) ==>
      cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
      sa.cs_next_id <= sb.cs_next_id /\ LENGTH xs = LENGTH args /\
      EVERY (\x. (!z. x = Var z ==> not_fresh_at sb z) /\
                 (!l. x <> Label l)) xs
Proof
  Induct >> simp[lower_word_args_nil, cs_extends_refl] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[lower_word_args_cons] >> strip_tac >> gvs[] >>
  first_assum (drule_at Any) >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`cenv`, `arg_ty`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  disch_then drule >> strip_tac >>
  simp[] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS,
                     not_fresh_at_mono]
QED

(* ===== Composable expression frames ===== *)

Theorem wb_frame_refl:
  !cenv es es' sa s. es'.scopes = es.scopes ==> wb_frame cenv es es' sa s s
Proof
  simp[wb_frame_def]
QED

(* A frame reads its end env only through its scopes. *)
Theorem wb_frame_gas_obs:
  !cenv es es' sa s0 s gs.
    wb_frame cenv es (es' with gas_obs := gs) sa s0 s <=>
    wb_frame cenv es es' sa s0 s
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def]
QED

Theorem wb_frame_vars:
  !cenv es es' sa s0 s x w.
    wb_frame cenv es es' sa s0 s /\ not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w
Proof
  simp[wb_frame_def]
QED

Theorem expr_post_frame:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s ==>
    wb_frame cenv es es' sa s0 s
Proof
  simp[expr_post_def, wb_frame_def] >> metis_tac[]
QED

Theorem expr_post_state:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s ==>
    stmt_state_rel ctx func cenv cx es' s
Proof
  simp[expr_post_def]
QED

Theorem expr_post_word_operand:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\ word_value v ==>
    eval_operand op s = SOME (val_to_w256 v)
Proof
  rpt strip_tac >> irule expr_val_rel_word >>
  gvs[expr_post_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem expr_post_word_intro:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    stmt_state_rel ctx func cenv cx es' s /\ is_word_type (expr_type e) /\ word_value v /\
    eval_operand op s = SOME (val_to_w256 v) /\ wb_frame cenv es es' sa s0 s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, wb_frame_def, expr_val_rel_def, expr_val_at_def,
       typed_val_to_w256_word_value] >> metis_tac[]
QED

Theorem wb_frame_readonly_tail:
  !cenv es es' sa s0 t s1 u.
    wb_frame cenv es es' sa s0 t /\ sa.cs_next_var <= s1.cs_next_var /\
    (!z w. not_fresh_at s1 z /\ lookup_var z t = SOME w ==> lookup_var z u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = t.vs_memory ==>
    wb_frame cenv es es' sa s0 u
Proof
  rpt strip_tac >>
  `locals_kept cenv es es' s0 t` by fs[wb_frame_def] >>
  `locals_kept cenv es es' s0 u` by metis_tac[locals_kept_mem_tail] >>
  fs[wb_frame_def] >> rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Theorem wb_frame_trans:
  !func cenv cx es s0 sa es1 es' s1 t u ctx.
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    wb_frame cenv es es1 sa s0 t /\ wb_frame cenv es1 es' s1 t u ==>
    wb_frame cenv es es' sa s0 u
Proof
  rpt gen_tac >> simp[wb_frame_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  reverse conj_tac
  >- (irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  disch_then irule >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
      qexists_tac `n` >> irule local_region_frame >>
      conj_tac >- (qexists_tac `func` >>
        gvs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl_tac [`sa`, `es1.scopes`, `t`] >> simp[]) 
  >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `sa.cs_next_id` >> simp[]) >>
  qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = _ ==> _` irule >> simp[]
QED

(* ===== Invariant-indexed source argument evaluation ===== *)
(* Each operand's facts at every state of the invariant; a later operand's
   only if the ones before it can evaluate, as evaluate_ind gives them. *)
Definition wb_args_ready_def:
  wb_args_ready ctx func cenv cx arg_ty Inv [] = T /\
  wb_args_ready ctx func cenv cx arg_ty Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim ctx func cenv cx (arg_ty e) e es /\
       is_word_type (expr_type e) /\
       IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
       (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
       (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
         word_value v /\ Inv es')) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      wb_args_ready ctx func cenv cx arg_ty Inv args))
End

Theorem wb_args_ready_head:
  !ctx func cenv cx arg_ty I e args es.
    wb_args_ready ctx func cenv cx arg_ty I (e::args) /\ I es ==>
      expr_sim ctx func cenv cx (arg_ty e) e es /\
      is_word_type (expr_type e) /\
      IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
      (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
      (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
        word_value v /\ I es')
Proof
  simp[wb_args_ready_def] >> metis_tac[]
QED

Theorem wb_args_ready_tail:
  !ctx func cenv cx arg_ty I e args es v es1.
    wb_args_ready ctx func cenv cx arg_ty I (e::args) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
    wb_args_ready ctx func cenv cx arg_ty I args
Proof
  simp[wb_args_ready_def] >> rpt strip_tac >> first_x_assum irule >>
  drule eval_expr_read_INL >> metis_tac[]
QED

Theorem eval_exprs_nil:
  !cx es. eval_exprs cx [] es = (INL [], es)
Proof
  simp[Once evaluate_def, return_def]
QED

Theorem wb_args_cons_cases:
  !ctx func cenv cx arg_ty I e args es res es'.
    wb_args_ready ctx func cenv cx arg_ty I (e::args) /\ I es /\
    eval_exprs cx (e::args) es = (res, es') ==>
    (?exc. (do r <- eval_expr cx e; read_result cx r od) es = (INR exc, es') /\ res = INR exc) \/
    ?v es1 rr. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
      word_value v /\ I es1 /\ eval_exprs cx args es1 = (rr, es') /\
      res = (case rr of INL vs => INL (v::vs) | INR exc => INR exc)
Proof
  rpt strip_tac >> drule_all wb_args_ready_head >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac
  >- metis_tac[]
  >> qpat_x_assum `!v es'. bind _ _ _ = (INL v, es') ==> _` drule >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Definition wb_args_exit_def:
  wb_args_exit rr =
    case rr of INL vs => (\r. F)
             | INR exc => expr_exit (INR exc : value + exception)
End

(* ===== Argument fragment execution ===== *)
Definition wb_args_post_def:
  wb_args_post ctx func cenv cx es sa s0 es' xs vs s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    LIST_REL (\x v. eval_operand x s = SOME (val_to_w256 v)) xs vs /\
    wb_frame cenv es es' sa s0 s
End

Definition wb_args_shape_def:
  wb_args_shape cenv arg_ty args <=>
    !e sa sb x. MEM e args /\
      lower_value compile_expr cenv (arg_ty e) e sa = (x, sb) ==>
      cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
      sa.cs_next_id <= sb.cs_next_id /\
      (!z. x = Var z ==> not_fresh_at sb z) /\ (!l. x <> Label l)
End

Theorem wb_args_shape_tail:
  !cenv arg_ty e args.
    wb_args_shape cenv arg_ty (e::args) ==> wb_args_shape cenv arg_ty args
Proof
  simp[wb_args_shape_def] >> metis_tac[]
QED

Theorem lower_word_args_shape_ready:
  !cenv arg_ty args sa xs sb.
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\ LENGTH xs = LENGTH args /\
    EVERY (\x. (!z. x = Var z ==> not_fresh_at sb z) /\ (!l. x <> Label l)) xs
Proof
  rpt gen_tac >> simp[wb_args_shape_def] >> strip_tac >>
  drule lower_word_args_shape >> disch_then drule >> simp[]
QED

Theorem expr_sim_apply:
  !ctx func cenv cx ty e es sa sb op s0.
    expr_sim ctx func cenv cx ty e es /\
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (bind (eval_expr cx e) (read_result cx)) (es, s0)
      (\res ee t. ?v. res = INL v /\
        expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  rewrite_tac[expr_sim_def] >> rpt strip_tac >>
  first_x_assum irule >> asm_rewrite_tac[]
QED

Theorem forced_eval_expr_preserves_scopes_dom:
  !cx e es res es'.
    (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==>
    MAP FDOM es.scopes = MAP FDOM es'.scopes
Proof
  rpt gen_tac >> simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule eval_expr_preserves_scopes_dom >> simp[]
QED

Theorem stmt_state_rel_gas_obs[simp]:
  stmt_state_rel ctx func cenv cx (es with gas_obs := gs) s =
  stmt_state_rel ctx func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_gas_obs, immutable_alloca_sep_def]
QED

Theorem wb_args_head_admissible:
  wb_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  `Inv (es with gas_obs := gs)` by metis_tac[] >>
  drule_all wb_args_ready_head >> strip_tac >>
  first_x_assum irule >> qexists_tac `ee` >> gvs[bind_def]
QED

Theorem wb_args_head_marked_facts:
  wb_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) mid r ==>
  word_value v /\ Inv (mid with gas_obs := []) /\
  wb_args_ready ctx func cenv cx arg_ty Inv args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  fs[] >> rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `Inv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) wb_args_ready_head) >> strip_tac >>
  `word_value v /\ Inv (mid with gas_obs := [])` by metis_tac[] >>
  `wb_args_ready ctx func cenv cx arg_ty Inv args` by
    (irule (CONV_RULE (DEPTH_CONV ETA_CONV) wb_args_ready_tail) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Theorem lower_word_args_nil_sim:
  !ctx func cenv cx es sa s0.
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_exprs cx []) (es, s0)
      (\rr ee t. ?vs. rr = INL vs /\
         wb_args_post ctx func cenv cx es sa s0 ee [] vs t /\
         t.vs_current_bb = sa.cs_current_bb /\
         t.vs_inst_idx = LENGTH sa.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  rpt strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_explicit_def,
       eval_exprs_nil, gas_marked_path_def] >>
  qexistsl_tac [`INL []`, `es`, `OK s0`] >>
  simp[cj 1 gas_path_rules, wb_args_post_def, wb_frame_refl]
QED

Theorem wb_args_post_cons:
  !func cenv cx e es sa s1 s0 es1 v x t es' xs vs u ctx.
    expr_post ctx func cenv cx e es sa s1 s0 es1 v x t /\
    wb_args_post ctx func cenv cx es1 s1 t es' xs vs u /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\ word_value v /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
    wb_args_post ctx func cenv cx es sa s0 es' (x::xs) (v::vs) u
Proof
  rpt strip_tac >>
  `eval_operand x t = SOME (val_to_w256 v)` by
    (drule_all expr_post_word_operand >> simp[]) >>
  `wb_frame cenv es es1 sa s0 t` by metis_tac[expr_post_frame] >>
  gvs[wb_args_post_def] >> conj_tac
  >- (irule eval_operand_frame >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[wb_frame_vars]) >>
  irule wb_frame_trans >> simp[] >> reverse conj_tac
  >- (qexistsl_tac [`es1`, `s1`, `t`] >> simp[]) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED

Theorem wb_frag_then:
  !ctx sa s1 P Q1.
    frag_exec ctx sa s1 P Q1 (\r. F) ==>
    !sb Q R. (!t. Q1 t ==> frag_exec ctx s1 sb (\s. s = t) Q R) /\
      cs_extends sa s1 /\ cs_extends s1 sb ==>
      frag_exec ctx sa sb P Q R
Proof
  rpt strip_tac >> irule frag_exec_seq_pointwise >>
  qexistsl_tac [`Q1`, `s1`] >> simp[] >>
  irule frag_exec_pre_exit >> goal_assum (drule_at Any) >> simp[]
QED

Theorem gas_marked_exec_cons_values:
  gas_marked_exec memory (ctx,func) (eval_exprs cx args)
    (es,s0) marks res mid r ==>
  gas_marked_exec memory (ctx,func)
    (bind (eval_exprs cx args) (\vs. return (v::vs)))
    (es,s0) marks (case res of INL vs => INL (v::vs) | INR exc => INR exc) mid r
Proof
  Cases_on `res` >> simp[gas_marked_exec_def, bind_def, return_def]
QED

Theorem eval_exprs_cons_ignore_action:
  ignore_bind (eval_exprs cx (e::args)) (return ()) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. ignore_bind (eval_exprs cx args) (return ()))
Proof
  rewrite_tac[eval_exprs_cons_action] >>
  qmatch_goalsub_abbrev_tac `bind head _` >>
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >> gen_tac >>
  Cases_on `head x` >> Cases_on `q` >> simp[] >>
  Cases_on `eval_exprs cx args r` >> Cases_on `q` >> simp[]
QED

Theorem wb_args_head_exempt_cert:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,endpoint) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_exprs cx (e::args)) (return ()))
    (es,s0) marks (err,ee) (leaf,endpoint)
Proof
  rewrite_tac[eval_exprs_cons_ignore_action] >> strip_tac >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem wb_args_tail_exempt_cert:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0) left (INL v) mid (OK t) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_exprs cx args) (return ()))
    (mid with gas_obs := [],t) right (err,ee) (leaf,endpoint) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_exprs cx (e::args)) (return ()))
    (es,s0) (left ++ right) (err,ee) (leaf,endpoint)
Proof
  rewrite_tac[eval_exprs_cons_ignore_action] >> strip_tac >>
  irule gas_exempt_cert_bind_value >> goal_assum (drule_at Any) >> simp[]
QED

Theorem lower_word_args_sim:
  !args ctx func cenv cx arg_ty Inv es sa xs sb s0.
    wb_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
    (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_exprs cx args) (es, s0)
      (\rr ee t. ?vs. rr = INL vs /\
         wb_args_post ctx func cenv cx es sa s0 ee xs vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  Induct
  >- (simp[lower_word_args_nil, eval_exprs_nil] >> rpt strip_tac >>
      irule lower_word_args_nil_sim >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `wb_args_ready ctx func cenv cx arg_ty Inv (e::args)` >>
  `wb_args_shape cenv arg_ty args` by metis_tac[wb_args_shape_tail] >>
  gvs[lower_word_args_cons] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    (qpat_x_assum `wb_args_shape _ _ (_::_)` mp_tac >>
     rewrite_tac[wb_args_shape_def] >>
     disch_then (qspec_then `e` mp_tac) >> simp[] >>
     disch_then drule >> simp[]) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  drule_all wb_args_ready_head >> strip_tac >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[wb_args_head_admissible] >>
  drule_all wb_args_ready_head >> strip_tac >>
  drule_all expr_sim_apply >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume lower_word_args_sim[head_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  drule_all wb_args_head_marked_facts >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `!ctx func cenv cx arg_ty Inv es sa xs sb s0. _`
    (drule_all_then mp_tac) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED
Resume lower_word_args_sim[head_exit]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume lower_word_args_sim[head_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any wb_args_head_exempt_cert >> goal_assum (drule_at Any)
QED
Resume lower_word_args_sim[tail_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK t'`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >> simp[] >>
  irule wb_args_post_cons >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume lower_word_args_sim[tail_exit]:
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume lower_word_args_sim[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Finalise lower_word_args_sim

Theorem expr_post_word_builtin:
  !func cenv cx es sa sm s0 es' xs vs t ann bt args sb v op u ctx.
    wb_args_post ctx func cenv cx es sa s0 es' xs vs t /\
    sa.cs_next_var <= sm.cs_next_var /\ is_word_type ann /\ word_value v /\
    stmt_state_rel ctx func cenv cx es' u /\ eval_operand op u = SOME (val_to_w256 v) /\
    (!z w. not_fresh_at sm z /\ lookup_var z t = SOME w ==> lookup_var z u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = t.vs_memory ==>
    expr_post ctx func cenv cx (Builtin ann bt args) es sa sb s0 es' v op u
Proof
  rpt strip_tac >> irule expr_post_word_intro >>
  simp[vyperASTTheory.expr_type_def] >> irule wb_frame_readonly_tail >>
  qexistsl_tac [`sm`, `t`] >> gvs[wb_args_post_def]
QED

Theorem word_builtin_continuation_summary:
  wb_args_post ctx func cenv cx es sa s0 (ee with gas_obs := []) xs vs t0 /\
  t0.vs_current_bb = sm.cs_current_bb /\
  t0.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t0.vs_halted /\
  word_builtin_frag ctx func cenv cx code
    (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs) vs
    (ee with gas_obs := []) /\
  expr_res_ok (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs) /\
  code xs sm = (op,sb) /\
  EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) xs /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ is_word_type ann /\
  sa.cs_next_var <= sm.cs_next_var ==>
  gas_summary_at F (ctx,func) []
    (\st. (builtin_result cx st.accounts ann bt (MAP expr_type args) vs,st))
    (ee with gas_obs := [],t0)
    (\res fin t. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin ann bt args) es sa sb s0 fin v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
   LIST_REL (\x v. eval_operand x t0 = SOME (val_to_w256 v)) xs vs` by
    gvs[wb_args_post_def] >>
  qpat_x_assum `word_builtin_frag _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [word_builtin_frag_def]) >>
  disch_then (qspecl_then [`sm`,`sb`,`xs`,`op`,`t0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (simp[gas_summary_at_def] >>
      qexistsl_tac [`builtin_result cx ee.accounts ann bt (MAP expr_type args) vs`,
                    `ee`, `r`] >> conj_tac
      >- (simp[gas_marked_exec_def] >> metis_tac[]) >>
      gvs[] >> irule expr_post_word_builtin >> simp[] >>
      qexistsl_tac [`sm`,`t0`,`vs`,`xs`] >> simp[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`builtin_result cx ee.accounts ann bt (MAP expr_type args) vs`,
                `ee`, `r`] >> simp[gas_marked_exec_def]
QED

Theorem word_builtin_marked_admissible:
  bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
  builtin_args_length_ok bt (LENGTH args) /\
  gas_admissible (bind (eval_expr cx (Builtin ann bt args)) (read_result cx))
    expr_res_ok es /\
  gas_marked_exec F (ctx,func) (eval_exprs cx args) (es,s0) marks (INL vs) ee r ==>
  expr_res_ok (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs)
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` assume_tac) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  asm_simp_tac (srw_ss()) [eval_expr_builtin_action, gas_admissible_def] >>
  disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
  gvs[bind_def]
QED

Theorem word_builtin_exempt_cert:
  bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
  builtin_args_length_ok bt (LENGTH args) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_exprs cx args) (return ()))
    (es,s0) marks out endpoint ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx (Builtin ann bt args)) (read_result cx))
      (return ())) (es,s0) marks out endpoint
Proof
  strip_tac >> asm_simp_tac (srw_ss()) [eval_expr_builtin_action] >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  `ignore_bind
     (bind (eval_exprs cx args)
       (\vs ee. (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs,ee)))
       (return ()) =
   bind (eval_exprs cx args)
     (\vs. ignore_bind
       (\ee. (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs,ee))
       (return ()))` by
    (qmatch_goalsub_abbrev_tac `bind a _` >>
     simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `a x` >> Cases_on `q` >> simp[] >>
     Cases_on `builtin_result cx r.accounts ann bt (MAP expr_type args) a'` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_values >> simp[]
QED

Theorem compile_word_builtin_sim:
  !ctx func cenv cx ty ann bt args arg_ty Inv es code.
    bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
    builtin_args_length_ok bt (LENGTH args) /\ is_word_type ann /\
    wb_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
    (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
    wb_args_shape cenv arg_ty args /\
    (!sa sb op. lower_value compile_expr cenv ty (Builtin ann bt args) sa = (op,sb) ==>
      ?xs sm. lower_word_args cenv arg_ty args sa = (xs,sm) /\ code xs sm = (op,sb)) /\
    (!xs sm sb op. code xs sm = (op,sb) ==> cs_extends sm sb) /\
    (!gs vs es'. eval_exprs cx args (es with gas_obs := gs) = (INL vs,es') ==>
      word_builtin_frag ctx func cenv cx code
        (builtin_result cx es'.accounts ann bt (MAP expr_type args) vs) vs es') ==>
    expr_sim ctx func cenv cx ty (Builtin ann bt args) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_sim_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!sa sb op. _ ==> _` drule >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sb` by metis_tac[] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) xs` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all lower_word_args_sim >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume compile_word_builtin_sim[normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  drule_all word_builtin_marked_admissible >> strip_tac >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `!gs vs es'. _` drule >> strip_tac >>
  fs[] >> drule_all word_builtin_continuation_summary >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qexists_tac `marks` >> disj1_tac >>
  asm_simp_tac (srw_ss()) [eval_expr_builtin_action, gas_summary_at_def] >>
  qexistsl_tac [`res`,`es_end'`,`r`] >>
  (conj_tac
   >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                |> REWRITE_RULE [APPEND_NIL]) >>
       qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _` (irule_at Any) >>
       gvs[]) >> gvs[])
QED
Resume compile_word_builtin_sim[exit]:
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  asm_simp_tac (srw_ss()) [eval_expr_builtin_action, gas_summary_at_def] >>
  qexistsl_tac [`INR y`,`es_end`,`r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume compile_word_builtin_sim[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any word_builtin_exempt_cert >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise compile_word_builtin_sim
