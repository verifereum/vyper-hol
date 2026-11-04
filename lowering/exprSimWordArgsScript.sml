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
 *   wb_args_cons_cases — the source's left-to-right operand evaluation,
 *                        using exprSimHyps' eval_exprs_cons_cases
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
  list exprSim exprSimHyps exprSimOps exprSimUnop loweringSlice exprLowering
  exprLoweringProps vyperEvalExprPreservesScopesDom vyperInterpreter
  vyperState vyperContext vyperTyping compileEnv freshWrites fragExec varsExt
  venomExecSemantics venomState emitHelper emitHelperProps venomInst

(* Keep the account parameter for account-dependent builtins.  Len and
   membership have dedicated interpreter paths rather than this boundary. *)
Definition builtin_result_def:
  builtin_result cx acc ty bt ts vs =
    case evaluate_builtin cx acc ty bt ts vs of
      INL v => INL v
    | INR err => INR (Error err)
End

Theorem eval_expr_builtin_cases:
  !cx ann bt args es res es'.
    bt <> Len /\ bt <> Env MsgGas /\ bt <> Bop In /\ bt <> Bop NotIn /\
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

(* ===== A list-indexed word fragment interface ===== *)
Definition word_builtin_frag_def:
  word_builtin_frag ctx func cenv cx code res vs es0 <=>
    !sa sb xs op s0.
      code xs sa = (op, sb) /\ expr_res_ok res /\
      EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb
        (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es0 s /\
             LIST_REL (\x v. eval_operand x s = SOME (val_to_w256 v)) xs vs)
        (\s. ?v. res = INL v /\ word_value v /\
                 stmt_state_rel ctx func cenv cx es0 s /\
                 eval_operand op s = SOME (val_to_w256 v) /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory)
        (expr_exit res)
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
  ho_match_mp_tac frag_exec_straight_fresh >>
  qexistsl_tac [`code xs`, `\a. F`] >>
  simp[word_operands_drop_fresh] >> rpt strip_tac >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> qexists_tac `xs` >> simp[]
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
  ho_match_mp_tac
    (INST_TYPE [``:'a`` |-> ``:operand``] frag_exec_straight_fresh_abort) >>
  qexistsl_tac [`code xs`, `op`, `\a. a = Revert_abort`] >>
  simp[word_operands_drop_fresh, expr_exit_def] >> rpt strip_tac >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> qexistsl_tac [`op`, `xs`] >> simp[]
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

Theorem compile_multi_exprs_lower_word_args:
  !args cenv. compile_multi_exprs compile_expr cenv args =
    lower_word_args cenv expr_type args
Proof
  Induct >> simp[compile_multi_exprs_def, lower_word_args_def]
QED

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

Theorem lower_value_bop_in_literal:
  !cenv ty bop e1 et bd elems sa op sb.
    (bop = In \/ bop = NotIn) /\ expr_type e1 = et /\
    lower_value compile_expr cenv ty
      (Builtin (BaseT BoolT) (Bop bop)
        [e1; Builtin (ArrayT et bd) (MakeArray (SOME et) bd) elems]) sa = (op,sb) ==>
    ?needle ops sm.
      lower_word_args cenv expr_type (e1::elems) sa = (needle::ops,sm) /\
      (if bop = In then compile_list_membership_in needle ops
       else compile_list_membership_notin needle ops) sm = (op,sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, exprBopLoweringTheory.compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, exprBopLoweringTheory.lower_value_child_call] >>
  simp[vyperASTTheory.expr_type_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `compile_multi_exprs (expr_child_callback bound compile_expr) cenv elems` >>
  `compile_multi_exprs (expr_child_callback bound compile_expr) cenv elems =
   compile_multi_exprs compile_expr cenv elems` by
    (irule compile_multi_exprs_callback_cong >> rpt strip_tac >>
     simp[FUN_EQ_THM, exprCallBoundsTheory.expr_child_callback_def] >>
     drule exprCallBoundsTheory.expr_list_member_bound >>
     simp[Abbr `bound`]) >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >>
  simp[exprBopLoweringTheory.as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  simp[lower_word_args_cons, GSYM compile_multi_exprs_lower_word_args] >>
  metis_tac[]
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
Definition wb_frame_def:
  wb_frame cenv es sa s0 s <=>
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es s0 s
End

Theorem wb_frame_refl:
  !cenv es sa s. wb_frame cenv es sa s s
Proof
  simp[wb_frame_def]
QED

Theorem wb_frame_vars:
  !cenv es sa s0 s x w.
    wb_frame cenv es sa s0 s /\ not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w
Proof
  simp[wb_frame_def]
QED

Theorem expr_post_frame:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s ==>
    wb_frame cenv es sa s0 s
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
    eval_operand op s = SOME (val_to_w256 v) /\ wb_frame cenv es sa s0 s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, wb_frame_def, expr_val_rel_def, expr_val_at_def,
       typed_val_to_w256_word_value] >> metis_tac[]
QED

Theorem wb_frame_readonly_tail:
  !cenv es sa s0 t s1 u.
    wb_frame cenv es sa s0 t /\ sa.cs_next_var <= s1.cs_next_var /\
    (!z w. not_fresh_at s1 z /\ lookup_var z t = SOME w ==> lookup_var z u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = t.vs_memory ==>
    wb_frame cenv es sa s0 u
Proof
  rpt strip_tac >>
  `locals_kept cenv es s0 t` by fs[wb_frame_def] >>
  `locals_kept cenv es s0 u` by metis_tac[locals_kept_mem_tail] >>
  fs[wb_frame_def] >> rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Theorem wb_frame_trans:
  !func cenv cx es s0 sa es1 s1 t u ctx.
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    wb_frame cenv es sa s0 t /\ wb_frame cenv es1 s1 t u ==>
    wb_frame cenv es sa s0 u
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
    wb_frame cenv es sa s0 s
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
  !ctx func cenv cx ty e es sa sb op res es' s0.
    expr_sim ctx func cenv cx ty e es /\
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (res, es') /\ expr_res_ok res /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?v. res = INL v /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op s)
      (expr_exit res)
Proof
  simp[expr_sim_def]
QED

Theorem lower_word_args_nil_sim:
  !ctx func cenv cx es sa s0.
    frag_exec ctx sa sa (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. wb_args_post ctx func cenv cx es sa s0 es [] [] s)
      (wb_args_exit (INL []))
Proof
  rpt gen_tac >> irule frag_exec_refl >>
  simp[wb_args_post_def, wb_frame_refl] >> metis_tac[]
QED

Theorem encoded_args_post_cons:
  !func cenv cx e es sa s1 s0 es1 v x t es' xs vs u ctx W.
    expr_post ctx func cenv cx e es sa s1 s0 es1 v x t /\
    stmt_state_rel ctx func cenv cx es' u /\
    LIST_REL (\x v. eval_operand x u = SOME (W v)) xs vs /\
    wb_frame cenv es1 s1 t u /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    eval_operand x t = SOME (W v) /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
    stmt_state_rel ctx func cenv cx es' u /\
    LIST_REL (\x v. eval_operand x u = SOME (W v)) (x::xs) (v::vs) /\
    wb_frame cenv es sa s0 u
Proof
  rpt gen_tac >> disch_then strip_assume_tac >> simp[] >> conj_tac
  >- (irule eval_operand_frame >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[wb_frame_vars]) >>
  `wb_frame cenv es sa s0 t` by metis_tac[expr_post_frame] >>
  irule wb_frame_trans >> simp[] >> conj_tac
  >- (qexistsl_tac [`es1`, `s1`, `t`] >> simp[]) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
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
  `wb_frame cenv es sa s0 t` by metis_tac[expr_post_frame] >>
  gvs[wb_args_post_def] >> conj_tac
  >- (irule eval_operand_frame >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[wb_frame_vars]) >>
  irule wb_frame_trans >> simp[] >> conj_tac
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

Theorem forced_eval_expr_preserves_scopes_dom:
  !cx e es res es'.
    (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==>
    MAP FDOM es.scopes = MAP FDOM es'.scopes
Proof
  rpt gen_tac >> simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule eval_expr_preserves_scopes_dom >> simp[]
QED

Theorem lower_word_args_sim_encoded:
  !args ctx func cenv cx arg_ty Ready V W es sa xs sb rr es' s0.
    Ready args es /\
    (!e rest st. Ready (e::rest) st ==>
      expr_sim ctx func cenv cx (arg_ty e) e st /\
      (!res st'. (do r <- eval_expr cx e; read_result cx r od) st = (res,st') ==>
        expr_res_ok res) /\
      (!v st'. (do r <- eval_expr cx e; read_result cx r od) st = (INL v,st') ==>
        V e v /\ Ready rest st')) /\
    (!e st ca cb t0 st' v x u. MEM e args /\ V e v /\
      expr_post ctx func cenv cx e st ca cb t0 st' v x u ==>
      eval_operand x u = SOME (W v)) /\
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    eval_exprs cx args es = (rr,es') /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?vs. rr = INL vs /\ stmt_state_rel ctx func cenv cx es' s /\
        LIST_REL (\x v. eval_operand x s = SOME (W v)) xs vs /\
        wb_frame cenv es sa s0 s)
      (wb_args_exit rr)
Proof
  Induct
  >- (simp[lower_word_args_nil, eval_exprs_nil] >> rpt strip_tac >>
      irule frag_exec_refl >> simp[wb_frame_refl]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `Ready (e::args) es` >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
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
  qpat_assum `!e rest st. Ready (e::rest) st ==> _`
    (drule_then strip_assume_tac) >>
  drule eval_exprs_cons_cases >> strip_tac
  >- (gvs[wb_args_exit_def] >>
      `expr_res_ok (INR exc)` by metis_tac[] >>
      drule_all expr_sim_apply >>
      disch_then (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
      irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  rename1 `eval_exprs cx args es1 = (rr1, _)` >>
  `V e v /\ Ready args es1` by metis_tac[] >>
  `expr_exit (INL v) = (\r. F)` by simp[FUN_EQ_THM] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  `expr_res_ok (INL v)` by simp[expr_res_ok_def] >>
  drule_all expr_sim_apply >> disch_then (qspec_then `s0` mp_tac) >>
  simp[expr_exit_def] >> disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  qpat_x_assum `!e' st ca cb t0 st' v x u. _` mp_tac >>
  pure_rewrite_tac[RIGHT_AND_OVER_OR, DISJ_IMP_THM] >>
  disch_then (fn th => assume_tac (cj 1 th) >> assume_tac (cj 2 th)) >>
  first_x_assum (drule_all_then (qspec_then `t` mp_tac)) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  conj_tac >- (Cases_on `rr1` >> simp[wb_args_exit_def]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[expr_post_state]) >>
  rpt strip_tac >> gvs[] >>
  `eval_operand x t = SOME (W' v)` by metis_tac[] >>
  drule_all encoded_args_post_cons >> simp[]
QED

Theorem compile_multi_exprs_typed_sim:
  !args ctx func cenv cx Ready V tv es sa xs sb rr es' s0.
    Ready args es /\
    (!e rest st. Ready (e::rest) st ==>
      expr_sim ctx func cenv cx (expr_type e) e st /\
      (!res st'. (do r <- eval_expr cx e; read_result cx r od) st = (res,st') ==>
        expr_res_ok res) /\
      (!v st'. (do r <- eval_expr cx e; read_result cx r od) st = (INL v,st') ==>
        V e v /\ Ready rest st')) /\
    (!e v. MEM e args /\ V e v ==> is_word_type (expr_type e) /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME tv) /\
    wb_args_shape cenv expr_type args /\
    compile_multi_exprs compile_expr cenv args sa = (xs,sb) /\
    eval_exprs cx args es = (rr,es') /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?vs. rr = INL vs /\ stmt_state_rel ctx func cenv cx es' s /\
        LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) xs vs /\
        wb_frame cenv es sa s0 s)
      (wb_args_exit rr)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_multi_exprs_lower_word_args] >>
  irule lower_word_args_sim_encoded >> simp[] >>
  qexistsl_tac [`Ready`, `V`, `expr_type`, `args`] >> simp[] >>
  metis_tac[expr_post_typed_stack_operand]
QED

Theorem lower_word_args_sim:
  !args ctx func cenv cx arg_ty I es sa xs sb rr es' s0.
    wb_args_ready ctx func cenv cx arg_ty I args /\ I es /\
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    eval_exprs cx args es = (rr,es') /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?vs. rr = INL vs /\ wb_args_post ctx func cenv cx es sa s0 es' xs vs s)
      (wb_args_exit rr)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `wb_args_ready ctx func cenv cx arg_ty Inv args` >>
  rewrite_tac[wb_args_post_def] >>
  irule lower_word_args_sim_encoded >> simp[] >>
  qexistsl_tac [
    `\args es. wb_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es`,
    `\e v. word_value v /\ is_word_type (expr_type e) /\
       IS_SOME (evaluate_type (get_tenv cx) (expr_type e))`, `arg_ty`, `args`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all expr_post_word_operand >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all wb_args_ready_head >> strip_tac >> simp[] >>
  rpt strip_tac >> metis_tac[wb_args_ready_tail]
QED

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

Theorem compile_word_builtin_sim:
  !ctx func cenv cx ty ann bt args arg_ty Inv es code.
    bt <> Len /\ bt <> Env MsgGas /\ bt <> Bop In /\ bt <> Bop NotIn /\
    builtin_args_length_ok bt (LENGTH args) /\ is_word_type ann /\
    wb_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
    wb_args_shape cenv arg_ty args /\
    (!sa sb op. lower_value compile_expr cenv ty (Builtin ann bt args) sa = (op,sb) ==>
      ?xs sm. lower_word_args cenv arg_ty args sa = (xs,sm) /\ code xs sm = (op,sb)) /\
    (!xs sm sb op. code xs sm = (op,sb) ==> cs_extends sm sb) /\
    (!vs es'. eval_exprs cx args es = (INL vs,es') ==>
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
  drule_all eval_expr_builtin_cases >> strip_tac
  >- (gvs[] >> drule_all lower_word_args_sim >>
      disch_then (qspec_then `s0` mp_tac) >> simp[wb_args_exit_def] >> strip_tac >>
      irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `!vs es'. _ ==> _` drule >> strip_tac >>
  `EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) xs` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all lower_word_args_sim >> disch_then (qspec_then `s0` mp_tac) >>
  simp[wb_args_exit_def] >> disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  gvs[] >> qpat_x_assum `word_builtin_frag _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[word_builtin_frag_def] >> disch_then drule_all >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> conj_tac
  >- gvs[wb_args_post_def] >>
  rpt strip_tac >> goal_assum (drule_at Any) >>
  irule expr_post_word_builtin >> goal_assum (drule_at Any) >>
  simp[] >> qexists_tac `sm` >> simp[] >>
  qexistsl_tac [`t`, `vs`, `xs`] >> simp[]
QED

Theorem compile_encoded_membership_sim:
  !ctx func cenv cx ty E e1 elems Ready V W es is_in.
    expr_type E = BaseT BoolT /\ Ready (e1::elems) es /\
    (!e rest st. Ready (e::rest) st ==>
      expr_sim ctx func cenv cx (expr_type e) e st /\
      (!res st'. (do r <- eval_expr cx e; read_result cx r od) st = (res,st') ==>
        expr_res_ok res) /\
      (!v st'. (do r <- eval_expr cx e; read_result cx r od) st = (INL v,st') ==>
        V e v /\ Ready rest st')) /\
    (!e st ca cb t0 st' v x u. MEM e (e1::elems) /\ V e v /\
      expr_post ctx func cenv cx e st ca cb t0 st' v x u ==>
      eval_operand x u = SOME (W v)) /\
    wb_args_shape cenv expr_type (e1::elems) /\
    (!sa op sb. lower_value compile_expr cenv ty E sa = (op,sb) ==>
      ?needle ops sm. lower_word_args cenv expr_type (e1::elems) sa = (needle::ops,sm) /\
        (if is_in then compile_list_membership_in needle ops
         else compile_list_membership_notin needle ops) sm = (op,sb)) /\
    eval_expr cx E es =
      (do vs <- eval_exprs cx (e1::elems);
          return (Value (BoolV (if is_in then MEM (HD vs) (TL vs)
                               else ~MEM (HD vs) (TL vs)))) od) es /\
    (!vs es'. eval_exprs cx (e1::elems) es = (INL vs,es') ==>
      (MEM (W (HD vs)) (MAP W (TL vs)) <=> MEM (HD vs) (TL vs))) ==>
    expr_sim ctx func cenv cx ty E es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_sim_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!sa op sb. _ ==> _` drule >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `straight_fresh (if is_in then compile_list_membership_in needle ops
                   else compile_list_membership_notin needle ops)` by
    (Cases_on `is_in` >> simp[straight_fresh_compile_list_membership]) >>
  `cs_extends sm sb` by (drule_all straight_fresh_cs_extends >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  Cases_on `eval_exprs cx (e1::elems) es` >>
  rename1 `eval_exprs cx (e1::elems) es = (rr,st)` >>
  Cases_on `rr` >> gvs[bind_def, return_def, read_result_def]
  >- (rename1 `eval_exprs cx (e1::elems) es = (INL vs,es')` >>
      `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
      qspec_then `e1::elems` (drule_all o SRULE [bind_def]) lower_word_args_sim_encoded >>
      disch_then (qspec_then `s0` mp_tac) >>
      simp[wb_args_exit_def, expr_exit_def] >>
      disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
      qx_gen_tac `t` >> strip_tac >>
      gvs[] >>
      `!z. MEM (Var z) ops ==> not_fresh_at sm z` by
        (gvs[EVERY_MEM] >> metis_tac[]) >>
      `MAP (\x. eval_operand x t) ops = MAP SOME (MAP W' ys)` by
        (simp[MAP_EQ_LIST_REL, LIST_REL_MAP2] >>
         metis_tac[LIST_REL_LENGTH]) >>
      drule_all compile_list_membership_sim >>
      disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`] mp_tac) >>
      disch_then (qspecl_then [`MAP W' ys`, `W' v`, `t`, `\r. F`] mp_tac) >>
      disch_then (mp_then Any irule frag_exec_weaken) >> simp[] >>
      rpt strip_tac >> irule expr_post_word_intro >> simp[] >>
      simp[is_word_type_def, word_value_def, valueEncodingTheory.val_to_w256_def,
           venomExecSemanticsTheory.bool_to_word_def] >>
      conj_tac
      >- (Cases_on `if is_in then MEM v ys else ~MEM v ys` >> simp[]) >>
      irule wb_frame_readonly_tail >> qexistsl_tac [`sm`, `t`] >> simp[]) >>
  qspec_then `e1::elems` (drule_all o SRULE [bind_def]) lower_word_args_sim_encoded >>
  disch_then (qspec_then `s0` mp_tac) >> simp[wb_args_exit_def] >> strip_tac >>
  irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED
