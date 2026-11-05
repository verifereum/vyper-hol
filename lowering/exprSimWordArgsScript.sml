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
  cheat
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
  cheat
QED

Theorem eval_exprs_cons_action:
  eval_exprs cx (e::args) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx args) (\vs. return (v::vs)))
Proof
  cheat
QED

Theorem eval_expr_builtin_action:
  bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
  builtin_args_length_ok bt (LENGTH args) ==>
  bind (eval_expr cx (Builtin ann bt args)) (read_result cx) =
  bind (eval_exprs cx args)
    (\vs ee. (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs,ee))
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem lower_word_args_cons:
  !cenv arg_ty e es sa xs sb.
    lower_word_args cenv arg_ty (e::es) sa = (xs, sb) <=>
    ?x s1 ys. lower_value compile_expr cenv (arg_ty e) e sa = (x, s1) /\
      lower_word_args cenv arg_ty es s1 = (ys, sb) /\ xs = x::ys
Proof
  cheat
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
  cheat
QED

(* ===== Composable expression frames ===== *)

Theorem wb_frame_refl:
  !cenv es sa s. wb_frame cenv es sa s s
Proof
  cheat
QED

Theorem wb_frame_vars:
  !cenv es sa s0 s x w.
    wb_frame cenv es sa s0 s /\ not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w
Proof
  cheat
QED

Theorem expr_post_frame:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s ==>
    wb_frame cenv es sa s0 s
Proof
  cheat
QED

Theorem expr_post_state:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s ==>
    stmt_state_rel ctx func cenv cx es' s
Proof
  cheat
QED

Theorem expr_post_word_operand:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\ word_value v ==>
    eval_operand op s = SOME (val_to_w256 v)
Proof
  cheat
QED

Theorem expr_post_word_intro:
  !func cenv cx e es sa sb s0 es' v op s ctx.
    stmt_state_rel ctx func cenv cx es' s /\ is_word_type (expr_type e) /\ word_value v /\
    eval_operand op s = SOME (val_to_w256 v) /\ wb_frame cenv es sa s0 s ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  cheat
QED

Theorem wb_frame_readonly_tail:
  !cenv es sa s0 t s1 u.
    wb_frame cenv es sa s0 t /\ sa.cs_next_var <= s1.cs_next_var /\
    (!z w. not_fresh_at s1 z /\ lookup_var z t = SOME w ==> lookup_var z u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = t.vs_memory ==>
    wb_frame cenv es sa s0 u
Proof
  cheat
QED

Theorem wb_frame_trans:
  !func cenv cx es s0 sa es1 s1 t u ctx.
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    wb_frame cenv es sa s0 t /\ wb_frame cenv es1 s1 t u ==>
    wb_frame cenv es sa s0 u
Proof
  cheat
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
  cheat
QED

Theorem wb_args_ready_tail:
  !ctx func cenv cx arg_ty I e args es v es1.
    wb_args_ready ctx func cenv cx arg_ty I (e::args) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
    wb_args_ready ctx func cenv cx arg_ty I args
Proof
  cheat
QED

Theorem eval_exprs_nil:
  !cx es. eval_exprs cx [] es = (INL [], es)
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem lower_word_args_shape_ready:
  !cenv arg_ty args sa xs sb.
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\ LENGTH xs = LENGTH args /\
    EVERY (\x. (!z. x = Var z ==> not_fresh_at sb z) /\ (!l. x <> Label l)) xs
Proof
  cheat
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
  cheat
QED

Theorem forced_eval_expr_preserves_scopes_dom:
  !cx e es res es'.
    (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==>
    MAP FDOM es.scopes = MAP FDOM es'.scopes
Proof
  cheat
QED

Theorem stmt_state_rel_gas_obs[simp]:
  stmt_state_rel ctx func cenv cx (es with gas_obs := gs) s =
  stmt_state_rel ctx func cenv cx es s
Proof
  cheat
QED

Theorem wb_args_head_admissible:
  wb_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem wb_frag_then:
  !ctx sa s1 P Q1.
    frag_exec ctx sa s1 P Q1 (\r. F) ==>
    !sb Q R. (!t. Q1 t ==> frag_exec ctx s1 sb (\s. s = t) Q R) /\
      cs_extends sa s1 /\ cs_extends s1 sb ==>
      frag_exec ctx sa sb P Q R
Proof
  cheat
QED

Theorem gas_marked_exec_cons_values:
  gas_marked_exec memory (ctx,func) (eval_exprs cx args)
    (es,s0) marks res mid r ==>
  gas_marked_exec memory (ctx,func)
    (bind (eval_exprs cx args) (\vs. return (v::vs)))
    (es,s0) marks (case res of INL vs => INL (v::vs) | INR exc => INR exc) mid r
Proof
  cheat
QED

Theorem eval_exprs_cons_ignore_action:
  ignore_bind (eval_exprs cx (e::args)) (return ()) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. ignore_bind (eval_exprs cx args) (return ()))
Proof
  cheat
QED

Theorem wb_args_head_exempt_cert:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,endpoint) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_exprs cx (e::args)) (return ()))
    (es,s0) marks (err,ee) (leaf,endpoint)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem word_builtin_marked_admissible:
  bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
  builtin_args_length_ok bt (LENGTH args) /\
  gas_admissible (bind (eval_expr cx (Builtin ann bt args)) (read_result cx))
    expr_res_ok es /\
  gas_marked_exec F (ctx,func) (eval_exprs cx args) (es,s0) marks (INL vs) ee r ==>
  expr_res_ok (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs)
Proof
  cheat
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
  cheat
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
  cheat
QED

