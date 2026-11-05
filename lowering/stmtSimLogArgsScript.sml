(* Frame interfaces for typed log arguments. *)
Theory stmtSimLogArgs
Ancestors
  exprBopSimProps
  exprSimDefs exprSimProps exprSimStack loweringPosts
  exprSimOps exprSimOperands compileEnv venomState stmtLowering
  exprSimWordArgs exprSimHyps exprSimAttributeFields

(* A captured value in a live local survives a later expression whenever
   its footprint avoids the local's dynamic array length words, the only
   local bytes expressions may change (locals_kept). *)
Theorem log_local_footprint_kept:
  !cenv es s t n b sz off len.
    locals_kept cenv es s t /\
    local_region cenv es.scopes s n b sz /\
    b <= off /\ off + len <= b + sz /\
    (!k. dynarray_len_at cenv n k ==> off + len <= b + k \/ b + k + 32 <= off) ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory
Proof
  cheat
QED

Theorem log_local_value_kept:
  !cenv cx ty tv v op es s t n b sz w.
    expr_val_rel cx ty v op s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
    eval_operand op s = SOME w /\ eval_operand op t = SOME w /\
    locals_kept cenv es s t /\
    local_region cenv es.scopes s n b sz /\
    b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
    (!k. dynarray_len_at cenv n k ==>
         w2n w + val_footprint tv v <= b + k \/ b + k + 32 <= w2n w) ==>
    expr_val_rel cx ty v op t
Proof
  cheat
QED

(* Wherever a value of type ty sits in a live local, it is apart from the
   local's dynamic array length words. *)
Definition log_arg_clear_def:
  log_arg_clear cenv cx ty v <=>
    !tv n j k.
      evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
      local_val_at cenv cx n j tv v /\ dynarray_len_at cenv n k ==>
      j + val_footprint tv v <= k \/ k + 32 <= j
End

(* A base type value holds no dynamic array, so it is clear of them. *)
Theorem log_arg_clear_base:
  expr_sim_inv cenv cx env es ==> log_arg_clear cenv cx (BaseT bt) v
Proof
  cheat
QED

Theorem log_argument_footprint_kept:
  !cenv cx ty tv v op sa sb es s t w.
    expr_val_at cenv cx ty sa sb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    ~is_word_type ty /\ log_arg_clear cenv cx ty v /\
    eval_operand op s = SOME w /\
    wb_frame cenv es sb s t ==>
    mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  cheat
QED

Theorem log_argument_value_kept:
  !cenv cx ty es sa sb s t v op.
    expr_val_rel cx ty v op s /\
    expr_val_at cenv cx ty sa sb es v op s /\
    wb_frame cenv es sb s t /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) /\
    log_arg_clear cenv cx ty v ==>
    expr_val_rel cx ty v op t
Proof
  cheat
QED

Theorem compile_log_eval_all_nil:
  compile_log_eval_all cenv [] sa = ([], sa)
Proof
  cheat
QED

Theorem compile_log_eval_all_cons:
  compile_log_eval_all cenv (e::args) sa = (xs, sb) <=>
  ?x sm ys.
    lower_value compile_expr cenv (expr_type e) e sa = (x, sm) /\
    compile_log_eval_all cenv args sm = (ys, sb) /\
    xs = (x, expr_type e)::ys
Proof
  cheat
QED

Theorem compile_log_eval_all_types:
  !args sa xs sb.
    compile_log_eval_all cenv args sa = (xs, sb) ==>
    MAP SND xs = MAP expr_type args
Proof
  cheat
QED

(* lower_word_args itself is type-polymorphic; only its simulation theorem
   is word-specific. Reuse its compile-state shape interface. *)
Theorem compile_log_eval_all_operands:
  !args sa xs sb.
    compile_log_eval_all cenv args sa = (xs, sb) ==>
    lower_word_args cenv expr_type args sa = (MAP FST xs, sb)
Proof
  cheat
QED

Theorem compile_log_eval_all_shape:
  !args cenv.
    (!e sa sb x. MEM e args /\
       lower_value compile_expr cenv (expr_type e) e sa = (x, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. x = Var z ==> not_fresh_at sb z) /\ (!l. x <> Label l)) ==>
    !sa sb xs. compile_log_eval_all cenv args sa = (xs, sb) ==>
      cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
      sa.cs_next_id <= sb.cs_next_id /\ LENGTH xs = LENGTH args /\
      EVERY (\x. (!z. FST x = Var z ==> not_fresh_at sb z) /\
                 (!l. FST x <> Label l)) xs
Proof
  cheat
QED

Theorem log_frame_operand:
  wb_frame cenv es sb s t /\
  (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  cheat
QED

Theorem log_frame_local_region:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  wb_frame cenv es sb s t ==>
  (local_region cenv es'.scopes t n b sz <=>
   local_region cenv es.scopes s n b sz)
Proof
  cheat
QED

Theorem log_frame_placement:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sb.cs_next_id <= sc.cs_next_id /\ wb_frame cenv es sb s t /\
  (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) /\
  expr_val_at cenv cx ty sa sb es v op s ==>
  expr_val_at cenv cx ty sa sc es' v op t
Proof
  cheat
QED

Definition log_arg_rel_def:
  log_arg_rel cenv cx sa sb es s (op,ty) v <=>
    expr_val_rel cx ty v op s /\ expr_val_at cenv cx ty sa sb es v op s /\
    log_arg_clear cenv cx ty v
End

Theorem log_arg_rel_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  log_arg_rel cenv cx sm sb es s arg v ==>
  log_arg_rel cenv cx sa sb es s arg v
Proof
  cheat
QED

Theorem log_arg_rel_frame:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sb.cs_next_id <= sc.cs_next_id /\ wb_frame cenv es sb s t /\
  (!z. FST arg = Var z ==> not_fresh_at sb z) /\
  (!l. FST arg <> Label l) /\
  log_arg_rel cenv cx sa sb es s arg v ==>
  log_arg_rel cenv cx sa sc es' t arg v
Proof
  cheat
QED

Definition log_args_post_def:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s <=>
    stmt_state_rel ctx func cenv cx es' s /\
    LIST_REL (log_arg_rel cenv cx sa sb es' s) xs vs /\
    wb_frame cenv es sa s0 s
End

Theorem log_args_post_nil:
  stmt_state_rel ctx func cenv cx es s ==>
  log_args_post ctx func cenv cx es sa sa s es [] [] s
Proof
  cheat
QED

Theorem log_args_post_state:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s ==>
  stmt_state_rel ctx func cenv cx es' s
Proof
  cheat
QED

Theorem log_args_post_frame:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s ==>
  wb_frame cenv es sa s0 s
Proof
  cheat
QED

Theorem log_args_post_values:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s ==>
  LIST_REL (\arg v. expr_val_rel cx (SND arg) v (FST arg) s) xs vs
Proof
  cheat
QED

Theorem log_args_post_placements:
  log_args_post ctx func cenv cx es sa sb s0 es' xs vs s ==>
  LIST_REL (\arg v. expr_val_at cenv cx (SND arg) sa sb es' v (FST arg) s) xs vs
Proof
  cheat
QED

Theorem log_args_post_cons:
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  expr_sim_inv cenv cx env0 es0 /\ expr_type e = BaseT bt /\
  expr_post ctx func cenv cx e es sa sm s0 es1 v x t /\
  log_args_post ctx func cenv cx es1 sm sb t es' ys vs u ==>
  log_args_post ctx func cenv cx es sa sb s0 es'
    ((x,expr_type e)::ys) (v::vs) u
Proof
  cheat
QED
