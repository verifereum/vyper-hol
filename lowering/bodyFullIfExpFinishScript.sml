(* The end of a ternary's selected arm: the arm's value is in op at u;
   ASSIGN it to the result variable and jump to the exit block, as one
   joint path with no GAS site, and give the ternary's root posts. *)
Theory bodyFullIfExpFinish
Ancestors
  bodySimFull fragGasOriginPtr exprSimIfExp exprSimDefs exprSimMemDefs
  bodyPtrDefs loweringPosts exprLowering fragExec emitHelper compileEnv
  allocaHistory stmtSimDefs vyperAST vyperInterpreter vyperState venomState

Theorem ifexp_arm_finish_full:
  (* the root's premises *)
  stmt_state_rel ctx func cenv cx es s0 /\ return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\ ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  (* the condition's posts at tt *)
  expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  s0.vs_alloca_next <= tt.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (* the selected arm's posts at u, from the jump to its block *)
  stmt_state_rel ctx func cenv cx es1 (jump_to lbl tt) /\
  read_result cx tv ee = (INL v,ee) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
  expr_store_bound cx t v op u /\
  u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~u.vs_halted /\
  alloca_history func u /\ tt.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee G tn u /\
  ptr_val_ok cx t v op G tn u /\
  (~is_word_type t ==>
   !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G u) /\
  (~is_word_type t ==>
   !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
          eval_operand op u = SOME w ==>
          type_memory_size rt = 0 \/
          w2n w + type_memory_size rt <= u.vs_alloca_next) /\
  ghost_kept_at lo cenv es1 sc G1 tn1 (jump_to lbl tt) G tn /\
  (* the layout *)
  expr_type e = t /\ post_value_type cenv e = t /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func ==>
  ?z H tf.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (u, G, tn) [] (OK z, H, tf) /\
    vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
      (if is_word_type t then StackValue t (Var rv)
       else LocatedValue t (mk_ptr (Var rv) LocMemory)) z /\
    vv_store_bound cx (expr_type (IfExp t c a b))
      (lowered_value_type cenv (IfExp t c a b)) ee tv
      (if is_word_type t then StackValue t (Var rv)
       else LocatedValue t (mk_ptr (Var rv) LocMemory)) z /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee H tf z /\
    ptr_vv_ok cx (post_value_type cenv (IfExp t c a b)) tv
      (if is_word_type t then StackValue t (Var rv)
       else LocatedValue t (mk_ptr (Var rv) LocMemory)) ee H tf z /\
    (~is_word_type t ==> ptr_buf_ok cenv (IfExp t c a b) (Var rv) H z) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 H tf
Proof
  cheat
QED
