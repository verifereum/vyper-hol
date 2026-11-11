(* The RHS snapshot of an Assign whose target can modify memory or storage
   (compile_stmt's Assign, expr_can_mutate), memory-counted: a word value is
   read at once, a composite one is copied into a fresh temporary
   (compile_snapshot_vv cenv T).  The copy's buffer is one of the snapshot's
   own allocations, so the saved value is clear of every live local
   (vv_own), and the snapshot writes nothing outside its own allocations
   (pure_frame).  bodyPtrAssignSnapshot is the pointer-safety sibling. *)
Theory bodyMemAssignSnapshot
Ancestors
  exprSimMemUnwrap exprSimMemDefs loweringPosts allocaHistory fragGasMode
  exprLowering context compileEnv vyperInterpreter vyperState venomState

Theorem snapshot_vv_counted_mem:
  !ctx func cenv cx e es sa sm sb s0 ee tv v vv saved s.
    post_value_type cenv e = expr_type e /\
    compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) vv) sm =
      (saved, sb) /\
    read_result cx tv ee = (INL v, ee) /\
    (!tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
           value_has_type tvt v) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!t op'. vv = StackValue t op' ==> is_word_type (expr_type e)) /\
    (is_word_type (expr_type e) ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    (!t tvt. (t = expr_type e \/ t = lowered_value_type cenv e) /\
             evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
             type_memory_bytes cenv t = type_memory_size tvt /\
             type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_marked_path T ctx func s 0 (OK u) /\
        vv_post ctx func cenv cx e es sa sb s0 ee tv saved u /\
        vv_own cenv cx (expr_type e) sm sb ee tv saved u /\
        pure_frame cenv func ee sm s u /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv
          saved u /\
        alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
