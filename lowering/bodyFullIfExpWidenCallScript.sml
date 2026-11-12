(* The arm step of a ternary whose arm is an internal call the lowering
   types at the callee's return type, a widening of the ternary's type:
   unwrap the arm's value at its lowered type, then read it as the
   ternary's type in place (same layout) or copy it into a fresh buffer
   of the ternary's type (compile_store_memory_typed), as one joint path
   with no GAS site. *)
Theory bodyFullIfExpWidenCall
Ancestors
  bodySimFull fragGasOriginPtr exprSimIfExp exprSimDefs exprSimMemDefs
  bodyPtrDefs loweringPosts exprLowering fragExec emitHelper compileEnv
  allocaHistory stmtSimDefs typedCopyDomain vyperTypeSystem
  vyperAST vyperInterpreter vyperState venomState

(* The unwrap inside is the shared joint unwrap_value lemma (r7), here its
   premise. *)
Theorem ifexp_widened_call_arm_step_full:
  (!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
     compile_expr cenv ty e sa = (vv,sm) /\
     sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
     unwrap_value cenv vv sb = (op,sc) /\
     local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
     MAP FDOM es.scopes = MAP FDOM ee.scopes /\
     sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
     fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
     ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
     (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
     (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     ~is_word_type (post_value_type cenv e) ==>
     type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
     type_memory_size rt < 2**64) /\
     evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
     (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
     vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
     vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
     alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
     ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
     s.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv_at D lo d cenv cx ee G tn s /\
     ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
     (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G s) /\
     (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G s) /\
     (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val, ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand vv) s = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rt val (w2n w) mem)) /\
     ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
     ?v H tf z.
     read_result cx tv ee = (INL v, ee) /\
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK z, H, tf) /\
     expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
     expr_store_bound cx (post_value_type cenv e) v op z /\
     z.vs_current_bb = sc.cs_current_bb /\
     z.vs_inst_idx = LENGTH sc.cs_current_insts /\
     alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
     s0.vs_alloca_next <= z.vs_alloca_next /\
     ghost_inv_at D lo d cenv cx ee H tf z /\
     ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
     (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
     eval_operand op z = SOME w ==>
     type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
     ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
     (!x. not_fresh_at sb x ==>
          lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tf (Var x) = op_taint tn (Var x)) /\
     wb_frame cenv ee sb s z /\
     ghost_kept_at lo cenv ee sb G tn s H tf) /\
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_type e = t /\ expr_type e0 = t /\ post_value_type cenv e0 = t /\
  ~is_word_type t /\ post_value_type cenv e = lowered_value_type cenv e /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==> value_has_type rty v) /\
  (!v ptv. read_result cx tva ee = (INL v,ee) /\
          evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
          value_has_type ptv v) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  vv_post ctx func cenv cx e es1 sa sm u ee tva vv z /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee G tn z /\
  ptr_vv_ok cx (post_value_type cenv e) tva vv ee G tn z /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G z) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tva ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es1 sa G1 tn1 u G tn ==>
  ?v z' H tf.
    read_result cx tva ee = (INL v,ee) /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (z, G, tn) [] (OK z', H, tf) /\
    expr_post ctx func cenv cx e0 es1 sa sb u ee v op z' /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee H tf z' /\
    ptr_val_ok cx t v op H tf z' /\
    (~is_word_type t ==>
     !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op H z') /\
    (~is_word_type t ==>
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/
            w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u H tf
Proof
  cheat
QED
