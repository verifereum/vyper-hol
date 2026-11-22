(* Request-prefix companion to bodyFullIfExpPrepare. *)
Theory s1PrefixIfExpPrepare
Ancestors
  s1PrefixPreds bodyFullIfExpPrepare s1PrefixDefs

Theorem ifexp_vv_prefix_root_uniform:
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  (!e sa sm av op sb es1 u G1 tn1 st0.
    (e = a \/ e = b) /\
    compile_expr cenv ty e sa = (av,sm) /\
    compile_ifexp_arm cenv t (lowered_value_type cenv e) av sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    !ee tv z G tn.
      (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
      (!id path. tv = PlaceR (MemoryPlace id path) ==>
        same_memory_layout cenv (lowered_value_type cenv e) t) /\
      storage_trace_domain cx st0 ee.storage_trace /\
      eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post H ctx func cenv cx e es1 sa sm u ee tv av z /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv av z /\
      z.vs_current_bb = sm.cs_current_bb /\
      z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
      alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
    ~is_bytestring_type (post_value_type cenv e) ==>
    vv_own cenv cx (post_value_type cenv e) sa sm ee tv av z) /\
      ptr_vv_ok cx (post_value_type cenv e) tv av ee G tn z /\
      (!t' op0. av = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
        ptr_buf_ok cenv e op0 G z) /\
      (!t' p. av = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G z) /\
      (cenv.ce_is_ctor /\ vv_location av = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand av) z = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      ghost_kept_at lo cenv es1 sa G1 tn1 u G tn /\
      (!v. read_result cx tv ee = (INL v,ee) ==>
        value_has_type rty v /\
        !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
          value_has_type ptv v) ==>
      ?v z' Gz tf.
        read_result cx tv ee = (INL v,ee) /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (z,G,tn) [] (OK z',Gz,tf) /\
          expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
          ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
        (~is_word_type t ==>
          vv_at cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z') /\
        (~is_word_type t ==> !id path. tv = PlaceR (MemoryPlace id path) ==>
          vv_place_ptr cenv cx ee z' tv (LocatedValue t (mk_ptr op LocMemory))) /\
    (!ctv v. conditional_result cx tv ee = (INL ctv,ee) /\
      ctv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
      vv_own cenv cx t sa sb ee ctv
        (LocatedValue t (mk_ptr op LocMemory)) z') /\
        expr_store_bound cx t v op z' /\
        z'.vs_current_bb = sb.cs_current_bb /\
        z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
        ptr_val_ok cx t v op Gz tf z' /\
        (~is_word_type t ==>
          !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
        (~is_word_type t ==>
          !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
        ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf) /\
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
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx (BaseT BoolT) c es /\
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx (BaseT BoolT) c es /\
  (!gs v es1.
     bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty a es1 /\
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty b es1 /\
     (!e gs' raw ee. (e = a \/ e = b) /\
       eval_expr cx e (es1 with gas_obs := gs') = (INL raw,ee) ==>
       eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
     !e gs' v' es2.
       (e = a \/ e = b) /\
       bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') =
         (INL v',es2) ==>
       value_has_type rty v' /\
       !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
             value_has_type ptv v') /\
  (!gs v es1.
     bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty a es1 /\
     expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty b es1) ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  cheat
QED
