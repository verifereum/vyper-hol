Theory bodyFullBopRestWordTail
Ancestors bodyFullBopRestWordTailFixed bodyFullBopRestWordTailDynamic

Theorem rest_word_membership_tail_full:
 !DF lo d explicit ctx fn PG cenv cx e es sa sm s0 G0 tn0 tv vv ee u Gu Tu needleop needle av ety bd pbd et is_in out ct guard.
 compile_var_array_membership cenv needleop vv (ArrayT ety bd) is_in sm = (out,ct) /\
 fn_has_code sm ct fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
 local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x. needleop = Var x \/ vv_operand vv = Var x ==> not_fresh_at sm x) /\
 is_word_type ety /\ expr_type e = ArrayT ety bd /\ post_value_type cenv e = ArrayT ety pbd /\
 (case bd of Fixed n => pbd = Fixed n | Dynamic cap => ?pcap. pbd = Dynamic pcap) /\
 (case bd of Fixed n => n | Dynamic cap => cap) < dimword (:256) /\
 ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
 (!H. guard H ==>
   read_result cx tv ee = (INL (ArrayV av),ee) /\
   evaluate_type (get_tenv cx) ety = SOME et /\
   evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME (ArrayTV et pbd) /\
   value_has_type (ArrayTV et bd) (ArrayV av) /\ value_has_type et needle /\
   eval_operand needleop u = SOME (typed_val_to_w256 et needle) /\
   op_prov (Gu H) needleop = NONE /\ op_taint (Tu H) needleop = {} /\
   vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
   alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
   ghost_inv_at (DF H) lo d cenv cx ee (Gu H) (Tu H) u /\
   ptr_vv_ok cx (post_value_type cenv e) tv vv ee (Gu H) (Tu H) u /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside (Tu H).t_mem u.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
   (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (Gu H) u) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (Gu H) u) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 (Gu H) (Tu H)) ==>
 ?t Gt Tt. !H. guard H ==>
   gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
     (u,Gu H,Tu H) [] (OK t,Gt H,Tt H) /\
   membership_loop_frame sm (Gu H) (Tu H) u (Gt H) (Tt H) t /\
   ~t.vs_halted /\ t.vs_current_bb = ct.cs_current_bb /\
   t.vs_inst_idx = LENGTH ct.cs_current_insts /\
   alloca_history fn t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
   vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv t /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
   ghost_inv_at (DF H) lo d cenv cx ee (Gt H) (Tt H) t /\
   ptr_vv_ok cx (post_value_type cenv e) tv vv ee (Gt H) (Tt H) t /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) t = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside (Tt H).t_mem t.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
   (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (Gt H) t) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (Gt H) t) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 (Gt H) (Tt H) /\
   eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
   op_prov (Gt H) needleop = NONE /\ op_taint (Tt H) needleop = {} /\
   eval_operand out t = SOME (bool_to_word
     (if is_in then evaluate_in_array (ArrayTV et bd) needle av
      else ~evaluate_in_array (ArrayTV et bd) needle av)) /\
   op_prov (Gt H) out = NONE /\ op_taint (Tt H) out = {}
Proof
  rpt gen_tac >> Cases_on `bd`
  >- (strip_tac >> irule rest_word_membership_tail_fixed_full >> gvs[] >> metis_tac[]) >>
  strip_tac >> irule rest_word_membership_tail_dynamic_full >> gvs[] >> metis_tac[]
QED
