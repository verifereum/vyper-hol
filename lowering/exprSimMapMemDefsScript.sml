(* The memory-counted judgment of an expression naming a mapping. *)
Theory exprSimMapMemDefs
Ancestors
  exprSimMapDefs exprSimMemDefs

(* exprSimMapDefs' expr_map_sim with every executed instruction inside
   allocated memory (gas_outcome T), and allocation history kept, as
   exprSimMemDefs' expr_vv_sim_mem adds them to expr_vv_sim. *)
Definition expr_map_sim_mem_def:
  expr_map_sim_mem ctx func cenv cx ty e es <=>
    !sa sb vv s0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_expr cx e) expr_map_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func) (eval_expr cx e) (es, s0)
        (\res ee t. ?tr slot kt vt tp p.
          res = INL (HashMapRef tr slot kt vt) /\
          storage_mapping_region cx tr slot (HashMapT kt vt) /\
          vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
          eval_operand p.ptr_operand t = SOME slot /\
          stmt_state_rel ctx func cenv cx ee t /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          (!aid off sz.
             FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\
             aid < sa.cs_next_id /\
             (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                        off + sz <= b \/ b + sz' <= off) ==>
             mem_bytes_at off sz t.vs_memory =
               mem_bytes_at off sz s0.vs_memory) /\
          locals_kept cenv es ee s0 t /\
          (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r /\ halt_exit cx ee res r)
End
