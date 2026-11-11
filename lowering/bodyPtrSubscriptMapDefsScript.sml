(*
 * The pointer judgment of an expression naming a mapping (a mapping
 * variable, or a mapping inside one), for the mapping subscript case of
 * bodyPtrSubscript.  The pointer twin of S1's expr_map_sim (exprSimMapDefs):
 * a mapping-typed base evaluates to a HashMapRef, which expr_vv_res_ok and
 * well_typed_expr leave out, so expr_body_pre never holds of it and
 * body_expr_ptr_ok says nothing of it.
 *
 * NEW DEFINITION: expr_map_sim_ptr.  Its premises are expr_vv_sim_ptr's,
 * with the admissible results S1's expr_map_res_ok; its normal post is
 * expr_map_sim's (the operand holding the mapping's declared slot, and
 * vv_post's frame) with expr_vv_sim_ptr's ghost conjuncts, and the slot
 * operand untainted, as ptr_vv_ok asks of a located value's pointer.
 *
 * TOP-LEVEL:
 *   expr_map_sim_ptr
 *)
Theory bodyPtrSubscriptMapDefs
Ancestors
  exprSimMapDefs bodyPtrDefs vyperStoragePlaceProvenance exprSimDefs loweringPosts
  fragGasPathPtr gasContext compileEnv valueEncoding exprLowering
  exprLoweringProps context venomState vyperInterpreter vyperState

Definition expr_map_sim_ptr_def:
  expr_map_sim_ptr d ctx PG func cenv cx ty e es <=>
    !sa sb vv s0 G0 tn0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
      ~cenv.ce_is_ctor /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_expr cx e) expr_map_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
        (eval_expr cx e) (es, s0, G0, tn0)
        (\res ee G tn t. ?tr slot kt vt tp p.
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
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_inv d cenv cx ee G tn t /\
          op_taint tn p.ptr_operand = {} /\
          ghost_kept cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
End
