(*
 * The pointer judgment of an expression naming a mapping (a mapping
 * variable, or a mapping inside one), for the mapping subscript case of
 * bodyPtrSubscript.  The pointer twin of S1's expr_map_sim (exprSimMapDefs):
 * a mapping-typed base evaluates to a HashMapRef, which expr_vv_res_ok and
 * well_typed_expr leave out, so expr_body_pre never holds of it and
 * body_expr_ptr_ok says nothing of it.
 *
 * NEW DEFINITIONS: expr_map_sim_ptr_at, at the dead bytes D and the bound
 * lo as bodyPtrDefs' expr_vv_sim_ptr_at, and expr_map_sim_ptr, its
 * (cx_dead cx, 0) instance in a runtime frame, as expr_vv_sim_ptr is.
 * Its premises are expr_vv_sim_ptr's,
 * with the admissible results S1's expr_map_res_ok; its normal post is
 * expr_map_sim's (the operand holding the mapping's declared slot, and
 * vv_post's frame) with expr_vv_sim_ptr's ghost conjuncts, and the slot
 * operand untainted, as ptr_vv_ok asks of a located value's pointer.
 *
 * TOP-LEVEL:
 *   expr_map_sim_ptr_at, expr_map_sim_ptr
 *   expr_map_pre_other -- only a top-level name or a subscript names a
 *     mapping
 *)
Theory bodyPtrSubscriptMapDefs
Ancestors
  exprSimMapDefs bodyPtrDefs vyperStoragePlaceProvenance exprSimDefs loweringPosts
  fragGasPathPtr gasContext compileEnv valueEncoding exprLowering
  exprLoweringProps context venomState vyperInterpreter vyperState

Definition expr_map_sim_ptr_at_def:
  expr_map_sim_ptr_at D lo d ctx PG func cenv cx ty e es <=>
    !sa sb vv s0 G0 tn0.
      compile_expr cenv ty e sa = (vv, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
      dead_lo_ok D lo cenv cx /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_expr cx e) expr_map_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr_lo D lo (cx_tops cx) (ctx, func) PG
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
          (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          ghost_inv_at D lo d cenv cx ee G tn t /\
          op_taint tn p.ptr_operand = {} /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
End

Definition expr_map_sim_ptr_cx_dead:
  expr_map_sim_ptr d ctx PG func cenv cx ty e es <=>
    ~cenv.ce_is_ctor ==>
    expr_map_sim_ptr_at (cx_dead cx) 0 d ctx PG func cenv cx ty e es
End

Theorem expr_map_sim_ptr_def:
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
      stmt_state_rel H ctx func cenv cx es s0 /\
      ghost_inv H d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_ptr (cx_dead H cx) (cx_tops cx) (ctx, func) PG
        (eval_expr cx e) (es, s0, G0, tn0)
        (\res ee G tn t. ?tr slot kt vt tp p.
          res = INL (HashMapRef tr slot kt vt) /\
          storage_mapping_region cx tr slot (HashMapT kt vt) /\
          vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
          eval_operand p.ptr_operand t = SOME slot /\
          stmt_state_rel H ctx func cenv cx ee t /\
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
          ghost_inv H d cenv cx ee G tn t /\
          op_taint tn p.ptr_operand = {} /\
          ghost_kept cenv es sa G0 tn0 s0 G tn)
        (\res ee gt r. expr_exit res r)
Proof
  simp[expr_map_sim_ptr_cx_dead, expr_map_sim_ptr_at_def, dead_lo_ok_def, ghost_inv_cx_dead,
       ghost_kept_zero, gas_outcome_ptr_zero] >>
  Cases_on `cenv.ce_is_ctor` >> simp[]
QED

(* Only a top-level name and a subscript name a mapping (bodySim's
   expr_map_pre_shape), so the mapping clauses of bodyPtrPreds'
   body_expr_ptr_ok and bodyPtrPredsAt's body_expr_ptr_ok_at hold of every
   other form by simp. *)
Theorem expr_map_pre_other[simp]:
  !cenv cx env e es.
    (!ty id. e <> TopLevelName ty id) /\ (!ty e1 e2. e <> Subscript ty e1 e2) ==>
    ~expr_map_pre cenv cx env e es
Proof
  metis_tac[bodySimTheory.expr_map_pre_shape]
QED
