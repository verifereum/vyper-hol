(*
 * internal_return_widened_ptr's body, up to the two facts it lacks, both
 * owed by whoever closes the held leaf (see the RESIDUAL comment on
 * internal_return_widened_ptr in bodyPtrIntCallFrameRet):
 *   - a widened compound return's source is disjoint from the caller's
 *     return buffer at the return point (from the return buffer's frame
 *     invariant once it carries the caller-buffer frontier);
 *   - a returned internal call's compiled return type agrees with its
 *     signature (at the body induction, from expr_body_pre's FST id = NONE
 *     plus body_inv).
 * The held leaf closes by irule internal_return_widened_ptr_of_disjoint
 * once both are derivable.
 *
 * TOP-LEVEL:
 *   internal_return_widened_ptr_of_disjoint
 *)
Theory bodyPtrIntCallReturnWiden
Ancestors
  bodyPtrIntCallFrameRet internalReturnWidenPtr
  bodyPtrDefs intCallReturnMem stmtSimReturn bodySim
  internalReturnStackPtr internalReturnStorePtr internalReturnCountedPtr
  internalReturnStackSuffixPtr internalReturnMemorySuffixPtr
  stmtSimReturnWiden compileEnv valueEncoding compileVyper loweringPosts
  ptrDiscipline fragGasPathPtr venomExecSemantics ctorReturnFrame
  returnValueTyped valueEncodingTyping typedMemoryCopy

(* The first two premises are the RESIDUAL (held) facts.
   1. Source/return-buffer disjointness; discharged once return_buf_frame
      carries the caller-buffer frontier.  It is asked only of a returned
      expression that has evaluated (its expr_sim_ptr post at the return
      type), and only when the store is the typed copy (source type differs
      from a compound, non-bytestring return type).
   2. A returned internal call's compiled return type is its signature's;
      discharged at the body induction from expr_body_pre (FST id = NONE)
      plus body_inv. *)
Theorem internal_return_widened_ptr_of_disjoint:
  !tops ctx PG func cx cenv ret_ty ret_tv d rpc rsz cenv' env lctx eo es.
    (!x sa sb op s0 G0 tn0 ee G tn t v sw bw cap stv.
       eo = SOME x /\ d = SOME (bw,cap) /\
       lowered_value_type cenv' x <> ret_ty /\
       ~is_word_type ret_ty /\ ~is_bytestring_type ret_ty /\
       evaluate_type (get_tenv cx) (lowered_value_type cenv' x) = SOME stv /\
       lower_value compile_expr cenv' ret_ty x sa = (op, sb) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv' sa /\ ~ctx_has_dalloca ctx /\
       ~cenv'.ce_is_ctor /\
       stmt_state_rel ctx func cenv' cx es s0 /\
       ghost_inv d cenv' cx es G0 tn0 s0 /\ ~s0.vs_halted /\
       s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
       expr_post ctx func cenv' cx x es sa sb s0 ee v op t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv d cenv' cx ee G tn t /\
       ptr_val_ok cx (post_value_type cenv' x) v op G tn t /\
       ptr_buf_ok cenv' x op G t /\
       ghost_kept cenv' es sa G0 tn0 s0 G tn /\
       eval_operand op t = SOME sw ==>
       regions_disjoint (w2n sw) (type_memory_size stv) (w2n bw) cap) /\
    (!ann id args drv sig.
       eo = SOME (Call ann (IntCall id) args drv) /\
       FLOOKUP env.fn_sigs id = SOME sig ==>
       cenv'.ce_func_return_type (nsid_to_string id) = sig.ret_ty) /\
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    (!off sz. cenv.ce_return_buf <> SOME (MemLoc off sz)) /\
    cenv.ce_imm_alloca = NONE /\
    (!nr nkey ut iv. cenv.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
    cenv.ce_returns_count =
      returns_stack_count
        (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name))
        ret_ty /\
    evaluate_type (get_tenv cx) ret_ty = SOME ret_tv /\
    (IS_SOME d <=> cenv.ce_returns_count = 0 /\ ret_ty <> NoneT) /\
    (!bw cap. d = SOME (bw,cap) ==>
       cap = type_memory_size ret_tv /\
       w2n bw + cap < dimword (:256) /\ cap + 64 < dimword (:256)) /\
    same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
    stmt_exprs_ok cenv' (Return eo) /\
    IS_SOME (type_stmt env ret_ty (Return eo)) /\
    call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
    (!e ty. eo = SOME e ==>
            expr_sim_ptr d ctx PG func cenv' cx ty e es /\
            expr_vv_sim_ptr d ctx PG func cenv' cx ty e es) /\
    ~(!e. eo = SOME e ==>
             lowered_value_type cenv' e = expr_type e /\
             (expr_type e = ret_ty \/ is_word_type ret_ty \/
              is_bytestring_type ret_ty)) ==>
    stmt_frag_ptr d ctx PG func cx lctx (intret_ptr_q func cenv cx ret_tv d)
      cenv' (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo))
      es
Proof
  cheat
QED
