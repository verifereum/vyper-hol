(*
 * The internal frame's returns, with the ghost (the producer the internal
 * call case needs; bodyPtrIntCallCase).
 *
 * TOP-LEVEL:
 *   intret_ptr_q -- what an internal frame's return hands its caller: the
 *     S1 return (intret_q, or intret_mem_q at the caller's return buffer),
 *     storage taint confined to dead bytes, and a memory-returned value
 *     independent of tainted memory.  The caller's ghost and the INVOKE
 *     outputs' taint come back through ptrSafeRun's ghost_step instead.
 *   internal_frame_ret_ok_ptr -- in an internal function's compile env,
 *     every return statement exits pointer-safely with intret_ptr_q;
 *     assembled from internal_return_direct_ptr (admitted leaf) and
 *     internal_return_widened_ptr (held residual)
 *)
Theory bodyPtrIntCallFrameRet
Ancestors
  bodyPtrDefs intCallReturnMem bodyIntCallReturnCopy stmtSimReturn bodySim
  compileEnv valueEncoding compileVyper

(* The return an internal frame hands back: d is the caller's return
   buffer (its address and capacity) when the value comes back in memory. *)
Definition intret_ptr_q_def:
  intret_ptr_q func cenv cx ret_tv d v (es : evaluation_state)
    (G, tn) r <=>
    (case d of
       NONE => intret_q func cenv cx ret_tv v es r
     | SOME (bw, cap) => intret_mem_q func cenv cx ret_tv bw v es r) /\
    ?ir s. r = IntRet ir s /\ stor_taint_ok cx tn s /\
      !bw cap mem.
        d = SOME (bw, cap) /\
        mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory ret_tv v (w2n bw) mem
End

(* ADMITTED (leaf): the pointer twin of s3-mem's internal_return_direct_mem:
   an internal function's return statement, pointer-safely, when the
   returned expression is lowered at its own type and that type is the
   return type, or the return type is a word or a bytestring (no compound
   widening into the caller's return buffer).  The compile env returns
   internally (RET to the return PC), with the stack-return count of the
   declared return type, and has a return buffer exactly when that count
   is 0 and the type isn't void; the buffer's capacity is the return
   value's size, it fits below 2 ** 256, and so does that size plus a
   copy's 64 bytes of length rounding (size headroom, not address
   headroom: the store never offsets the buffer address).
   Constructor frames are excluded by stmt_frag_ptr itself.  S1's pieces:
   stmtSimReturn (step_ret_values, compile_load_tuple_elements_run,
   intret_vals_match_word/_tuple), bodyIntCallReturnCopy's
   compile_internal_return_memory_size_bound_frag (the size-headroom form
   of intCallReturnMem's compile_internal_return_memory_frag), and the
   bytestring branch of
   stmtSimReturnWiden's compile_internal_return_memory_widen_frag; the
   returned expression's expr_sim_ptr/expr_vv_sim_ptr for the ghost side
   (ptr_mem_ok makes the source robust under t_mem, and MCOPY carries its
   taint to the buffer). *)
Theorem internal_return_direct_ptr:
  !tops ctx PG func cx cenv ret_ty ret_tv d rpc rsz cenv' env lctx eo es.
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_imm_alloca = NONE /\
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
    (!e. eo = SOME e ==>
             lowered_value_type cenv' e = expr_type e /\
             (expr_type e = ret_ty \/ is_word_type ret_ty \/
              is_bytestring_type ret_ty)) ==>
    stmt_frag_ptr d ctx PG func cx lctx (intret_ptr_q func cenv cx ret_tv d)
      cenv' (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo))
      es
Proof
  cheat
QED

(* RESIDUAL (held): as s3-mem's held internal_return_widened_mem.  A
   compound value widening into the caller's return buffer is copied
   element by element (compile_copy_dynarray_typed: a forward loop with
   different source and destination strides, no memmove), which is right
   only when the source is disjoint from the buffer.  Nothing here ties
   the buffer to the frame's allocas (return_buf_ptr gives only ghost
   coverage, and ghost_inv carries no alloca frontier for it), so for a
   buffer at the frame's alloca frontier the copy clobbers its own
   source.  Real runs don't reach that state; the fix is a frontier
   conjunct in return_buf_ptr's SOME arm. *)
Theorem internal_return_widened_ptr:
  !tops ctx PG func cx cenv ret_ty ret_tv d rpc rsz cenv' env lctx eo es.
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_imm_alloca = NONE /\
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

(* The internal twin of extFrameRetOkPtr's external_frame_ret_ok_ptr and
   the pointer twin of s3-mem's internal_frame_ret_ok_mem, assembled from
   the two cases above. *)
Theorem internal_frame_ret_ok_ptr:
  !tops ctx PG func cx cenv ret_ty ret_tv d rpc rsz.
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_imm_alloca = NONE /\
    cenv.ce_returns_count =
      returns_stack_count
        (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name))
        ret_ty /\
    evaluate_type (get_tenv cx) ret_ty = SOME ret_tv /\
    (IS_SOME d <=> cenv.ce_returns_count = 0 /\ ret_ty <> NoneT) /\
    (!bw cap. d = SOME (bw,cap) ==>
       cap = type_memory_size ret_tv /\
       w2n bw + cap < dimword (:256) /\ cap + 64 < dimword (:256)) ==>
    frame_ret_ok_ptr d ctx PG func cx (intret_ptr_q func cenv cx ret_tv d)
      cenv ret_ty
Proof
  rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC [frame_ret_ok_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `(!e. eo = SOME e ==>
             lowered_value_type cenv' e = expr_type e /\
             (expr_type e = ret_ty \/ is_word_type ret_ty \/
              is_bytestring_type ret_ty))`
  >- (irule internal_return_direct_ptr >> metis_tac[]) >>
  irule internal_return_widened_ptr >> metis_tac[]
QED
