(* An internal function's return statement, memory-safely, for the
   returns bodyMemIntCallReturnDirect leaves out: a widened internal call's
   value (lowered at a type other than its own), or a compound value
   widening into the caller's return buffer. *)
Theory bodyMemIntCallReturnWidened
Ancestors
  bodyMemoryDefs intCallReturnMem stmtSimReturn compileEnv valueEncoding
  compileVyper

(* RESIDUAL (held): as loweringMemFrameRet's held
   external_frame_ret_widened_call_mem.  A widened call's value has
   expr_sim_mem only at expr_type e, while the return lowers it at
   lowered_value_type; and compile_internal_return_memory_widen_frag's
   compound branch needs the source disjoint from the return buffer, which
   return_buf_frame doesn't give (the buffer is the caller's, not a fresh
   ALLOCA). *)
Theorem internal_return_widened_mem:
  !tops ctx func cx cenv ret_ty ret_tv rb rpc rsz cenv' env lctx eo es.
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
    (IS_SOME rb <=> cenv.ce_returns_count = 0 /\ ret_ty <> NoneT) /\
    (!bw cap. rb = SOME (bw,cap) ==>
       cap = type_memory_size ret_tv /\
       w2n bw + cap + 64 < dimword (:256) /\
       (cenv.ce_is_ctor ==>
        !nm io ity itv.
          FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) =
            SOME (ImmutableLoc io) /\
          cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
          evaluate_type (get_tenv cx) ity = SOME itv ==>
          regions_disjoint io (type_memory_size itv) (w2n bw) cap)) /\
    same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
    stmt_exprs_ok cenv' (Return eo) /\
    IS_SOME (type_stmt env ret_ty (Return eo)) /\
    call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
    (!e ty. eo = SOME e ==>
            expr_sim_mem ctx func cenv' cx ty e es /\
            expr_vv_sim_mem ctx func cenv' cx ty e es) /\
    ~(!e. eo = SOME e ==>
              lowered_value_type cenv' e = expr_type e /\
              (expr_type e = ret_ty \/ is_word_type ret_ty \/
               is_bytestring_type ret_ty)) ==>
    stmt_frag_mem rb ctx func cx lctx
        (case rb of
           NONE => intret_q func cenv cx ret_tv
         | SOME (bw,cap) => intret_mem_q func cenv cx ret_tv bw)
      cenv' (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo)) es
Proof
  cheat
QED
