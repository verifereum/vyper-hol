(* The internal frame's returns, with memory (the producer the internal
   call step needs; bodyMemIntCall).

   TOP-LEVEL:
   - internal_frame_ret_ok_mem: in an internal function's compile env,
     every return statement exits memory-safely as the caller expects: an
     IntRet that intret_q accepts for a stack return, and for a memory
     return one that intret_mem_q accepts, with the value at the caller's
     return buffer bw. *)
Theory bodyMemIntCallFrameRet
Ancestors
  bodyMemoryDefs bodyMemIntCallReturnDirect bodyMemIntCallReturnWidened

(* Assembled from bodyMemIntCallReturnDirect and the held
   bodyMemIntCallReturnWidened.  The internal twin of loweringMemFrameRet's
   external_frame_ret_ok_mem.  The compile env returns internally (RET to
   the return PC), with the stack-return count of the declared return type,
   and has a return buffer exactly when that count is 0 and the type isn't
   void.  The buffer's capacity is the return value's size, a store's 64
   bytes of rounding fit below 2 ** 256, and in a constructor it misses
   every immutable's region.  Tools: stmtSimReturnWord's
   compile_return_word_int_frag, stmtSimReturnTuple's
   compile_return_tuple_int_frag, intCallReturnMem's
   compile_internal_return_memory_frag and stmtSimReturnWiden's
   compile_internal_return_memory_widen_frag for the S1 exits; the
   returned expression's memory simulation for the memory side. *)
Theorem internal_frame_ret_ok_mem:
  !tops ctx func cx cenv ret_ty ret_tv rb rpc rsz.
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
          regions_disjoint io (type_memory_size itv) (w2n bw) cap)) ==>
    frame_ret_ok_mem rb ctx func cx
      (case rb of
         NONE => intret_q func cenv cx ret_tv
       | SOME (bw,cap) => intret_mem_q func cenv cx ret_tv bw)
      cenv ret_ty
Proof
  rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC [frame_ret_ok_mem_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `(!e. eo = SOME e ==>
                      lowered_value_type cenv' e = expr_type e /\
                      (expr_type e = ret_ty \/ is_word_type ret_ty \/
                       is_bytestring_type ret_ty))`
  >- (qspecl_then [`tops`,`ctx`,`func`,`cx`,`cenv`,`ret_ty`,`ret_tv`,`rb`,`rpc`,`rsz`,`cenv'`,`env`,`lctx`,`eo`,`es`] mp_tac internal_return_direct_mem >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  qspecl_then [`tops`,`ctx`,`func`,`cx`,`cenv`,`ret_ty`,`ret_tv`,`rb`,`rpc`,`rsz`,`cenv'`,`env`,`lctx`,`eo`,`es`] mp_tac internal_return_widened_mem >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
