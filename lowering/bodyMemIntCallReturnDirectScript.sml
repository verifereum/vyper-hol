(* An internal function's return statement, memory-safely, when the
   returned expression is lowered at its own type and that type is the
   return type, or the return type is a word or a bytestring (no compound
   widening into the caller's return buffer).  bodyMemIntCallFrameRet's
   internal_frame_ret_ok_mem is assembled from this and the held
   bodyMemIntCallReturnWidened. *)
Theory bodyMemIntCallReturnDirect
Ancestors
  bodyMemoryDefs intCallReturnMem stmtSimReturn compileEnv valueEncoding
  compileVyper internalReturnImmutableTypes internalReturnPathMem internalReturnStoreMem internalReturnSuffixMem internalReturnTupleMem internalReturnBytestringMem internalReturnCompileMem internalReturnComposeMem internalReturnVoidMem internalReturnWordMem stmtSimReturnWiden bodySim

(* ADMITTED (leaf): the internal twin of loweringMemFrameRet's
   external_frame_ret_ok_mem's direct returns.  The compile env returns
   internally (RET to the return PC), with the stack-return count of the
   declared return type, and has a return buffer exactly when that count
   is 0 and the type isn't void.  The buffer's capacity is the return
   value's size, a store's 64 bytes of rounding fit below 2 ** 256, and in
   a constructor it misses every immutable's region.  Tools:
   stmtSimReturnWord's compile_return_word_int_frag, stmtSimReturnTuple's
   compile_return_tuple_int_frag, intCallReturnMem's
   compile_internal_return_memory_frag and the bytestring branch of
   stmtSimReturnWiden's compile_internal_return_memory_widen_frag. *)
Theorem internal_return_direct_mem:
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
    (!e. eo = SOME e ==>
             lowered_value_type cenv' e = expr_type e /\
             (expr_type e = ret_ty \/ is_word_type ret_ty \/
              is_bytestring_type ret_ty)) ==>
    stmt_frag_mem rb ctx func cx lctx
        (case rb of
           NONE => intret_q func cenv cx ret_tv
         | SOME (bw,cap) => intret_mem_q func cenv cx ret_tv bw)
      cenv' (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo)) es
Proof
  rpt gen_tac >> strip_tac >> Cases_on `eo`
  >- (`ret_ty = NoneT` by fs[vyperTypeSystemTheory.type_stmt_def] >>
      `rb = NONE` by (Cases_on `rb` >> gvs[]) >> gvs[] >>
      irule internal_return_void_mem >> metis_tac[]) >>
  rename1 `Return (SOME e)` >> Cases_on `is_word_type ret_ty`
  >- (`cenv.ce_returns_count = 1` by
        (Cases_on `ret_ty` >> gvs[returns_stack_count_def, is_word_type_def]) >>
      `rb = NONE` by (Cases_on `rb` >> gvs[]) >>
      `expr_type e = ret_ty` by
        (irule stack_return_widens_eq >>
         conj_tac
         >- (qexists_tac `\name. MAP (FST o SND)
               (get_struct_fields cenv.ce_struct_fields name)` >> fs[]) >>
         qexists_tac `env.type_defs` >> fs[vyperTypeSystemTheory.type_stmt_def]) >>
      gvs[] >> irule internal_return_word_mem >>
      fs[same_frame_def, compile_env_component_equality] >> metis_tac[]) >>
  cheat
QED
