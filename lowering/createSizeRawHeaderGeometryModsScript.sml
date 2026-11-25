(* Allocation and byte widths at the actual raw CREATE snapshot site. *)
Theory createSizeRawHeaderGeometryMods
Ancestors
  createSizeRawHeaderGeometry createExprSizeExitDefsMods
  createBlueprintRawCopyLayoutMods exprLowering exprLoweringProps compileEnv
  copyExecution abiDecoderBytesTyped abiEncodeArgsCase loweringHalt
  exprPtrUnwrapAllocSeparation fragExec emitHelperProps loweringPosts
  exprSimHyps valueEncodingProps context words arithmetic pair
  allocLimits exprBodyPreProps exprSimHypsDefs exprSimIfExpCompat exprSimSource
  vyperTypeEvalCaseProofs vyperTypeSystem

Theorem create_raw_header_capacity_mods:
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  lowered_value_type ce e = BaseT (BytesT (Dynamic n)) ==>
  32 <= type_memory_bytes ce (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size (BaseTV (BytesT (Dynamic n))) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) < 2 ** 64
Proof
  strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[well_formed_type_def, env_consistent_var_type_evaluates] >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
            ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[expr_sim_inv_mods_def] >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (drule_all ifexp_lowered_type_classify >> strip_tac >>
     gvs[ifexp_arg_type_fits_refl] >> PairCases_on `fid` >>
     gvs[well_typed_expr_def, lowered_value_type_def, vyperASTTheory.expr_type_def] >>
     qpat_assum `!fid sg. _ ==> ce.ce_func_return_type _ = _`
       (drule_then assume_tac) >>
     gvs[type_widens_to_def, arg_type_fits_def]) >>
  `type_alloc_ok ce (expr_type e)` by
    (irule alloc_limits_expr_type_alloc_ok >> fs[expr_body_pre_mods_def]) >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
   type_memory_bytes ce (expr_type e)` by
    (irule (cj 1 abi_args_fits_memory_bytes) >> simp[]) >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    (qpat_x_assum `type_alloc_ok _ _` mp_tac >>
     simp[type_alloc_ok_def, is_word_type_def]) >>
  mp_tac (Q.INST [`n` |-> `n`, `ce` |-> `ce`] abi_decoder_bytes_copy_size) >>
  strip_tac >> gvs[] >> decide_tac
QED
