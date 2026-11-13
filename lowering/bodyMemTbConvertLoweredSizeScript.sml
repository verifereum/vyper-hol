(* Lowered source capacity for the plain convert operand. *)
Theory bodyMemTbConvertLoweredSize
Ancestors exprSimIfExp exprSimIfExpCompat exprSafeOperand exprSimHyps memoryLocalRhsProps
  exprSimSource exprSimHypsDefs
  vyperTypeSystem vyperValue vyperABI exprLowering context list compileEnv

Theorem convert_abi_encode_lowered_fits:
  !ce env ann ensure mid ty args.
    well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) ty args) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            well_formed_type env.type_defs t) /\
    sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
    (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==>
       ce.ce_func_return_type (nsid_to_string fid) = sig.ret_ty) ==>
    is_bytestring_type ann /\
    is_bytestring_type (lowered_value_type ce
      (TypeBuiltin ann (AbiEncode ensure mid) ty args)) /\
    arg_type_fits (lowered_value_type ce
      (TypeBuiltin ann (AbiEncode ensure mid) ty args)) ann
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ifexp_lowered_type_classify >>
  simp[vyperASTTheory.expr_type_def] >> strip_tac >>
  gvs[ifexp_arg_type_fits_refl, lowered_value_type_def, is_bytestring_type_def]
QED

Theorem convert_plain_lowered_type_compatible:
  !ce e env.
    well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            well_formed_type env.type_defs t) /\
    sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
    (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==>
       ce.ce_func_return_type (nsid_to_string fid) = sig.ret_ty) /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type ce e = expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ifexp_lowered_type_classify >> strip_tac >> gvs[]
QED

Theorem convert_plain_body_pre_lowered_size:
  !ce cx env e es tops.
    expr_body_pre ce cx env e es /\ supported_expr tops e /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type ce e = expr_type e) ==>
    type_memory_bytes ce (lowered_value_type ce e) <=
    type_memory_bytes ce (expr_type e)
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
   (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==>
      ce.ce_func_return_type (nsid_to_string fid) = sig.ret_ty)` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def,
        exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all convert_plain_lowered_type_compatible >> strip_tac >>
  irule lowered_value_type_memory_bound >> metis_tac[]
QED
