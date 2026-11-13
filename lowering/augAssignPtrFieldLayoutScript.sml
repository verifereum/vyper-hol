(* Split the field-address/load/RHS/operator/store code at stable boundaries. *)
Theory augAssignPtrFieldLayout
Ancestors
  stmtSimAugAssignAttr exprLoweringProps emitHelperProps fragExec
  compileEnv loweringSlice stmtLowering

Theorem augassign_attr_local_layout_ptr:
  stmt_env cenv lctx ty0
    (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) sa = (c,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME (StructT sid) /\ fn_has_code sa sb func ==>
  c = cenv /\
  ?sn s1 s2 s3 dst cur rhs res_op.
    emit_op ADD [Var p; Lit (n2w (struct_field_offset
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
      sa = (dst,sn) /\
    emit_op MLOAD [dst] sn = (cur,s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
    compile_binop bop cur rhs ty NONE
      (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op,s3) /\
    emit_void MSTORE [dst;res_op] s3 = ((),sb) /\
    cs_extends sa sn /\ cs_extends sn s1 /\ cs_extends s1 s2 /\
    cs_extends s2 s3 /\ cs_extends s3 sb /\
    cs_extends sa s1 /\ cs_extends sa s2 /\ cs_extends sa s3 /\
    cs_extends sn s2 /\ cs_extends sn s3 /\ cs_extends sn sb /\
    cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
    fn_has_code sa sn func /\ fn_has_code sn s1 func /\
    fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
    fn_has_code s3 sb func
Proof
  strip_tac >> drule_all augassign_attr_local_code_parts >> strip_tac >> simp[] >>
  `cs_extends sa sn /\ cs_extends sn s1 /\ cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends sa s1 /\ cs_extends sa s2 /\ cs_extends sa s3 /\
   cs_extends sn s2 /\ cs_extends sn s3 /\ cs_extends sn sb /\
   cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb` by
    metis_tac[cs_extends_trans] >>
  simp[] >> metis_tac[fn_has_code_mid, cs_extends_refl]
QED
