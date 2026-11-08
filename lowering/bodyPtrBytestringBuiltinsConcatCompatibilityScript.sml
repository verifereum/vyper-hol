(* A shared block-local boundary for compiler introduction and body consumers.
   This excludes records with linked operands, not opcode membership. *)
Theory bodyPtrBytestringBuiltinsConcatCompatibility
Ancestors
  exprLowering exprLoweringProps exprCallBounds fragExec context
  compileEnv emitHelper venomInst list vyperAST exprSimHypsDefs

Definition concat_header_free_def:
  concat_header_free func <=>
  !label bb p q i0 i1 i2 i3 bytes b data off.
    lookup_block label func.fn_blocks = SOME bb ==>
    bb.bb_instructions <>
      p ++ [mk_inst i0 ALLOCA [Lit (n2w bytes)] [b];
            mk_inst i1 ADD [Var b; Lit 32w] [data];
            mk_inst i2 ALLOCA [Lit 64w] [off];
            mk_inst i3 MSTORE [Var off; Lit 0w] []] ++ q
End

Theorem names_builtin_not_concat[local]:
  !args. ~names_builtin (Concat n) args
Proof
  `!bt args. names_builtin bt args ==> bt <> Concat n` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_concat_mandatory_header:
  compile_expr cenv out_ty (Builtin ann (Concat n) args) sa = (vv,sb) /\
  fn_has_code sa sb func ==> ~concat_header_free func
Proof
  simp[compile_expr_builtin_dispatch, names_builtin_not_concat] >>
  simp[Once compile_builtin_dispatch_component_eq] >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  `ci_mono st3b st4a` by
    (mp_tac (cj 1 compile_expr_ci_mono) >>
     metis_tac[ci_mono_compile_concat_cfn, ci_mono_expr_child_callback,
               pairTheory.SND]) >>
  `cs_extends st3b sb` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, fresh_var_def,
         fresh_id_def, emit_def, ci_mono_def] >>
     irule cs_extends_trans >> goal_assum (drule_at Any) >>
     simp[cs_extends_def, APPEND_ASSOC, prefix_drop_equiv, DROP_PREFIX]) >>
  `cs_extends sa st3b` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, fresh_var_def,
         fresh_id_def, emit_def] >>
     simp[cs_extends_def, APPEND_ASSOC, prefix_drop_equiv, DROP_PREFIX]) >>
  `fn_has_code sa st3b func` by metis_tac[fn_has_code_split] >>
  qpat_x_assum `fn_has_code sa st3b func`
    (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def,
      fresh_id_def, emit_def, prefix_drop_equiv, APPEND_ASSOC] >>
  qpat_x_assum `concat_header_free func`
    (drule o REWRITE_RULE [concat_header_free_def]) >>
  metis_tac[]
QED
