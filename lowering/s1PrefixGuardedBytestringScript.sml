(* Guarded list and address premises for bytestring builtin prefixes. *)
Theory s1PrefixGuardedBytestring
Ancestors
  s1PrefixPreds bodyFullPreds vyperInterpreter vyperAST list
  s1PrefixBuiltinCalldataSlice s1PrefixBuiltinConcat
  s1PrefixBuiltinSlice s1PrefixBuiltinUint2Str

Theorem bytestring_builtin_expr_prefix_ok:
  !cx ty bt es.
    ((?n. bt = CalldataSlice n) \/ (?n. bt = Concat n) \/ (?n. bt = Slice n) \/
     (?n. bt = Uint2Str n)) /\
    (builtin_args_length_ok bt (LENGTH es) ==>
      case code_slice_source bt es of
        NONE => body_exprs_full_ok cx es
      | SOME (code_ty,addr) =>
          body_exprs_full_ok cx (TL es) /\
          (!s tail_vs t. eval_exprs cx (TL es) s = (INL tail_vs,t) ==>
            body_exprs_full_ok cx [addr])) /\
    (builtin_args_length_ok bt (LENGTH es) ==>
      case code_slice_source bt es of
        NONE => body_exprs_prefix_ok cx es
      | SOME (code_ty,addr) =>
          body_exprs_prefix_ok cx (TL es) /\
          (!s tail_vs t. eval_exprs cx (TL es) s = (INL tail_vs,t) ==>
            body_exprs_prefix_ok cx [addr])) ==>
    body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_prefix_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `(?n. bt = CalldataSlice n) \/ _` mp_tac >> strip_tac
      >- (gvs[code_slice_source_def] >>
          metis_tac[calldata_slice_expr_sim_prefix, calldata_slice_vv_sim_prefix])
      >- (gvs[code_slice_source_def] >> irule concat_sim_prefix >> metis_tac[])
      >- (gvs[] >> irule slice_builtin_sim_prefix >> metis_tac[]) >>
      gvs[code_slice_source_def] >> irule uint2str_builtin_sim_prefix >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED
