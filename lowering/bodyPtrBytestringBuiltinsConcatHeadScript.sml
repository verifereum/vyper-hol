(* Compiler cuts for one Concat iteration, before pointer execution dispatch. *)
Theory bodyPtrBytestringBuiltinsConcatHead
Ancestors
  bodyPtrBytestringBuiltinsConcatFrame bodyPtrBytestringBuiltinsConcatBytes
  bodyPtrBytestringBuiltinsEval exprLowering emitHelper compileEnv
Libs monadsyntax

Theorem compile_concat_bytes_cons:
  compile_concat compile_expr cenv (e::es) data_ptr ((T,m)::infos) off_ptr sa =
    ((),sb) ==>
  ?op sm sn.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    (do arg_len <- emit_op MLOAD [op];
        arg_data <- emit_op ADD [op;Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr;offset_op];
        emit_void MCOPY [dst;arg_data;arg_len];
        new_offset <- emit_op ADD [offset_op;arg_len];
        emit_void MSTORE [off_ptr;new_offset]
     od) sm = ((),sn) /\
    compile_concat compile_expr cenv es data_ptr infos off_ptr sn = ((),sb)
Proof
  simp[Once compile_concat_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_concat_fixed_cons:
  compile_concat compile_expr cenv (e::es) data_ptr ((F,m)::infos) off_ptr sa =
    ((),sb) ==>
  ?op sm sn.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr;offset_op];
        emit_void MSTORE [dst;op];
        new_offset <- emit_op ADD [offset_op;Lit (n2w m)];
        emit_void MSTORE [off_ptr;new_offset]
     od) sm = ((),sn) /\
    compile_concat compile_expr cenv es data_ptr infos off_ptr sn = ((),sb)
Proof
  simp[Once compile_concat_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED
