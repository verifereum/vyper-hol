(* Structural boundaries for the joint external-call request. *)
Theory bodyFullExtCallRequestInterfaces
Ancestors
  exprSimSource exprSimExtCallCase exprSimHypsDefs exprLowering exprLoweringProps gasShadow
  gasShadowCompileExternal exprCallbackContracts fragExec vyperTypeSystem
  supportedExprTraverse allocLimits vyperTypeCallGraph list rich_list
  compileEnv pair gasShadowState gasShadowCompile gasShadowCompileHelpers
  gasShadowCompileStmtHelpers
Libs
  pairLib

Theorem extcall_request_source_boundary:
  !cenv cx env ann stat skip name ats rt opts args dr es.
    expr_body_pre cenv cx env
      (Call ann (ExtCall stat skip (name,ats,rt) opts) args dr) es ==>
    ann = rt /\ dr = NONE /\ ext_call_opts_ok stat opts /\
    LENGTH args = 1 + LENGTH ats + LENGTH opts /\
    expr_type (HD args) = BaseT AddressT /\
    arg_types_fit (MAP expr_type (TAKE (LENGTH ats) (TL args))) ats /\
    MAP expr_type (DROP (1 + LENGTH ats) args) =
      MAP (ext_call_kw_type rt) opts /\
    (!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
      expr_body_pre cenv cx env e st)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def] >>
  rpt strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
      alloc_limits_expr_def, int_calls_expr_def,
      expr_has_evm_run_thm, supported_expr_exists_def,
      supported_exprs_exists_every, EVERY_MEM] >>
  imp_res_tac well_typed_exprs_member >>
  imp_res_tac byte_widths_exprs_mem >>
  imp_res_tac alloc_limits_exprs_mem >>
  imp_res_tac call_evaluation_safe_exprs_mem >>
  gvs[GSYM EVERY_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem extcall_request_operands_layout:
  !cenv ty ann stat skip name ats rt opts addr rest dr sa vv sb.
    compile_call compile_expr cenv ann ty
      (ExtCall stat skip (name,ats,rt) opts) (addr::rest) dr sa = (vv,sb) ==>
    ?ao av vo go def gas s1 s2 s3 s5 result.
      lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,s1) /\
      compile_ext_call_args compile_expr cenv (DROP (LENGTH ats) rest)
        (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))
        (TAKE (LENGTH ats) rest) s1 = (av,s2) /\
      compile_ext_call_kwargs compile_expr cenv rt opts
        (DROP (LENGTH ats) rest) s2 = ((vo,go,def),s3) /\
      (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
      compile_external_call_kwargs cenv ao av
        (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))
        (SUM (MAP (type_memory_bytes cenv)
          (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))))
        (abi_size_bound cenv.ce_struct_fields
          (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))))
        (cenv.ce_method_id name ats)
        (abi_size_bound cenv.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt))
        (abi_static_size cenv.ce_struct_fields
          (if needs_external_call_wrap rt then TupleT [rt] else rt))
        (type_memory_bytes cenv rt) stat
        (case vo of SOME v => v | NONE => Lit 0w) gas skip
        (IS_SOME def) (case def of SOME (d,dt) => d | NONE => Lit 0w)
        rt (case def of SOME (d,dt) => dt | NONE => rt)
        (type_to_abi_enc_info cenv.ce_struct_fields cenv
          (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))))
        (type_to_abi_dec_info cenv.ce_struct_fields cenv
          (if needs_external_call_wrap rt then TupleT [rt] else rt))
        s5 = (result,sb) /\
      vv = (if rt = NoneT then StackValue ann result
            else LocatedValue ann (mk_ptr result LocMemory))
Proof
  rpt gen_tac >> simp[compile_call_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs()]
QED

Theorem extcall_request_buffer_layout:
  !ce addr vals tys mem abi mid cap minsz retbytes stat value gas skip
   hasdef def rt dt enc dec sa ro sb.
    compile_external_call_kwargs ce addr vals tys mem abi mid cap minsz
      retbytes stat value gas skip hasdef def rt dt enc dec sa = (ro,sb) ==>
    ?ba s1 s2 len s3 off sp sr u.
      compile_alloc_buffer ((if abi > cap then abi else cap) + 32) sa = (ba,s1) /\
      emit_void MSTORE [ba.buf_operand; Lit (n2w mid)] s1 = ((),s2) /\
      (if vals = [] then comp_return (Lit 4w) else
        comp_bind (compile_alloc_buffer mem) (\aa.
        comp_ignore_bind (compile_extcall_store_values ce (ZIP (vals,tys))
                           aa.buf_operand 0)
        (comp_bind (emit_op ADD [ba.buf_operand; Lit 32w]) (\dst.
         comp_bind (compile_abi_encode_to_buf dst aa.buf_operand enc) (\alen.
         emit_op ADD [alen; Lit 4w]))))) s2 = (len,s3) /\
      emit_op ADD [ba.buf_operand; Lit 28w] s3 = (off,sp) /\
      comp_ignore_bind
        (if rt = NoneT /\ ~skip then compile_extcodesize_check addr
         else comp_return ())
        (comp_bind
          (if stat then emit_op STATICCALL
             [gas; addr; off; len; ba.buf_operand; Lit (n2w cap)]
           else emit_op CALL
             [gas; addr; value; off; len; ba.buf_operand; Lit (n2w cap)])
          (\success. comp_bind (fresh_label "extcall_fail") (\fail.
           comp_bind (fresh_label "extcall_cont") (\cont.
           comp_ignore_bind (emit_inst JNZ [success; Label cont; Label fail] [])
           (comp_ignore_bind (new_block fail)
           (comp_bind (emit_op RETURNDATASIZE []) (\rds.
            comp_bind (compile_alloc_buffer 0) (\fb.
            comp_ignore_bind (emit_void RETURNDATACOPY
                              [fb.buf_operand; Lit 0w; rds])
            (comp_ignore_bind (emit_inst REVERT [fb.buf_operand; rds] [])
                              (new_block cont)))))))))) sp = (u,sr) /\
      (if rt = NoneT then comp_return (Lit 0w)
       else if hasdef then
         comp_bind (compile_alloc_buffer retbytes) (\r.
           compile_default_return_path ce rt dt ba.buf_operand r.buf_operand
             def addr skip minsz cap dec)
       else comp_bind (compile_alloc_buffer retbytes) (\r.
         comp_bind (compile_return_value_decode minsz cap) (\hi.
         comp_ignore_bind (compile_abi_decode_to_buf r.buf_operand (Lit 0w)
                            MLOAD ba.buf_operand hi dec)
                          (comp_return r.buf_operand)))) sr = (ro,sb)
Proof
  rpt gen_tac >>
  simp[compile_external_call_kwargs_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
QED
