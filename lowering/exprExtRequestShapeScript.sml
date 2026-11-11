(* Definitional boundaries for the external request compiler. *)
Theory exprExtRequestShape
Ancestors
  exprLowering loweringShapeProps exprExtRequestTyping compileEnv
  exprSimHypsDefs vyperTypeSystem supportedExprTraverse vyperAST list
  exprCallbackContracts exprCallBounds exprSimSource allocLimits vyperTypeCallGraph
  exprLoweringProps fragExec exprSafeOperand

Definition extrequest_compile_prefix_def:
  extrequest_compile_prefix cenv arg_vals arg_types args_mem_size args_abi_size
      method_id_val return_abi_size args_enc_info =
    comp_bind
      (compile_alloc_buffer
        ((if args_abi_size > return_abi_size then args_abi_size
          else return_abi_size) + 32))
      (\buf. comp_ignore_bind
        (emit_void MSTORE [buf.buf_operand; Lit (n2w method_id_val)])
        (comp_bind
          (if arg_vals = [] then comp_return (Lit 4w)
           else comp_bind (compile_alloc_buffer args_mem_size)
             (\args_buf. comp_ignore_bind
               (compile_extcall_store_values cenv (ZIP (arg_vals,arg_types))
                  args_buf.buf_operand 0)
               (comp_bind (emit_op ADD [buf.buf_operand; Lit 32w])
                 (\dst. comp_bind
                   (compile_abi_encode_to_buf dst args_buf.buf_operand args_enc_info)
                   (\len. emit_op ADD [len; Lit 4w])))))
          (\len. comp_bind (emit_op ADD [buf.buf_operand; Lit 28w])
            (\offset. comp_return (buf.buf_operand,offset,len)))))
End

Definition extrequest_compile_step_def:
  extrequest_compile_step return_type skip_check use_staticcall gas_op addr_op
      call_value call_offset call_len buf_op return_abi_size =
    comp_ignore_bind
      (if return_type = NoneT /\ ~skip_check then
         compile_extcodesize_check addr_op else comp_return ())
      (comp_bind
        (if use_staticcall then
           emit_op STATICCALL [gas_op; addr_op; call_offset; call_len;
                              buf_op; Lit (n2w return_abi_size)]
         else emit_op CALL [gas_op; addr_op; call_value; call_offset; call_len;
                            buf_op; Lit (n2w return_abi_size)])
        (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
         comp_bind (fresh_label "extcall_cont") (\cont_lbl.
         comp_ignore_bind
           (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
         (comp_ignore_bind (new_block fail_lbl)
         (comp_bind (emit_op RETURNDATASIZE []) (\rds.
         comp_bind (compile_alloc_buffer 0) (\fail_buf.
         comp_ignore_bind
           (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
         (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
           (new_block cont_lbl))))))))))
End

Definition extrequest_compile_return_def:
  extrequest_compile_return cenv return_type has_default default_ty buf_op
      default_op addr_op skip_check min_return_size return_abi_size
      ret_mem_bytes ret_dec_info =
    if return_type = NoneT then comp_return (Lit 0w)
    else if has_default then
      comp_bind (compile_alloc_buffer ret_mem_bytes)
        (\r. compile_default_return_path cenv return_type default_ty
          buf_op r.buf_operand default_op addr_op skip_check min_return_size
          return_abi_size ret_dec_info)
    else comp_bind (compile_alloc_buffer ret_mem_bytes)
      (\r. comp_bind (compile_return_value_decode min_return_size return_abi_size)
        (\hi. comp_ignore_bind
          (compile_abi_decode_to_buf r.buf_operand (Lit 0w) MLOAD
             buf_op hi ret_dec_info)
          (comp_return r.buf_operand)))
End

Theorem extrequest_compile_kwargs_factor:
  compile_external_call_kwargs cenv addr_op arg_vals arg_types args_mem_size
    args_abi_size method_id_val return_abi_size min_return_size ret_mem_bytes
    use_staticcall call_value gas_op skip_check has_default default_op
    return_type default_ty args_enc_info ret_dec_info =
  comp_bind
    (extrequest_compile_prefix cenv arg_vals arg_types args_mem_size
       args_abi_size method_id_val return_abi_size args_enc_info)
    (\(buf_op,call_offset,call_len).
      comp_ignore_bind
        (extrequest_compile_step return_type skip_check use_staticcall gas_op
           addr_op call_value call_offset call_len buf_op return_abi_size)
        (extrequest_compile_return cenv return_type has_default default_ty buf_op
           default_op addr_op skip_check min_return_size return_abi_size
           ret_mem_bytes ret_dec_info))
Proof
  simp[compile_external_call_kwargs_def, extrequest_compile_prefix_def,
       extrequest_compile_step_def, extrequest_compile_return_def,
       comp_ignore_bind_def, comp_bind_assoc] >>
  simp[comp_bind_def, comp_return_def, FUN_EQ_THM]
QED

Theorem extrequest_compile_kwargs_split:
  !cenv addr_op arg_vals arg_types args_mem_size args_abi_size method_id_val
   return_abi_size min_return_size ret_mem_bytes use_staticcall call_value
   gas_op skip_check has_default default_op return_type default_ty
   args_enc_info ret_dec_info sa result_op sb.
    compile_external_call_kwargs cenv addr_op arg_vals arg_types args_mem_size
      args_abi_size method_id_val return_abi_size min_return_size ret_mem_bytes
      use_staticcall call_value gas_op skip_check has_default default_op
      return_type default_ty args_enc_info ret_dec_info sa = (result_op,sb)
    ==> ?buf_op call_offset call_len sp u sr.
      extrequest_compile_prefix cenv arg_vals arg_types args_mem_size
        args_abi_size method_id_val return_abi_size args_enc_info sa =
        ((buf_op,call_offset,call_len),sp) /\
      extrequest_compile_step return_type skip_check use_staticcall gas_op
        addr_op call_value call_offset call_len buf_op return_abi_size sp =
        (u,sr) /\
      extrequest_compile_return cenv return_type has_default default_ty buf_op
        default_op addr_op skip_check min_return_size return_abi_size
        ret_mem_bytes ret_dec_info sr = (result_op,sb)
Proof
  rpt gen_tac >> rewrite_tac[extrequest_compile_kwargs_factor] >>
  Cases_on `extrequest_compile_prefix cenv arg_vals arg_types args_mem_size
    args_abi_size method_id_val return_abi_size args_enc_info sa` >>
  rename1 `extrequest_compile_prefix _ _ _ _ _ _ _ _ _ = (triple,sp)` >>
  PairCases_on `triple` >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  rpt strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extrequest_compile_call_split:
  !cfn cenv ann ty is_static skip fname arg_types ret_type opts addr rest dflt
   sa vv sb.
    compile_call cfn cenv ann ty
      (ExtCall is_static skip (fname,arg_types,ret_type) opts)
      (addr::rest) dflt sa = (vv,sb) ==>
    ?addr_op s1 arg_vals s2 value_opt gas_opt default_opt s3 gas_op s4 result_op.
      lower_value cfn cenv (BaseT AddressT) addr sa = (addr_op,s1) /\
      compile_multi_vvs cfn cenv (TAKE (LENGTH arg_types) rest) s1 =
        (arg_vals,s2) /\
      compile_ext_call_kwargs cfn cenv ret_type opts
        (DROP (LENGTH arg_types) rest) s2 = ((value_opt,gas_opt,default_opt),s3) /\
      (case gas_opt of SOME g => (g,s3) | NONE => emit_op GAS [] s3) =
        (gas_op,s4) /\
      (let call_types = MAP (lowered_value_type cenv)
                         (TAKE (LENGTH arg_types) rest) in
       let wrapped = if needs_external_call_wrap ret_type
                     then TupleT [ret_type] else ret_type in
       let (has_default,default_op,default_ty) =
         case default_opt of SOME (d,dty) => (T,d,dty)
           | NONE => (F,Lit 0w,ret_type) in
       compile_external_call_kwargs cenv addr_op arg_vals call_types
         (SUM (MAP (type_memory_bytes cenv) call_types))
         (abi_size_bound cenv.ce_struct_fields (TupleT call_types))
         (cenv.ce_method_id fname arg_types)
         (abi_size_bound cenv.ce_struct_fields wrapped)
         (abi_static_size cenv.ce_struct_fields wrapped)
         (type_memory_bytes cenv ret_type) is_static
         (case value_opt of SOME v => v | NONE => Lit 0w)
         gas_op skip has_default default_op ret_type default_ty
         (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT call_types))
         (type_to_abi_dec_info cenv.ce_struct_fields cenv wrapped) s4 =
         (result_op,sb)) /\
      vv = (if ret_type = NoneT then StackValue ann result_op
            else LocatedValue ann (mk_ptr result_op LocMemory))
Proof
  rpt gen_tac >> simp[Once compile_call_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  strip_tac >> Cases_on `ret_type = NoneT` >> gvs[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extrequest_body_typed:
  !cenv cx env ann stat skip sig opts args d es.
    expr_body_pre cenv cx env (Call ann (ExtCall stat skip sig opts) args d) es ==>
    well_typed_expr env (Call ann (ExtCall stat skip sig opts) args d) /\
    EVERY (\e. ~expr_has_effect e) (DROP 1 args)
Proof
  rpt strip_tac >>
  gvs[expr_body_pre_def] >>
  metis_tac[call_operands_effect_extcall_tail]
QED


Theorem extrequest_typed_nonempty:
  !env ann stat skip fname arg_types ret_type opts args d.
    well_typed_expr env
      (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args d) ==>
    args <> [] /\ ann = ret_type /\ d = NONE /\
    LENGTH args = 1 + LENGTH arg_types + LENGTH opts /\
    ext_call_opts_ok stat opts /\
    (ret_type = NoneT ==> ~MEM EKDefault opts)
Proof
  rpt gen_tac >> simp[Once well_typed_expr_def] >>
  Cases_on `args` >> simp[]
QED

Theorem extrequest_compile_expr_extcall:
  compile_expr cenv ty
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dflt) sa =
  compile_call compile_expr cenv ann ty
    (ExtCall stat skip (fname,ats,rt) opts) args dflt sa
Proof
  `expr_callbacks_agree
     (expr_child_callback
       (expr_size (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dflt))
       compile_expr) compile_expr cenv (call_callback_children args dflt)` by
    (irule expr_child_callback_agrees >>
     metis_tac[call_callback_child_bound]) >>
  simp[Once compile_expr_def, expr_type_def] >>
  irule compile_extcall_callback_contract >> gvs[expr_size_def]
QED

Theorem extrequest_body_pre_arg:
  !cenv cx env ann stat skip fname ats rt opts args d e es es'.
    expr_body_pre cenv cx env
      (Call ann (ExtCall stat skip (fname,ats,rt) opts) args d) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[expr_has_evm_run_thm, EXISTS_MEM, int_calls_expr_def] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Theorem extrequest_compile_kwarg_type:
  !cfn cenv rt k e s op dty t.
    compile_ext_call_kwarg cfn cenv rt k e s = ((op,dty),t) ==>
    dty = (if k = EKDefault /\ ~is_word_type rt
           then lowered_value_type cenv e else rt)
Proof
  rpt gen_tac >> Cases_on `k = EKDefault /\ ~is_word_type rt` >>
  simp[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem extrequest_compile_kwargs_no_default:
  !ks es s v gas def t.
    ~MEM EKDefault ks /\
    compile_ext_call_kwargs cfn cenv rt ks es s = ((v,gas,def),t) ==>
    def = NONE
Proof
  Induct >- simp[compile_ext_call_kwargs_def, comp_return_def] >>
  gen_tac >> Cases_on `es` >- simp[compile_ext_call_kwargs_def, comp_return_def] >>
  rpt gen_tac >> simp[compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  ntac 4 (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  Cases_on `h` >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem extrequest_compile_kwargs_default_type:
  !ks es s v gas op dty t.
    MAP expr_type es = MAP (ext_call_kw_type rt) ks /\
    EVERY (well_typed_expr env) es /\ EVERY (\e. ~expr_has_effect e) es /\
    compile_ext_call_kwargs cfn cenv rt ks es s = ((v,gas,SOME (op,dty)),t) ==>
    dty = rt \/ is_bytestring_type dty /\ is_bytestring_type rt
Proof
  Induct >- simp[compile_ext_call_kwargs_def, comp_return_def] >>
  gen_tac >> Cases_on `es` >- simp[compile_ext_call_kwargs_def, comp_return_def] >>
  rpt gen_tac >> simp[compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  ntac 4 (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  Cases_on `h` >> simp[ext_call_kw_type_def] >> rpt strip_tac >> gvs[]
  >- (first_x_assum irule >> simp[] >> metis_tac[])
  >- (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule extrequest_compile_kwarg_type >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[extrequest_lowered_type_compatible]
QED

(* The corresponding compiler facts are local in exprLoweringProps. *)
Theorem extrequest_store_values_mono[local]:
  !vals cenv buf off s.
    ci_mono s (SND (compile_extcall_store_values cenv vals buf off s))
Proof
  Induct >> rpt gen_tac
  >- simp[compile_extcall_store_values_def, ci_mono_comp_return] >>
  PairCases_on `h` >>
  simp[Once compile_extcall_store_values_def, LET_THM] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_unwrap_value] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >>
      simp[ci_mono_emit_void, ci_mono_compile_store_bytestring] >>
      IF_CASES_TAC >>
      simp[ci_mono_emit_void, ci_mono_compile_store_bytestring]) >>
  rpt strip_tac >> first_x_assum irule
QED

Theorem extrequest_compile_prefix_mono:
  !cenv vals tys mem abi mid cap info s.
    ci_mono s
      (SND (extrequest_compile_prefix cenv vals tys mem abi mid cap info s))
Proof
  rpt gen_tac >> rewrite_tac[extrequest_compile_prefix_def] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_alloc_buffer] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- simp[ci_mono_emit_void] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (gen_tac >> IF_CASES_TAC >- simp[ci_mono_comp_return] >>
      rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[ci_mono_compile_alloc_buffer] >>
      rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
      >- simp[extrequest_store_values_mono] >>
      rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
      rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[cj 2 ci_mono_compile_abi_encode] >>
      simp[ci_mono_emit_op]) >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >>
  simp[ci_mono_emit_op, ci_mono_comp_return]
QED

Theorem extrequest_compile_step_mono:
  !rt skip stat gas addr value off len buf cap s.
    ci_mono s
      (SND (extrequest_compile_step rt skip stat gas addr value off len buf cap s))
Proof
  rpt gen_tac >> rewrite_tac[extrequest_compile_step_def] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (gen_tac >> IF_CASES_TAC >- (
        rewrite_tac[compile_extcodesize_check_def] >>
        rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
      simp[ci_mono_comp_return]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (gen_tac >> IF_CASES_TAC >> simp[ci_mono_emit_op]) >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_fresh_label] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_fresh_label] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- simp[ci_mono_emit_inst] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_alloc_buffer] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- simp[ci_mono_emit_void] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> simp[ci_mono_emit_inst, ci_mono_new_block]
QED

Theorem extrequest_compile_return_mono:
  !cenv rt hd dty buf def addr skip min cap mem info s.
    ci_mono s (SND (extrequest_compile_return cenv rt hd dty buf def addr
      skip min cap mem info s))
Proof
  rpt gen_tac >> rewrite_tac[extrequest_compile_return_def] >>
  IF_CASES_TAC >- simp[ci_mono_comp_return] >>
  IF_CASES_TAC
  >- (rpt gen_tac >> ho_match_mp_tac ci_mono_bind >>
      simp[ci_mono_compile_alloc_buffer, ci_mono_compile_default_return_path]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_alloc_buffer] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_return_value_decode] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >>
  simp[cj 1 ci_mono_compile_abi_decode, ci_mono_comp_return]
QED

Theorem extrequest_compile_kwargs_code:
  !cenv addr vals tys mem abi mid cap min rmem stat value gas skip hd def rt dty
   enc dec sa result sb func.
    compile_external_call_kwargs cenv addr vals tys mem abi mid cap min rmem
      stat value gas skip hd def rt dty enc dec sa = (result,sb) /\
    fn_has_code sa sb func ==>
    ?buf off len sp u sr.
      extrequest_compile_prefix cenv vals tys mem abi mid cap enc sa =
        ((buf,off,len),sp) /\
      extrequest_compile_step rt skip stat gas addr value off len buf cap sp =
        (u,sr) /\
      extrequest_compile_return cenv rt hd dty buf def addr skip min cap rmem dec sr =
        (result,sb) /\
      ci_mono sa sp /\ ci_mono sp sr /\ ci_mono sr sb /\
      fn_has_code sa sp func /\ fn_has_code sp sr func /\ fn_has_code sr sb func
Proof
  rpt strip_tac >> drule extrequest_compile_kwargs_split >> strip_tac >>
  `ci_mono sa sp` by metis_tac[extrequest_compile_prefix_mono, pairTheory.SND] >>
  `ci_mono sp sr` by metis_tac[extrequest_compile_step_mono, pairTheory.SND] >>
  `ci_mono sr sb` by metis_tac[extrequest_compile_return_mono, pairTheory.SND] >>
  qexistsl_tac [`buf_op`,`call_offset`,`call_len`,`sp`,`u`,`sr`] >>
  simp[] >>
  `cs_extends sp sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  gvs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem extrequest_typed_kwargs:
  !env ann stat skip fname ats rt opts addr rest d.
    well_typed_expr env
      (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::rest) d) ==>
    MAP expr_type (DROP (LENGTH ats) rest) = MAP (ext_call_kw_type rt) opts /\
    EVERY (well_typed_expr env) (DROP (LENGTH ats) rest)
Proof
  rpt gen_tac >> simp[Once well_typed_expr_def, DROP_def] >>
  strip_tac >> simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  imp_res_tac rich_listTheory.MEM_DROP_IMP >>
  metis_tac[well_typed_exprs_member, MEM]
QED

Theorem extrequest_body_default_type:
  !cenv cx env ann stat skip fname ats rt opts addr rest d es cfn s v gas op dty t.
    expr_body_pre cenv cx env
      (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::rest) d) es /\
    compile_ext_call_kwargs cfn cenv rt opts (DROP (LENGTH ats) rest) s =
      ((v,gas,SOME (op,dty)),t) ==>
    rt <> NoneT /\
    (dty = rt \/ is_bytestring_type dty /\ is_bytestring_type rt)
Proof
  rpt gen_tac >> strip_tac >> drule extrequest_body_typed >> strip_tac >>
  drule extrequest_typed_nonempty >> strip_tac >>
  drule extrequest_typed_kwargs >> strip_tac >>
  `EVERY (\e. ~expr_has_effect e) (DROP (LENGTH ats) rest)` by
    (irule rich_listTheory.EVERY_DROP >> gvs[]) >>
  conj_tac
  >- (strip_tac >> gvs[] >>
      drule_all extrequest_compile_kwargs_no_default >> simp[]) >>
  metis_tac[extrequest_compile_kwargs_default_type]
QED
