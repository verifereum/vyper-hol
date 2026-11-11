(* Syntactic operand safety for unread external-call operands. *)
Theory exprExtRequestOperandSafety
Ancestors
  exprLowering exprLoweringProps exprCallBounds exprOperandVar
  exprSafeOperand exprSafeOperandBuiltins exprSimHypsDefs
  compileEnv context vyperTypeSystem vyperAST emitHelper freshWrites
  builtinSimple builtinMath builtinHashing builtinMisc builtinBytes builtinSystem
  builtinAbi builtinCreate list

Theorem extrequest_type_convert_nonlabel[local]:
  (!l. v <> Label l) /\ compile_type_convert v conv sa = (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `conv` >>
  simp[compile_type_convert_def, compile_int_clamp_def,
       load_bytestring_as_word_def,
       contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt (IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def]) >>
  rpt strip_tac >> gvs[]
QED

fun name_tac g = (
  gvs[well_typed_expr_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  simp[compile_expr_body_def, compile_name_vv_def, comp_return_def,
       vv_operand_def, mk_ptr_def] >> strip_tac >> gvs[vv_operand_def]
) g

and ifexp_tac g = (
  simp[compile_expr_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[AllCaseEqs(), vv_operand_def, mk_ptr_def]
) g

and struct_tac g = (
  simp[compile_expr_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vv_operand_def, base_ptr_def] >>
  metis_tac[alloc_buffer_not_label]
) g

and toplevel_tac g = (
  rename1 `compile_expr_body _ _ _ _ _ (TopLevelName _ nsid) _` >>
  simp[compile_expr_body_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[vv_operand_def, mk_ptr_def] >>
  rename1 `FLOOKUP ce.ce_module_vars nsid = SOME loc` >>
  Cases_on `loc` >> gvs[vv_operand_def, mk_ptr_def]
) g

and pop_tac g = (
  simp[compile_expr_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[CONJUNCT2 (CONJUNCT2 subscript_pop_not_label)]
) g

and expr_builtin_tac g = (
  special_builtin_tac
) g

and expr_type_builtin_tac g = (
  simp[compile_expr_body_def, expr_type_def, Abbr `tf`,
       type_child_callback_def, expr_size_def] >>
  strip_tac >>
  qpat_x_assum `!args ce vt ty tb rt sa. _` irule >>
  goal_assum (drule_at Any) >> simp[expr_size_def] >>
  qexists `env` >> simp[]
) g

and hash_nonlabel_tac facts =
  gvs[AllCaseEqs(), as_stack_val_def, vv_operand_def] >>
  rpt (qmatch_asmsub_abbrev_tac `as_stack_val _ result` >>
       Cases_on `result` >>
       gvs[as_stack_val_def, markerTheory.Abbrev_def, vv_operand_def]) >>
  rpt (pairarg_tac >> gvs[vv_operand_def]) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  qpat_x_assum `well_typed_expr _ _` kall_tac >>
  map_every imp_res_tac (facts @ map GSYM facts) >>
  gvs[safe_operand_def]

and wei_tac g = (
  gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[well_typed_expr_def] >>
  gvs[is_decimal_type_def, is_signed_type_def, as_stack_val_def,
      lower_value_def, comp_bind_def, expr_child_callback_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `!l. vv_operand vv' <> Label l` by
    (first_x_assum irule >> goal_assum (drule_at Any)) >>
  `!l. v <> Label l` by metis_tac[unwrap_value_not_label] >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  simp[compile_as_wei_value_int_def] >> IF_CASES_TAC >>
  simp[as_stack_val_def, comp_return_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[as_stack_val_def, vv_operand_def]
) g

and slice_origin_tac g = (
  gvs[AllCaseEqs(), as_ptr_val_def, vv_operand_def, mk_ptr_def] >>
  rpt (qmatch_asmsub_abbrev_tac `as_ptr_val _ _ result` >>
       Cases_on `result` >>
       gvs[as_ptr_val_def, markerTheory.Abbrev_def, vv_operand_def, mk_ptr_def]) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  gvs[compile_slice_calldata_def, compile_slice_code_def,
      compile_slice_extcode_def, compile_slice_data_def, compile_slice_out_buf_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  metis_tac[alloc_buffer_not_label]
) g

and bop_origin_tac g = (
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  qpat_x_assum `well_typed_expr _ _` kall_tac >>
  rpt (qpat_x_assum `option_CASE (bytestring_literal_hash _) _ _ = _` kall_tac) >>
  gvs[AllCaseEqs(), as_stack_val_def, vv_operand_def] >>
  rpt (qmatch_asmsub_abbrev_tac `as_stack_val _ result` >>
       Cases_on `result` >>
       gvs[as_stack_val_def, markerTheory.Abbrev_def, vv_operand_def]) >>
  rpt (pairarg_tac >> gvs[vv_operand_def]) >>
  rpt (qmatch_asmsub_abbrev_tac `as_stack_val _ result` >>
       Cases_on `result` >>
       gvs[as_stack_val_def, markerTheory.Abbrev_def, vv_operand_def]) >>
  imp_res_tac (GSYM compile_var_array_membership_safe_operand) >>
  imp_res_tac (GSYM compile_list_membership_in_safe_operand) >>
  imp_res_tac (GSYM compile_list_membership_notin_safe_operand) >>
  imp_res_tac (GSYM compile_binop_safe_operand) >>
  imp_res_tac (GSYM emit_op_safe_operand) >>
  imp_res_tac emit_op_safe_operand >>
  gvs[safe_operand_def]
) g

and special_builtin_tac g = (
  `!vv sb. bf ce t ty b l sa = (vv,sb) ==> !lab. vv_operand vv <> Label lab` by
    (simp[Abbr `bf`, builtin_child_callback_def, expr_size_def] >>
     rpt gen_tac >> disch_tac >>
     qpat_x_assum `!args ce rt ty bi sa. _ ==> !vv sb env.
       compile_builtin_dispatch _ _ _ _ _ _ = _ /\ _ ==> _` irule >>
     goal_assum (drule_at Any) >> simp[expr_size_def] >>
     qexists `env` >> simp[]) >>
  rpt (qpat_x_assum `!args ce rt ty bi sa. _` kall_tac) >>
  qpat_x_assum `!e' ce ty sa. _` kall_tac >>
  rpt (qpat_x_assum `Abbrev _` kall_tac) >>
  Cases_on `l` >> simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `h` >> simp[] >>
  qmatch_asmsub_rename_tac `well_typed_expr env (Builtin t b (Name aty a :: tail))` >>
  Cases_on `tail` >> simp[] >>
  qmatch_asmsub_rename_tac `well_typed_expr env (Builtin t b (Name aty a :: hd2 :: tail2))` >>
  Cases_on `hd2` >> simp[] >>
  Cases_on `tail2` >> simp[]
  >- (Cases_on `b` >> simp[] >> named_modular_tac) >>
  qmatch_asmsub_rename_tac `well_typed_expr env
    (Builtin t b (Name aty a :: Name bty bn :: hd3 :: tail3))` >>
  Cases_on `hd3` >> simp[] >>
  Cases_on `tail3` >> simp[] >>
  Cases_on `b` >> simp[] >> named_modular_tac
) g

and named_modular_tac g = (
  rpt strip_tac >>
  gvs[compile_addmod_names_def, compile_mulmod_names_def,
      compile_powmod256_names_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[as_stack_val_def] >>
  rpt (qmatch_asmsub_abbrev_tac `as_stack_val _ result` >>
       Cases_on `result` >>
       gvs[as_stack_val_def, markerTheory.Abbrev_def, vv_operand_def]) >>
  imp_res_tac (GSYM compile_addmod_safe_operand) >>
  imp_res_tac (GSYM compile_mulmod_safe_operand) >>
  imp_res_tac (GSYM compile_pow_mod256_safe_operand) >>
  gvs[safe_operand_def]
) g

and rawlog_tac g = (
  namedCases_on `l` ["", "e1 xs"] >> simp[compile_call_def, LET_THM]
  >- (pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  namedCases_on `xs` ["", "e2 ys"] >> simp[]
  >- (pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  Cases_on `ys` >> simp[] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt (IF_CASES_TAC >> simp[]) >>
  rpt (pairarg_tac >> simp[]) >>
  rpt strip_tac >> gvs[vv_operand_def]
) g

and rawrevert_tac g = (
  namedCases_on `l` ["", "e1 xs"] >> simp[compile_call_def, LET_THM]
  >- (pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  Cases_on `xs` >> simp[] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt strip_tac >> gvs[vv_operand_def]
) g

and send_tac g = (
  namedCases_on `l` ["", "e1 xs"] >> simp[compile_call_def, LET_THM]
  >- (pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  namedCases_on `xs` ["", "e2 ys"] >> simp[]
  >- (pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  IF_CASES_TAC >> simp[]
  >- (rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[vv_operand_def]) >>
  pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]
) g

and create_tac g = (
  simp[compile_call_def] >>
  qmatch_goalsub_abbrev_tac `as_stack_val _ result` >>
  Cases_on `result` >> simp[as_stack_val_def] >>
  rpt strip_tac >> gvs[vv_operand_def, markerTheory.Abbrev_def] >>
  drule (GSYM compile_create_call_safe_operand) >> simp[safe_operand_def]
) g

and raw_finish_tac g = (
  rpt strip_tac >>
  TRY (drule compile_raw_call_finish_zero_safe_operand >> simp[safe_operand_def] >> NO_TAC) >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  rpt (pairarg_tac >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  rpt strip_tac >> gvs[] >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  Cases_on `r.rcf_revert_on_failure` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  TRY (drule alloc_buffer_not_label >> simp[] >> NO_TAC) >>
  qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
) g

;

Theorem extrequest_compiler_nonlabel:
  (!ce ty e sa vv sb env.
     compile_expr ce ty e sa = (vv,sb) /\ well_typed_expr env e /\
     (!id t. FLOOKUP env.var_types id = SOME t ==>
        ?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
     !l. vv_operand vv <> Label l) /\
  (!ce rt ty bi args sa vv sb env.
     compile_builtin_dispatch ce rt ty bi args sa = (vv,sb) /\
     well_typed_expr env (Builtin rt bi args) /\
     (!id t. FLOOKUP env.var_types id = SOME t ==>
        ?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
     !l. vv_operand vv <> Label l) /\
  (!ce vt ty tb rt args sa vv sb env.
     compile_type_builtin_dispatch ce vt ty tb rt args sa = (vv,sb) /\
     well_typed_expr env (TypeBuiltin vt tb rt args) /\
     (!id t. FLOOKUP env.var_types id = SOME t ==>
        ?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
     !l. vv_operand vv <> Label l)
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_raw_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      qmatch_goalsub_abbrev_tac `compile_expr_body f bf tf` >>
      Cases_on `e`
      >~ [`compile_expr_body _ _ _ _ _ (Name _ _) _`] >- name_tac
      >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >- expr_builtin_tac
      >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _`] >- expr_type_builtin_tac
      >~ [`compile_expr_body _ _ _ _ _ (Literal _ _) _`] >-
        (Cases_on `l` >>
         simp[compile_expr_body_def, expr_type_def, compile_literal_vv_def, comp_return_def] >>
         rpt (BasicProvers.TOP_CASE_TAC >> simp[comp_bind_def, comp_return_def]) >>
         simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def,
              comp_return_def, LET_THM] >>
         rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
         gvs[vv_operand_def, base_ptr_def] >>
         TRY (rename1 `compile_literal_vv _ (BoolL b) _ = _` >>
              Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def, vv_operand_def] >> NO_TAC) >>
         metis_tac[alloc_buffer_not_label])
      >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >- ifexp_tac
      >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _`] >- struct_tac
      >~ [`compile_expr_body _ _ _ _ _ (TopLevelName _ _) _`] >- toplevel_tac
      >~ [`compile_expr_body _ _ _ _ _ (Pop _ _) _`] >- pop_tac
      >~ [`compile_expr_body _ _ _ _ _ (Call _ _ _ _) _`] >-
        (simp[compile_expr_body_def, LET_THM] >> Cases_on `c`
         >~ [`compile_call _ _ _ _ (IntCall _) _ _ _`] >-
           metis_tac[compile_internal_call_not_label]
         >~ [`compile_call _ _ _ _ (ExtCall _ _ _ _) _ _ _`] >-
           (rename1 `ExtCall _ _ sig _` >> PairCases_on `sig` >>
            simp[compile_call_def, LET_THM] >>
            BasicProvers.TOP_CASE_TAC >> simp[LET_THM] >>
            rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
            gvs[AllCaseEqs(), vv_operand_def, mk_ptr_def] >>
            metis_tac[compile_external_call_not_label]) >>
         all_tac
         >~ [`compile_call _ _ _ _ RawLog _ _ _`] >- rawlog_tac
         >~ [`compile_call _ _ _ _ RawRevert _ _ _`] >- rawrevert_tac
         >~ [`compile_call _ _ _ _ SelfDestructTarget _ _ _`] >-
           (simp[compile_call_def, LET_THM] >> pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def])
         >~ [`compile_call _ _ _ _ (Send _) _ _ _`] >- send_tac
         >~ [`compile_call _ _ _ _ (RawCallTarget _) _ _ _`] >-
           (namedCases_on `l` ["", "e1 xs"] >> simp[compile_call_def, LET_THM]
            >- (pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
            namedCases_on `xs` ["", "e2 ys"] >> simp[]
            >- (pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
            rpt (pairarg_tac >> simp[]) >>
            rpt (IF_CASES_TAC >> simp[]) >>
            rpt strip_tac >> gvs[vv_operand_def, mk_ptr_def, base_ptr_def] >>
            raw_finish_tac)
         >~ [`compile_call _ _ _ _ (RawCallCalldataTarget _) _ _ _`] >-
           (namedCases_on `l` ["", "e1 xs"] >> simp[compile_call_def, LET_THM]
            >- (pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
            rpt (pairarg_tac >> simp[]) >>
            rpt (IF_CASES_TAC >> simp[]) >>
            rpt strip_tac >> gvs[vv_operand_def, mk_ptr_def, base_ptr_def] >> raw_finish_tac) >>
         create_tac) >>
      simp[compile_expr_body_def, LET_THM] >> rpt strip_tac
      >~ [`compile_attribute _ _ _ _ _ _ _ = _`] >-
        (drule compile_attribute_safe_operand >> simp[safe_operand_def])
      >~ [`compile_subscript _ _ _ _ _ _ _ = _`] >-
        (drule compile_subscript_not_label >> simp[]) >>
      gvs[vv_operand_def])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_raw_def] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      qmatch_goalsub_abbrev_tac `compile_builtin_dispatch_body f` >>
      `!e ty s vv sb. MEM e args /\ well_typed_expr env e /\
         f ce ty e s = (vv,sb) ==> !l. vv_operand vv <> Label l` by
        (rpt gen_tac >> strip_tac >>
         `expr_size e < list_size expr_size args` by
           metis_tac[expr_list_member_bound] >>
         gvs[Abbr `f`, expr_child_callback_def] >>
         first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
         metis_tac[]) >>
      Cases_on `bi` >>
      simp[compile_builtin_dispatch_body_def, LET_THM, as_stack_val_def, as_ptr_val_def] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
      gvs[vv_operand_def, mk_ptr_def, base_ptr_def] >>
      rpt strip_tac >>
      gvs[as_stack_val_def, as_ptr_val_def] >>
      rpt (pairarg_tac >> gvs[as_stack_val_def, as_ptr_val_def, vv_operand_def, mk_ptr_def]) >>
      TRY (qmatch_asmsub_abbrev_tac `as_stack_val _ result` >>
           Cases_on `result` >>
           gvs[as_stack_val_def, markerTheory.Abbrev_def, vv_operand_def]) >>
      TRY (qmatch_asmsub_abbrev_tac `as_ptr_val _ _ result` >>
           Cases_on `result` >>
           gvs[as_ptr_val_def, markerTheory.Abbrev_def, vv_operand_def, mk_ptr_def]) >>
      qpat_x_assum `well_typed_expr _ (Builtin _ _ _)` mp_tac
      >~ [`well_typed_expr _ (Builtin _ (Acc acc) _)`] >-
        (disch_tac >> Cases_on `acc` >>
         gvs[compile_acc_def, lower_value_def, comp_bind_def, LET_THM] >>
         rpt (pairarg_tac >> gvs[]) >-
           (gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
            Cases_on `args` >> gvs[well_typed_expr_def] >>
            `!l. vv_operand vv <> Label l` by
              (qpat_x_assum `!ty s vv' sb'. _` drule >> simp[]) >>
            qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
            drule_all unwrap_value_not_label >> simp[]) >>
         qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule exprSafeOperandTheory.emit_op_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ (Env e) _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_env_var_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ Keccak256 _)`] >-
        (disch_tac >> hash_nonlabel_tac [compile_keccak256_word_safe_operand,
          compile_keccak256_bytes_safe_operand, compile_keccak256_bytesm_safe_operand])
      >~ [`well_typed_expr _ (Builtin _ Sha256 _)`] >-
        (disch_tac >> hash_nonlabel_tac [compile_sha256_word_safe_operand,
          compile_sha256_bytes_safe_operand, compile_sha256_bytesm_safe_operand])
      >~ [`well_typed_expr _ (Builtin _ MethodId _)`] >-
        (disch_tac >> gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
         gvs[AllCaseEqs(), vv_operand_def] >>
         gvs[compile_method_id_runtime_def, compile_literal_vv_def,
             compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def,
             comp_return_def, LET_THM] >>
         rpt (pairarg_tac >> gvs[vv_operand_def, base_ptr_def]) >>
         rpt (qpat_x_assum `!x. _` kall_tac) >>
         imp_res_tac emit_op_safe_operand >> gvs[safe_operand_def] >>
         drule exprSafeOperandTheory.alloc_buffer_not_label >> simp[] >> metis_tac[])
      >~ [`well_typed_expr _ (Builtin _ Neg _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_neg_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ Abs _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_builtin_abs_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ BlobHash _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_blobhash_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ BlockHash _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_blockhash_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ Ceil _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_ceil_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ Floor _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_floor_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ Len _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_builtin_len_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ PowMod256 _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_pow_mod256_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ AddMod _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_addmod_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ MulMod _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_mulmod_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ Not _)`] >-
        (disch_tac >> gvs[AllCaseEqs(), as_stack_val_def, vv_operand_def] >>
         rpt (qmatch_asmsub_abbrev_tac `as_stack_val _ result` >>
              Cases_on `result` >> gvs[as_stack_val_def, markerTheory.Abbrev_def, vv_operand_def]) >>
         TRY (qpat_x_assum `pair = compile_invert x at ce st` (assume_tac o SYM)) >>
         TRY (qpat_x_assum `pair = emit_op opc operands st` (assume_tac o SYM)) >>
         imp_res_tac compile_invert_safe_operand >>
         imp_res_tac emit_op_safe_operand >> gvs[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ (AsWeiValue d) _)`] >- (disch_tac >> wei_tac) >>
      all_tac
      >~ [`well_typed_expr _ (Builtin _ ECMul _)`] >-
        (disch_tac >> metis_tac[CONJUNCT2 ec_arith_result_not_label])
      >~ [`well_typed_expr _ (Builtin _ ECAdd _)`] >-
        (disch_tac >> metis_tac[CONJUNCT1 ec_arith_result_not_label])
      >~ [`well_typed_expr _ (Builtin _ (Concat n) _)`] >-
        (disch_tac >> metis_tac[alloc_buffer_not_label])
      >~ [`well_typed_expr _ (Builtin _ (CalldataSlice n) _)`] >-
        (disch_tac >> gvs[compile_slice_calldata_def, compile_slice_out_buf_def,
             comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
         rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
         metis_tac[alloc_buffer_not_label])
      >~ [`well_typed_expr _ (Builtin _ (Uint2Str n) _)`] >-
        (disch_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
         qpat_x_assum `well_typed_expr _ _` kall_tac >>
         gvs[builtinStringsTheory.compile_uint2str_def, comp_bind_def,
             comp_ignore_bind_def, comp_return_def] >>
         ntac 10 (pairarg_tac >> gvs[]) >>
         ntac 10 (pairarg_tac >> gvs[]) >>
         ntac 10 (pairarg_tac >> gvs[]) >>
         rpt (pairarg_tac >> gvs[]))
      >~ [`well_typed_expr _ (Builtin _ ECRecover _)`] >-
        (disch_tac >> qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule compile_ecrecover_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ (MakeArray o' b) _)`] >-
        (disch_tac >> gvs[AllCaseEqs(), as_ptr_val_def, vv_operand_def, mk_ptr_def] >>
         rpt (qmatch_asmsub_abbrev_tac `as_ptr_val _ _ result` >>
              Cases_on `result` >>
              gvs[as_ptr_val_def, markerTheory.Abbrev_def, vv_operand_def, mk_ptr_def]) >>
         rpt (qpat_x_assum `!x. _` kall_tac) >>
         imp_res_tac (GSYM compiler_make_tuple_result) >>
         imp_res_tac (GSYM compiler_make_array_result) >> gvs[] >>
         metis_tac[alloc_buffer_not_label])
      >~ [`well_typed_expr _ (Builtin _ CalldataLen _)`] >-
        (disch_tac >> gvs[compile_builtin_calldatasize_def, comp_bind_def, comp_return_def] >>
         qpat_x_assum `(Label l,r) = _` (assume_tac o SYM) >>
         drule emit_op_safe_operand >> simp[safe_operand_def])
      >~ [`well_typed_expr _ (Builtin _ (Bop b) _)`] >- (disch_tac >> bop_origin_tac) >>
      disch_tac >> slice_origin_tac)
  >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_builtin_dispatch _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  qmatch_goalsub_abbrev_tac `compile_type_builtin_dispatch_body f` >>
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM, as_stack_val_def, as_ptr_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[vv_operand_def, mk_ptr_def, base_ptr_def] >>
  qpat_x_assum `well_typed_expr _ (TypeBuiltin _ _ _ _)` mp_tac
  >~ [`well_typed_expr _ (TypeBuiltin _ Convert _ _)`] >-
    (disch_tac >> gvs[well_typed_expr_def, well_typed_type_builtin_args_def] >>
     Cases_on `args` >> gvs[well_typed_expr_def] >>
     gvs[Abbr `f`, lower_value_def, comp_bind_def, expr_child_callback_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     `!l. vv_operand vv' <> Label l` by
       (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
        qexists `env` >> simp[]) >>
     `!l. v <> Label l` by metis_tac[unwrap_value_not_label] >>
     rpt (qpat_x_assum `!x. _ ==> _` kall_tac) >>
     gvs[AllCaseEqs(), as_stack_val_def, vv_operand_def] >>
     rpt (qmatch_asmsub_abbrev_tac `as_stack_val _ result` >>
          Cases_on `result` >>
          gvs[as_stack_val_def, markerTheory.Abbrev_def, vv_operand_def]) >>
     TRY (qpat_x_assum `_ = compile_type_convert _ _ _` (assume_tac o SYM) >>
          drule_all extrequest_type_convert_nonlabel >> simp[] >> NO_TAC) >>
     gvs[compile_bytestring_widen_copy_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> metis_tac[alloc_buffer_not_label]) >>
  disch_tac >>
  gvs[AllCaseEqs(), as_stack_val_def, as_ptr_val_def, vv_operand_def, mk_ptr_def] >>
  rpt (qmatch_asmsub_abbrev_tac `as_stack_val _ result` >>
       Cases_on `result` >> gvs[as_stack_val_def, markerTheory.Abbrev_def, vv_operand_def]) >>
  rpt (qmatch_asmsub_abbrev_tac `as_ptr_val _ _ result` >>
       Cases_on `result` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def, vv_operand_def, mk_ptr_def]) >>
  TRY (drule compile_empty_not_label >> simp[] >> NO_TAC) >>
  TRY (drule (GSYM lower_abi_decode_not_label) >> simp[] >> NO_TAC) >>
  qpat_x_assum `well_typed_expr _ (TypeBuiltin _ _ _ _)` mp_tac
  >~ [`well_typed_expr _ (TypeBuiltin _ Extract32 _ _)`] >-
    (disch_tac >> imp_res_tac (GSYM compile_clamp_basetype_returns) >> gvs[] >>
     drule compile_extract32_load_safe_operand >> simp[safe_operand_def]) >>
  disch_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
  gvs[lower_abi_encode_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  metis_tac[alloc_buffer_not_label]
QED

(* This helper must remain independent of the admitted seam interfaces. *)
val _ =
  if List.exists (fn s => s <> "DISK_THM")
       (#1 (Tag.dest_tag (Thm.tag extrequest_compiler_nonlabel)))
     orelse not (null (Thm.hyp extrequest_compiler_nonlabel))
  then raise Fail "extrequest_compiler_nonlabel: unclosed proof"
  else ();
