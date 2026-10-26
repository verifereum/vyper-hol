(*
 * The operand lowering hands out for a word-typed expression (#636)
 *
 * For a well-typed word expression (with well-formed local types)
 * compile_expr returns a word_result_ok value (exprSafeOperand): a
 * StackValue whose operand is a literal or a variable it already handed
 * out, or a LocatedValue of word type, which unwrap_value loads into a
 * fresh variable.  Without the typing hypotheses a conversion that returns
 * its operand as is (ConvIdentity, ConvBytesMToBytesM) could pass a
 * pointer from cenv through.
 *
 * TOP-LEVEL:
 *   compile_expr_word_result — by induction over compile_expr, for
 *                              compile_expr and both builtin dispatchers
 *   lower_value_word_safe_operand — the operand of lower_value compile_expr
 *                              (exprSimOperators' lower_value_word_shape)
 *
 * Helpers: the word_* lemmas, one per case of compile_expr_body and the
 *   builtin dispatch bodies.
 *)

Theory exprWordOperand
Ancestors
  exprSafeOperand exprSafeOperandBuiltins
  exprLoweringProps freshWrites compileEnv emitHelper context
  exprLowering exprCallBounds vyperTypeSystem vyperValue vyperAST vyperTypeBuiltins
  builtinSimple builtinMath builtinHashing builtinMisc builtinBytes builtinSystem

(* ===== The cases of compile_expr_body and the dispatchers ===== *)

Theorem word_compile_expr_toplevelname:
  is_word_type ann /\
  compile_expr_body f g h cenv ty (TopLevelName ann nsid) sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  Cases_on `FLOOKUP cenv.ce_vars (module_var_key nsid)` >> simp[] >-
    (strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  rename1 `FLOOKUP cenv.ce_vars _ = SOME bnd` >> Cases_on `bnd` >> simp[] >>
  strip_tac >>
  rpt (pairarg_tac >> gvs[word_result_ok_def]) >> gvs[word_result_ok_def]
QED

Theorem word_compile_expr_pop:
  is_word_type ann /\
  compile_expr_body f g h cenv ty (Pop ann target) sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `target` >> simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Theorem word_compile_expr_structlit:
  is_word_type ann /\
  compile_expr_body f g h cenv ty (StructLit ann name fields) sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Theorem word_compile_expr_ifexp:
  (!ce t e s r s'. lower_value f ce t e s = (r,s') ==>
                   s.cs_next_var <= s'.cs_next_var) /\
  is_word_type ann /\
  compile_expr_body f g h cenv ty (IfExp ann cond_e then_e else_e) sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[word_result_ok_def] >>
  imp_res_tac fresh_var_safe_operand >>
  irule safe_operand_mono >> goal_assum (drule_at Any) >>
  qpat_x_assum `!ce t e s r s'. _` (fn th => imp_res_tac th) >>
  gvs[fresh_label_def, emit_inst_def, fresh_id_def, emit_def,
      new_block_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem word_type_builtin_nonconvert:
  tb <> Convert /\
  type_builtin_result_ok tenv tb vt rt (MAP expr_type args) /\
  is_word_type vt /\
  compile_type_builtin_dispatch_body f cenv vt ty tb rt args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `tb` >>
  simp[type_builtin_result_ok_def, compile_type_builtin_dispatch_body_def,
       LET_THM, is_word_type_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[word_result_ok_def]
  >~ [`as_stack_val rt (compile_clamp_extract32 raw clamp st3) = _`] >-
    (irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
     rpt strip_tac >> drule_all compile_extract32_safe_operand >>
     strip_tac >> metis_tac[compile_clamp_extract32_safe_operand])
  >~ [`as_ptr_val _ _ _ = _`] >- metis_tac[as_ptr_val_word_result_ok] >>
  gvs[is_word_type_def]
QED

Theorem word_type_builtin_convert:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
       is_word_type (expr_type e) /\ lower_value f cenv t e s = (op,s') ==>
       safe_operand s' op) /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  well_typed_expr env (TypeBuiltin vt Convert rt args) /\
  is_word_type vt /\
  compile_type_builtin_dispatch_body f cenv vt ty Convert rt args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[well_typed_expr_def, well_typed_type_builtin_args_def,
       type_builtin_result_ok_def] >>
  Cases_on `args` >> simp[] >>
  rename1 `compile_type_builtin_dispatch_body _ _ _ _ _ _ (arg :: rest)` >>
  Cases_on `rest` >> simp[] >>
  rpt strip_tac >> gvs[well_typed_expr_def] >>
  `well_formed_type env.type_defs (expr_type arg)` by
    metis_tac[well_typed_expr_type_well_formed] >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `rt` >> gvs[is_word_type_def]
  >~ [`FlagT flag_nsid`] >-
    (`is_word_type (expr_type arg)` by
       (Cases_on `expr_type arg` >> gvs[valid_conversion_def, is_word_type_def] >>
        rename1 `BaseT bt` >> Cases_on `bt` >>
        gvs[valid_conversion_def, is_word_type_def]) >>
     `safe_operand st1 v` by metis_tac[] >>
     irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
     metis_tac[compile_type_convert_safe_input]) >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  rpt strip_tac >> irule compile_type_convert_word_safe >>
  goal_assum (drule_at Any) >> qexists_tac `env.type_defs` >>
  simp[] >> metis_tac[]
QED

Theorem word_builtin_scalar:
  (bi = Not \/ bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
   bi = Ceil \/ bi = Floor \/ bi = AddMod \/ bi = MulMod \/ bi = PowMod256 \/
   bi = ECRecover \/ bi = CalldataLen \/ (?item. bi = Env item)) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  metis_tac[emit_op_safe_operand, compile_invert_safe_operand,
    compile_neg_safe_operand, compile_builtin_abs_safe_operand,
    compile_blockhash_safe_operand, compile_blobhash_safe_operand,
    compile_ceil_safe_operand, compile_floor_safe_operand,
    compile_addmod_safe_operand, compile_mulmod_safe_operand,
    compile_pow_mod256_safe_operand, compile_ecrecover_safe_operand,
    compile_builtin_calldatasize_safe_operand, compile_env_var_safe_operand]
QED

Theorem word_builtin_hash:
  (bi = Keccak256 \/ bi = Sha256) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  metis_tac[compile_keccak256_bytes_safe_operand,
    compile_keccak256_bytesm_safe_operand, compile_keccak256_word_safe_operand,
    compile_sha256_bytes_safe_operand, compile_sha256_bytesm_safe_operand,
    compile_sha256_word_safe_operand]
QED

Theorem word_builtin_located:
  ((?n. bi = CalldataSlice n) \/ bi = ECAdd \/ bi = ECMul \/
   (?n. bi = Concat n) \/ (?n. bi = Slice n) \/ (?n. bi = Uint2Str n) \/
   (?et bd. bi = MakeArray et bd)) /\ is_word_type vt /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), word_result_ok_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[as_ptr_val_word_result_ok]
QED

Theorem word_builtin_method_id:
  is_word_type vt /\
  compile_builtin_dispatch_body f cenv vt ty MethodId args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[compile_literal_vv_word_result_ok]
  >~ [`as_ptr_val _ _ _ = _`] >- metis_tac[as_ptr_val_word_result_ok] >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  metis_tac[compile_method_id_word_safe_operand]
QED

Theorem word_builtin_len:
  compile_builtin_dispatch_body f cenv vt ty Len args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  metis_tac[compile_builtin_calldatasize_safe_operand, compile_builtin_len_safe_operand]
QED

Theorem word_builtin_bop:
  compile_builtin_dispatch_body f cenv vt ty (Bop bop) args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  metis_tac[compile_binop_safe_operand, emit_op_safe_operand,
    compile_list_membership_in_safe_operand, compile_list_membership_notin_safe_operand,
    compile_var_array_membership_safe_operand]
QED

Theorem word_builtin_acc:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
       is_word_type (expr_type e) /\ lower_value f cenv t e s = (op,s') ==>
       safe_operand s' op) /\
  well_typed_expr env (Builtin vt (Acc item) args) /\
  compile_builtin_dispatch_body f cenv vt ty (Acc item) args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[] >>
  rename1 `compile_builtin_dispatch_body _ _ _ _ _ (_ :: rest)` >>
  Cases_on `rest` >> simp[] >>
  rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  drule_at (Pos last) compile_acc_safe_operand >>
  gvs[well_typed_expr_def, is_word_type_def] >> metis_tac[]
QED

Theorem word_builtin_as_wei_value:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
       is_word_type (expr_type e) /\ lower_value f cenv t e s = (op,s') ==>
       safe_operand s' op) /\
  well_typed_expr env (Builtin vt (AsWeiValue denom) args) /\
  compile_builtin_dispatch_body f cenv vt ty (AsWeiValue denom) args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[] >>
  rename1 `compile_builtin_dispatch_body _ _ _ _ _ (_ :: rest)` >>
  Cases_on `rest` >> simp[] >>
  rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, LET_THM,
      well_typed_expr_def, is_uint_type_def, is_word_type_def, is_decimal_type_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `safe_operand st1 v` by metis_tac[] >>
  metis_tac[compile_as_wei_value_int_safe_operand]
QED

Theorem word_builtin_dispatch_body:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
       is_word_type (expr_type e) /\ lower_value f cenv t e s = (op,s') ==>
       safe_operand s' op) /\
  well_typed_expr env (Builtin vt bi args) /\ is_word_type vt /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `bi` >> rpt strip_tac
  >~ [`Bop bop`] >- metis_tac[word_builtin_bop]
  >~ [`Acc item`] >- (irule word_builtin_acc >> goal_assum (drule_at Any) >> metis_tac[])
  >~ [`AsWeiValue denom`] >-
    (irule word_builtin_as_wei_value >> goal_assum (drule_at Any) >> metis_tac[])
  >~ [`Len`] >- metis_tac[word_builtin_len]
  >~ [`MethodId`] >- metis_tac[word_builtin_method_id]
  >> metis_tac[word_builtin_scalar, word_builtin_hash, word_builtin_located]
QED

Theorem word_type_builtin_dispatch_body:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
       is_word_type (expr_type e) /\ lower_value f cenv t e s = (op,s') ==>
       safe_operand s' op) /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  well_typed_expr env (TypeBuiltin vt tb rt args) /\ is_word_type vt /\
  compile_type_builtin_dispatch_body f cenv vt ty tb rt args sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `tb = Convert` >> rpt strip_tac >-
    (gvs[] >> irule word_type_builtin_convert >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  irule word_type_builtin_nonconvert >> goal_assum (drule_at Any) >>
  gvs[well_typed_expr_def] >> metis_tac[]
QED

Theorem word_compile_named_modular:
  (!ce rt at a bt b mt m s vv s'.
    compile_addmod_names ce rt at a bt b mt m s = (vv,s') ==> word_result_ok s' vv) /\
  (!ce rt at a bt b mt m s vv s'.
    compile_mulmod_names ce rt at a bt b mt m s = (vv,s') ==> word_result_ok s' vv) /\
  (!ce rt at a bt b s vv s'.
    compile_powmod256_names ce rt at a bt b s = (vv,s') ==> word_result_ok s' vv)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_addmod_names_def, compile_mulmod_names_def,
       compile_powmod256_names_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  irule as_stack_val_word_result_ok >> goal_assum (drule_at Any) >>
  metis_tac[compile_addmod_safe_operand, compile_mulmod_safe_operand,
            compile_pow_mod256_safe_operand]
QED

(* ===== The induction ===== *)

Theorem word_list_result_elim[local]:
  (list_CASE xs n c = r ==> Q) <=>
  (xs = [] ==> n = r ==> Q) /\
  (!h t. xs = h::t ==> c h t = r ==> Q)
Proof
  Cases_on `xs` >> simp[]
QED

Theorem word_expr_result_elim[local]:
  (expr_CASE e f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 = r ==> Q) <=>
  (!a b. e = Name a b ==> f1 a b = r ==> Q) /\
  (!a b. e = TopLevelName a b ==> f2 a b = r ==> Q) /\
  (!a b c. e = FlagMember a b c ==> f3 a b c = r ==> Q) /\
  (!a b c d. e = IfExp a b c d ==> f4 a b c d = r ==> Q) /\
  (!a b. e = Literal a b ==> f5 a b = r ==> Q) /\
  (!a b c. e = StructLit a b c ==> f6 a b c = r ==> Q) /\
  (!a b c. e = Subscript a b c ==> f7 a b c = r ==> Q) /\
  (!a b c. e = Attribute a b c ==> f8 a b c = r ==> Q) /\
  (!a b c. e = Builtin a b c ==> f9 a b c = r ==> Q) /\
  (!a b c d. e = TypeBuiltin a b c d ==> f10 a b c d = r ==> Q) /\
  (!a b. e = Pop a b ==> f11 a b = r ==> Q) /\
  (!a b c d. e = Call a b c d ==> f12 a b c d = r ==> Q)
Proof
  Cases_on `e` >> simp[]
QED

Theorem word_compile_expr_builtin_classify:
  compile_expr_body f g h cenv ty (Builtin ann bi args) sa = (vv,sb) ==>
  g cenv ann ty bi args sa = (vv,sb) \/ word_result_ok sb vv
Proof
  Cases_on `bi` >>
  simp[compile_expr_body_def, expr_type_def, LET_THM,
       word_list_result_elim, word_expr_result_elim] >>
  rpt strip_tac >>
  metis_tac[word_compile_named_modular]
QED

Theorem word_compile_expr_builtin:
  (!ann bi args s vv s'.
    well_typed_expr env (Builtin ann bi args) /\ is_word_type ann /\
    g cenv ann ty bi args s = (vv,s') ==> word_result_ok s' vv) /\
  well_typed_expr env (Builtin ann bi args) /\ is_word_type ann /\
  compile_expr_body f g h cenv ty (Builtin ann bi args) sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  rpt strip_tac >> drule word_compile_expr_builtin_classify >>
  strip_tac >> metis_tac[]
QED

Theorem word_compile_expr_body:
  (!ce t e s r s'. lower_value f ce t e s = (r,s') ==>
                   s.cs_next_var <= s'.cs_next_var) /\
  (!ann bi args s vv s'.
    well_typed_expr env (Builtin ann bi args) /\ is_word_type ann /\
    g cenv ann ty bi args s = (vv,s') ==> word_result_ok s' vv) /\
  (!ann tb rt args s vv s'.
    well_typed_expr env (TypeBuiltin ann tb rt args) /\ is_word_type ann /\
    h cenv ann ty tb rt args s = (vv,s') ==> word_result_ok s' vv) /\
  well_typed_expr env e /\ is_word_type (expr_type e) /\
  compile_expr_body f g h cenv ty e sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `e` >> rpt strip_tac
  >~ [`Builtin ann bi args`] >-
    (irule word_compile_expr_builtin >> goal_assum (drule_at Any) >>
     qexists_tac `env` >> gvs[expr_type_def] >> first_assum ACCEPT_TAC)
  >~ [`TopLevelName ann nsid`] >- metis_tac[word_compile_expr_toplevelname, expr_type_def]
  >~ [`Pop ann target`] >- metis_tac[word_compile_expr_pop, expr_type_def]
  >~ [`StructLit ann name fields`] >- metis_tac[word_compile_expr_structlit, expr_type_def]
  >~ [`IfExp ann cond_e then_e else_e`] >-
    (irule word_compile_expr_ifexp >> goal_assum (drule_at Any) >>
     gvs[expr_type_def] >> first_assum ACCEPT_TAC) >>
  gvs[compile_expr_body_def, expr_type_def, LET_THM]
  >~ [`compile_name_vv _ _ _ _ = _`] >- metis_tac[compile_name_vv_word_result_ok]
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[compile_literal_vv_word_result_ok]
  >~ [`compile_subscript _ _ _ _ _ _ _ = _`] >- metis_tac[compile_subscript_word_result_ok]
  >~ [`compile_attribute _ _ _ _ _ _ _ = _`] >- metis_tac[compile_attribute_word_result_ok]
  >~ [`compile_call _ _ _ _ _ _ _ _ = _`] >- metis_tac[compile_call_word_result_ok]
  >~ [`h cenv _ ty _ _ _ sa = (vv,sb)`] >-
    (qpat_x_assum `!ann tb rt args s vv s'. _` drule_all >> simp[]) >>
  gvs[word_result_ok_def] >> rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Theorem word_lower_value_child_grows[local]:
  lower_value (expr_child_callback bound compile_expr) ce ty e sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `expr_size e < bound` >-
    (`lower_value (expr_child_callback bound compile_expr) ce ty e sa =
      lower_value compile_expr ce ty e sa` by
       simp[lower_value_def, comp_bind_def] >>
     metis_tac[cj 2 compile_expr_grows]) >>
  simp[lower_value_def, expr_child_callback_def, invalid_expr_call_def,
       comp_bind_def, comp_return_def, unwrap_value_def, emit_inst_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem word_lower_value_child_safe[local]:
  lower_value (expr_child_callback bound cfn) ce ty e sa = (op,sb) ==>
  (!e ce ty s vv s'. expr_size e < bound /\ cfn ce ty e s = (vv,s') /\
      well_typed_expr env e /\ is_word_type (expr_type e) ==> word_result_ok s' vv) ==>
  well_typed_expr env e ==> is_word_type (expr_type e) ==>
  safe_operand sb op
Proof
  Cases_on `expr_size e < bound` >>
  simp[lower_value_def, comp_bind_def, invalid_expr_call_def,
       unwrap_value_def, comp_return_def, LET_THM] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >-
    (qpat_x_assum `!e ce ty s vv s'. _` drule_all >>
     metis_tac[unwrap_value_safe_operand]) >>
  gvs[unwrap_value_def, comp_return_def]
QED

Theorem compile_expr_word_result:
  (!cenv ty e sa env vv sb.
    compile_expr cenv ty e sa = (vv,sb) /\ well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t) /\
    is_word_type (expr_type e) ==> word_result_ok sb vv) /\
  (!cenv ann ty bi args sa env vv sb.
    compile_builtin_dispatch cenv ann ty bi args sa = (vv,sb) /\
    well_typed_expr env (Builtin ann bi args) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t) /\
    is_word_type ann ==> word_result_ok sb vv) /\
  (!cenv ann ty tb rt args sa env vv sb.
    compile_type_builtin_dispatch cenv ann ty tb rt args sa = (vv,sb) /\
    well_typed_expr env (TypeBuiltin ann tb rt args) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t) /\
    is_word_type ann ==> word_result_ok sb vv)
Proof
  ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume compile_expr_word_result[expr]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule word_compile_expr_body >> goal_assum (drule_at (Pat `compile_expr_body`)) >>
  qexists_tac `env` >>
  conj_tac >- (rpt strip_tac >> drule word_lower_value_child_grows >> simp[]) >>
  simp[] >> conj_tac >-
    (rpt gen_tac >> simp[builtin_child_callback_def] >>
     Cases_on `list_size expr_size args < expr_size e` >> simp[] >-
       metis_tac[] >>
     simp[invalid_expr_call_def, LET_THM] >> strip_tac >>
     rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  rpt gen_tac >> simp[type_child_callback_def] >>
  Cases_on `list_size expr_size args < expr_size e` >> simp[] >-
    metis_tac[] >>
  simp[invalid_expr_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Resume compile_expr_word_result[builtin]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule word_builtin_dispatch_body >>
  goal_assum (drule_at (Pat `compile_builtin_dispatch_body`)) >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >>
  drule word_lower_value_child_safe >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >-
     (conj_tac >- (qx_gen_tac `arg` >> rpt gen_tac >> strip_tac >>
                   qpat_x_assum `!e cenv ty sa. _` (qspec_then `arg` mp_tac) >>
                   simp[] >> disch_then drule_all >> simp[]) >>
      simp[])) >> simp[]
QED
Resume compile_expr_word_result[type_builtin]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule word_type_builtin_dispatch_body >>
  goal_assum (drule_at (Pat `compile_type_builtin_dispatch_body`)) >>
  qexists_tac `env` >> simp[] >> conj_tac >-
    (rpt strip_tac >> drule word_lower_value_child_safe >>
     disch_then (qspec_then `env` mp_tac) >>
     (impl_tac >-
        (conj_tac >- (qx_gen_tac `arg` >> rpt gen_tac >> strip_tac >>
                      qpat_x_assum `!e cenv ty sa. _` (qspec_then `arg` mp_tac) >>
                      simp[] >> disch_then drule_all >> simp[]) >>
         simp[])) >> simp[]) >>
  first_assum ACCEPT_TAC
QED
Finalise compile_expr_word_result

Theorem lower_value_word_safe_operand:
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t) /\
  is_word_type (expr_type e) ==> safe_operand sb op
Proof
  simp[lower_value_def, comp_bind_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  drule (cj 1 compile_expr_word_result) >>
  disch_then (qspec_then `env` mp_tac) >>
  simp[] >> metis_tac[unwrap_value_safe_operand]
QED
