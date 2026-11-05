(* Typed compiler output operands, independently of global environment shape. *)
Theory exprTypedOperand
Ancestors
  exprWordOperand exprSafeOperand exprSafeOperandBuiltins
  exprLoweringProps freshWrites compileEnv emitHelper context
  exprLowering exprCallBounds vyperTypeSystem vyperValue vyperAST vyperTypeBuiltins
  builtinSimple builtinMath builtinHashing builtinMisc builtinBytes builtinSystem
  builtinStrings

(* unwrap_value_not_label is the shared, type-independent unwrap boundary. *)
Theorem lower_value_not_label:
  (!ce t e s vv s'. f ce t e s = (vv,s') /\ well_typed_expr env e ==>
     !l. vv_operand vv <> Label l) /\
  well_typed_expr env e /\ lower_value f ce t e sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[lower_value_def, comp_bind_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[unwrap_value_not_label]
QED

Theorem lower_value_child_not_label:
  (!e t s vv s'. expr_size e < bound /\ f ce t e s = (vv,s') /\
     well_typed_expr env e ==> !l. vv_operand vv <> Label l) /\
  well_typed_expr env e /\
  lower_value (expr_child_callback bound f) ce t e sa = (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `expr_size e < bound`
  >- (simp[lower_value_def, expr_child_callback_def, comp_bind_def] >>
      rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
      qpat_x_assum `!e t s vv s'. _` drule_all >>
      strip_tac >> drule_all unwrap_value_not_label >> simp[]) >>
  simp[lower_value_def, expr_child_callback_def, invalid_expr_call_def,
       comp_bind_def, comp_return_def, unwrap_value_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[unwrap_value_def, comp_return_def]
QED

Theorem compile_expr_toplevelname_not_label[local]:
  compile_expr_body f g h ce ty (TopLevelName ann nsid) sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[]
  >- (strip_tac >> rpt (pairarg_tac >> gvs[vv_operand_def, mk_ptr_def])) >>
  rename1 `FLOOKUP ce.ce_module_vars _ = SOME bnd` >> Cases_on `bnd` >> simp[] >>
  strip_tac >> rpt (pairarg_tac >> gvs[vv_operand_def, mk_ptr_def]) >>
  gvs[vv_operand_def, mk_ptr_def]
QED

Theorem compile_expr_ifexp_not_label[local]:
  compile_expr_body f g h ce ty (IfExp ann c a b) sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[vv_operand_def, mk_ptr_def, fresh_var_def, fresh_id_def,
      comp_bind_def, comp_return_def] >>
  Cases_on `is_word_type ann` >> gvs[vv_operand_def, mk_ptr_def]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Typed operand helper dependency" else ()
  end) [lower_value_not_label, lower_value_child_not_label,
         compile_expr_toplevelname_not_label, compile_expr_ifexp_not_label];

Theorem compile_expr_pop_not_label[local]:
  compile_expr_body f g h ce ty (Pop ann target) sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[cj 3 subscript_pop_not_label]
QED

Theorem compile_expr_structlit_not_label[local]:
  compile_expr_body f g h ce ty (StructLit ann name fields) sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[vv_operand_def, base_ptr_def] >> metis_tac[alloc_buffer_not_label]
QED

Theorem compile_bytelike_literal_not_label[local]:
  compile_bytelike_literal bs mx sa = (buf,sb) ==> !l. buf.buf_operand <> Label l
Proof
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem compile_literal_vv_not_label[local]:
  compile_literal_vv ty lit sa = (vv,sb) ==> !l. vv_operand vv <> Label l
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def, comp_return_def] >>
  rpt strip_tac
  >~ [`BoolL b`] >-
    (Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def, vv_operand_def])
  >~ [`BytesV bs`] >-
    (Cases_on `ty` >> gvs[compile_literal_vv_def, comp_bind_def,
                          comp_return_def, vv_operand_def, base_ptr_def] >>
     Cases_on `b` >> gvs[compile_literal_vv_def, comp_bind_def,
                         comp_return_def, vv_operand_def, base_ptr_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[compile_literal_vv_def, comp_bind_def,
         comp_return_def, vv_operand_def, base_ptr_def] >>
     rpt (pairarg_tac >> gvs[vv_operand_def, base_ptr_def]) >>
     metis_tac[compile_bytelike_literal_not_label]) >>
  gvs[vv_operand_def, base_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[vv_operand_def, base_ptr_def]) >>
  metis_tac[compile_bytelike_literal_not_label]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Typed result-origin dependency" else ()
  end) [compile_expr_pop_not_label, compile_expr_structlit_not_label,
         compile_bytelike_literal_not_label, compile_literal_vv_not_label];

Theorem compile_extcall_not_label[local]:
  compile_call f ce rt ty (ExtCall stat skip sig opts) args d sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  PairCases_on `sig` >> Cases_on `args` >>
  simp[compile_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[vv_operand_def]) >>
  Cases_on `sig2 = NoneT` >> gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[compile_external_call_not_label]
QED

Theorem raw_call_outbuf_not_label[local]:
  compile_raw_call_outbuf n sa = ((v,p),sb) ==> !l. v <> Label l
Proof
  Cases_on `n > 0` >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem raw_call_finish_not_label[local]:
  compile_raw_call_finish addr dp dl gas value ct n rof ov op sa = (v,sb) /\
  (!l. ov <> Label l) ==> !l. v <> Label l
Proof
  Cases_on `ct` >> Cases_on `rof` >> Cases_on `n > 0` >>
  simp[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label, emit_op_safe_operand, safe_operand_def]
QED

Theorem compile_raw_calls_not_label[local]:
  (compile_call f ce rt ty (RawCallTarget rcf) args d sa = (vv,sb) ==>
     !l. vv_operand vv <> Label l) /\
  (compile_call f ce rt ty (RawCallCalldataTarget rcf) args d sa = (vv,sb) ==>
     !l. vv_operand vv <> Label l)
Proof
  conj_tac >> Cases_on `args` >> simp[compile_call_def, LET_THM] >>
  TRY (rename1 `list_CASE rest _ _` >> Cases_on `rest` >> simp[]) >>
  strip_tac >> rpt (pairarg_tac >> gvs[vv_operand_def]) >>
  Cases_on `rcf.rcf_max_outsize = 0` >> gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[raw_call_outbuf_not_label, raw_call_finish_not_label]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Call result-origin dependency" else ()
  end) [compile_extcall_not_label, raw_call_outbuf_not_label,
         raw_call_finish_not_label, compile_raw_calls_not_label];

Theorem compile_call_not_label[local]:
  compile_call f ce rt ty target args d sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `target`
  >~ [`IntCall fid`] >- metis_tac[compile_internal_call_not_label]
  >~ [`ExtCall stat skip sig opts`] >- metis_tac[compile_extcall_not_label]
  >~ [`RawCallTarget rcf`] >- metis_tac[cj 1 compile_raw_calls_not_label]
  >~ [`RawCallCalldataTarget rcf`] >- metis_tac[cj 2 compile_raw_calls_not_label] >>
  simp[compile_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[vv_operand_def]) >>
  gvs[vv_operand_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[vv_operand_def]) >>
  Cases_on `compile_create_call f ce c b b0 args sa` >>
  gvs[as_stack_val_def, vv_operand_def] >>
  metis_tac[compile_create_call_safe_operand, safe_operand_def]
QED

val _ = let val (ors,axs) = Tag.dest_tag (Thm.tag compile_call_not_label) in
  if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
  then raise Fail "General call operand dependency" else ()
end;

Theorem compile_name_vv_local_not_label[local]:
  ~(?l sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz)) /\
  compile_name_vv ce ty id sa = (vv,sb) ==> !l. vv_operand vv <> Label l
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[compile_name_vv_def, comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  TRY (rename1 `SOME loc` >> Cases_on `loc` >> simp[]) >>
  rpt strip_tac >> gvs[vv_operand_def, mk_ptr_def, comp_return_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[vv_operand_def, mk_ptr_def, comp_return_def, comp_bind_def]) >>
  metis_tac[]
QED

Theorem compile_expr_body_not_label[local]:
  (!id t. FLOOKUP env.var_types id = SOME t ==>
    ~(?l sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz))) /\
  (!ann bi args s vv s'. well_typed_expr env (Builtin ann bi args) /\
    g ce ann ty bi args s = (vv,s') ==> !l. vv_operand vv <> Label l) /\
  (!ann tb rt args s vv s'. well_typed_expr env (TypeBuiltin ann tb rt args) /\
    h ce ann ty tb rt args s = (vv,s') ==> !l. vv_operand vv <> Label l) /\
  well_typed_expr env e /\
  compile_expr_body f g h ce ty e sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `e` >> rpt strip_tac
  >~ [`Builtin ann bi args`] >- suspend "builtin"
  >~ [`TopLevelName ann nsid`] >- metis_tac[compile_expr_toplevelname_not_label]
  >~ [`Pop ann target`] >- metis_tac[compile_expr_pop_not_label]
  >~ [`StructLit ann name fields`] >- metis_tac[compile_expr_structlit_not_label]
  >~ [`IfExp ann cond_e then_e else_e`] >- metis_tac[compile_expr_ifexp_not_label] >>
  gvs[compile_expr_body_def, expr_type_def, LET_THM]
  >~ [`compile_name_vv _ _ _ _ = _`] >- suspend "name"
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[compile_literal_vv_not_label]
  >~ [`compile_subscript _ _ _ _ _ _ _ = _`] >- metis_tac[compile_subscript_not_label]
  >~ [`compile_attribute _ _ _ _ _ _ _ = _`] >-
    metis_tac[compile_attribute_safe_operand, safe_operand_def]
  >~ [`compile_call _ _ _ _ _ _ _ _ = _`] >- metis_tac[compile_call_not_label]
  >~ [`h ce _ ty _ _ _ sa = (vv,sb)`] >-
    (qpat_x_assum `!ann tb rt args s vv s'. _` drule_all >> simp[]) >>
  gvs[vv_operand_def]
QED

Resume compile_expr_body_not_label[name]:
  fs[well_typed_expr_def] >>
  metis_tac[compile_name_vv_local_not_label]
QED

Theorem named_modular_not_label[local]:
  (!ce rt at a bt b mt m s vv s'.
    compile_addmod_names ce rt at a bt b mt m s = (vv,s') ==> !l. vv_operand vv <> Label l) /\
  (!ce rt at a bt b mt m s vv s'.
    compile_mulmod_names ce rt at a bt b mt m s = (vv,s') ==> !l. vv_operand vv <> Label l) /\
  (!ce rt at a bt b s vv s'.
    compile_powmod256_names ce rt at a bt b s = (vv,s') ==> !l. vv_operand vv <> Label l)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_addmod_names_def, compile_mulmod_names_def,
       compile_powmod256_names_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `as_stack_val rt result` >>
  PairCases_on `result` >> gvs[as_stack_val_def, vv_operand_def, markerTheory.Abbrev_def] >>
  metis_tac[compile_addmod_safe_operand, compile_mulmod_safe_operand,
            compile_pow_mod256_safe_operand, safe_operand_def]
QED

Theorem compile_expr_builtin_not_label_classify[local]:
  compile_expr_body f g h ce ty (Builtin ann bi args) sa = (vv,sb) ==>
  g ce ann ty bi args sa = (vv,sb) \/ (!l. vv_operand vv <> Label l)
Proof
  Cases_on `bi` >>
  simp[compile_expr_body_def, expr_type_def, LET_THM,
       word_list_result_elim, word_expr_result_elim] >>
  rpt strip_tac >> metis_tac[named_modular_not_label]
QED

Resume compile_expr_body_not_label[builtin]:
  drule compile_expr_builtin_not_label_classify >> strip_tac >> metis_tac[]
QED
Finalise compile_expr_body_not_label

Theorem compile_type_convert_not_label[local]:
  (!l. v <> Label l) /\ compile_type_convert v conv sa = (r,sb) ==>
  !l. r <> Label l
Proof
  Cases_on `conv` >>
  simp[compile_type_convert_def, compile_int_clamp_def,
       load_bytestring_as_word_def,
       compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt (IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def]) >>
  strip_tac >> gvs[]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Typed body operand dependency" else ()
  end) [compile_name_vv_local_not_label, named_modular_not_label,
         compile_expr_builtin_not_label_classify, compile_expr_body_not_label,
         compile_type_convert_not_label];

Theorem as_stack_val_not_label[local]:
  (!op st. result = (op,st) ==> !l. op <> Label l) /\
  as_stack_val ty result = (vv,sb) ==> !l. vv_operand vv <> Label l
Proof
  PairCases_on `result` >> simp[as_stack_val_def] >> rpt strip_tac >> gvs[vv_operand_def]
QED

Theorem as_ptr_val_not_label[local]:
  (!op st. result = (op,st) ==> !l. op <> Label l) /\
  as_ptr_val ty loc result = (vv,sb) ==> !l. vv_operand vv <> Label l
Proof
  PairCases_on `result` >> simp[as_ptr_val_def] >> rpt strip_tac >> gvs[vv_operand_def, mk_ptr_def]
QED

Theorem compile_bytestring_widen_copy_not_label[local]:
  compile_bytestring_widen_copy dst v src sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[compile_bytestring_widen_copy_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem type_builtin_convert_not_label[local]:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
    lower_value f ce t e s = (op,s') ==> !l. op <> Label l) /\
  well_typed_expr env (TypeBuiltin vt Convert rt args) /\
  compile_type_builtin_dispatch_body f ce vt ty Convert rt args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> drule typed_convert_child >> strip_tac >> gvs[] >>
  gvs[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> Cases_on `rt` >>
  gvs[AllCaseEqs(), vv_operand_def] >>
  drule_at (Pos last) as_stack_val_not_label >>
  (impl_tac >- metis_tac[compile_type_convert_not_label,
                        compile_bytestring_widen_copy_not_label]) >> simp[]
QED

Theorem lower_abi_encode_not_label[local]:
  lower_abi_encode ensure mid src info maxlen sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinAbiTheory.lower_abi_encode_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem type_builtin_nonconvert_not_label[local]:
  tb <> Convert /\
  compile_type_builtin_dispatch_body f ce vt ty tb rt args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), vv_operand_def, base_ptr_def]
  >~ [`as_stack_val _ _ = _`] >-
    (drule_at (Pos last) as_stack_val_not_label >>
     (impl_tac >-
       (rpt strip_tac >> drule_all compile_extract32_load_safe_operand >>
        strip_tac >> metis_tac[compile_clamp_basetype_safe_operand, safe_operand_def])) >>
     simp[])
  >~ [`compile_builtin_empty_complex _ _ _ = _`] >- metis_tac[compile_empty_not_label]
  >~ [`lower_abi_decode _ _ _ _ _ _`] >-
    (drule_at (Pos last) as_ptr_val_not_label >>
     (impl_tac >- metis_tac[lower_abi_decode_not_label]) >> simp[]) >>
  drule_at (Pos last) as_ptr_val_not_label >>
  (impl_tac >- metis_tac[lower_abi_encode_not_label]) >> simp[]
QED

Theorem type_builtin_dispatch_body_not_label[local]:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
    lower_value f ce t e s = (op,s') ==> !l. op <> Label l) /\
  well_typed_expr env (TypeBuiltin vt tb rt args) /\
  compile_type_builtin_dispatch_body f ce vt ty tb rt args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `tb = Convert` >> rpt strip_tac
  >- (gvs[] >> metis_tac[type_builtin_convert_not_label]) >>
  metis_tac[type_builtin_nonconvert_not_label]
QED

Theorem builtin_scalar_not_label[local]:
  (bi = Not \/ bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
   bi = Ceil \/ bi = Floor \/ bi = AddMod \/ bi = MulMod \/ bi = PowMod256 \/
   bi = ECRecover \/ bi = CalldataLen \/ (?item. bi = Env item)) /\
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  drule_at (Pos last) as_stack_val_not_label >>
  (impl_tac >-
    metis_tac[emit_op_safe_operand, compile_invert_safe_operand,
      compile_neg_safe_operand, compile_builtin_abs_safe_operand,
      compile_blockhash_safe_operand, compile_blobhash_safe_operand,
      compile_ceil_safe_operand, compile_floor_safe_operand,
      compile_addmod_safe_operand, compile_mulmod_safe_operand,
      compile_pow_mod256_safe_operand, compile_ecrecover_safe_operand,
      compile_builtin_calldatasize_safe_operand, compile_env_var_safe_operand,
      safe_operand_def]) >> simp[]
QED

Theorem builtin_hash_not_label[local]:
  (bi = Keccak256 \/ bi = Sha256) /\
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  drule_at (Pos last) as_stack_val_not_label >>
  (impl_tac >-
    metis_tac[compile_keccak256_bytes_safe_operand,
      compile_keccak256_bytesm_safe_operand, compile_keccak256_word_safe_operand,
      compile_sha256_bytes_safe_operand, compile_sha256_bytesm_safe_operand,
      compile_sha256_word_safe_operand, safe_operand_def]) >> simp[]
QED

Theorem builtin_bop_not_label[local]:
  compile_builtin_dispatch_body f ce vt ty (Bop bop) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  drule_at (Pos last) as_stack_val_not_label >>
  (impl_tac >-
    metis_tac[compile_binop_safe_operand, emit_op_safe_operand,
      compile_list_membership_in_safe_operand, compile_list_membership_notin_safe_operand,
      compile_var_array_membership_safe_operand, safe_operand_def]) >> simp[]
QED

Theorem builtin_len_not_label[local]:
  compile_builtin_dispatch_body f ce vt ty Len args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  drule_at (Pos last) as_stack_val_not_label >>
  (impl_tac >- metis_tac[compile_builtin_calldatasize_safe_operand,
                        compile_builtin_len_safe_operand, safe_operand_def]) >> simp[]
QED

Theorem compile_acc_not_label[local]:
  (acc = Address ==> !s r s'. lower_value f ce (BaseT AddressT) e s = (r,s') ==>
     !l. r <> Label l) /\
  compile_acc f ce e acc sa = (r,sb) ==> !l. r <> Label l
Proof
  Cases_on `acc` >> simp[compile_acc_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_op_safe_operand, safe_operand_def]
QED

Theorem builtin_acc_not_label[local]:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
    lower_value f ce t e s = (op,s') ==> !l. op <> Label l) /\
  well_typed_expr env (Builtin vt (Acc item) args) /\
  compile_builtin_dispatch_body f ce vt ty (Acc item) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[] >> rename1 `_ :: rest` >>
  Cases_on `rest` >> simp[] >> rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  drule_at (Pos last) as_stack_val_not_label >>
  (impl_tac >-
    (gvs[well_typed_expr_def] >> rpt strip_tac >>
     drule_at (Pos last) compile_acc_not_label >>
     (impl_tac >- metis_tac[]) >> simp[])) >> simp[]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Typed dispatcher operand dependency" else ()
  end) [as_stack_val_not_label, as_ptr_val_not_label,
         compile_bytestring_widen_copy_not_label, type_builtin_convert_not_label,
         lower_abi_encode_not_label, type_builtin_nonconvert_not_label,
         type_builtin_dispatch_body_not_label, builtin_scalar_not_label,
         builtin_hash_not_label, builtin_bop_not_label, builtin_len_not_label,
         compile_acc_not_label, builtin_acc_not_label];

Theorem compile_make_tuple_result_operand[local]:
  !es buf off sa op sb.
    compile_make_tuple f ce es buf off sa = (op,sb) ==> op = buf
Proof
  Induct_on `es` >>
  simp[Once compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compile_make_array_elems_result_operand[local]:
  !es buf idx sa op sb.
    compile_make_array_elems f ce es et sz lw buf idx sa = (op,sb) ==> op = buf
Proof
  Induct_on `es` >>
  simp[Once compile_make_array_elems_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compile_make_array_result_operand[local]:
  compile_make_array f ce es et sz lw buf sa = (op,sb) ==> op = buf
Proof
  simp[compile_make_array_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_make_array_elems_result_operand]
QED

Theorem builtin_make_array_not_label[local]:
  compile_builtin_dispatch_body f ce vt ty (MakeArray et bd) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `et` >> simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  drule_at (Pos last) as_ptr_val_not_label >>
  (impl_tac >- metis_tac[compile_make_tuple_result_operand,
     compile_make_array_result_operand, alloc_buffer_not_label]) >> simp[]
QED

Theorem builtin_ec_not_label[local]:
  (bi = ECAdd \/ bi = ECMul) /\
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_at (Pos last) as_ptr_val_not_label >>
  (impl_tac >- metis_tac[ec_arith_result_not_label]) >> simp[]
QED

Theorem builtin_concat_not_label[local]:
  compile_builtin_dispatch_body f ce vt ty (Concat n) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def, base_ptr_def] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem slice_out_buf_not_label[local]:
  compile_slice_out_buf sz sa = ((buf,data),sb) ==> !l. buf <> Label l
Proof
  simp[compile_slice_out_buf_def, comp_bind_def, comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem slice_result_not_label[local]:
  (compile_slice_data len data start cnt sz sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_slice_calldata start cnt sz sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_slice_code start cnt sz sa = (op,sb) ==> !l. op <> Label l) /\
  ((!l. buf <> Label l) /\
   compile_slice_extcode addr start cnt buf data sa = (op,sb) ==> !l. op <> Label l)
Proof
  rpt conj_tac >>
  simp[compile_slice_data_def, compile_slice_calldata_def, compile_slice_code_def,
       compile_slice_extcode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  gvs[] >> metis_tac[alloc_buffer_not_label, slice_out_buf_not_label]
QED

Theorem builtin_slice_not_label[local]:
  (bi = CalldataSlice n \/ bi = Slice n) /\
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_at (Pos last) as_ptr_val_not_label >>
  (impl_tac >- metis_tac[slice_result_not_label, slice_out_buf_not_label]) >> simp[]
QED

Theorem compile_uint2str_not_label[local]:
  compile_uint2str v n sz sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[compile_uint2str_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> gvs[]
QED

Theorem builtin_uint2str_not_label[local]:
  compile_builtin_dispatch_body f ce vt ty (Uint2Str n) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> drule_at (Pos last) as_ptr_val_not_label >>
  (impl_tac >- metis_tac[compile_uint2str_not_label]) >> simp[]
QED

Theorem compile_as_wei_value_decimal_not_label[local]:
  compile_as_wei_value_decimal v scale divisor sa = (op,sb) ==> !l. op <> Label l
Proof
  Cases_on `scale = 1` >>
  simp[compile_as_wei_value_decimal_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `emit_op Div _ _ = _` (mp_tac o MATCH_MP emit_op_safe_operand) >>
  simp[safe_operand_def]
QED

Theorem compile_as_wei_value_int_not_label[local]:
  (!l. v <> Label l) /\
  compile_as_wei_value_int v scale signed sa = (op,sb) ==> !l. op <> Label l
Proof
  Cases_on `scale = 1` >>
  simp[compile_as_wei_value_int_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> gvs[] >>
  qpat_x_assum `emit_op MUL _ _ = _` (mp_tac o MATCH_MP emit_op_safe_operand) >>
  simp[safe_operand_def]
QED

Theorem builtin_as_wei_value_not_label[local]:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
    lower_value f ce t e s = (op,s') ==> !l. op <> Label l) /\
  well_typed_expr env (Builtin vt (AsWeiValue denom) args) /\
  compile_builtin_dispatch_body f ce vt ty (AsWeiValue denom) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[] >> rename1 `_ :: rest` >>
  Cases_on `rest` >> simp[] >> rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, LET_THM, well_typed_expr_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  drule_at (Pos last) as_stack_val_not_label >>
  (impl_tac >- metis_tac[compile_as_wei_value_decimal_not_label,
                        compile_as_wei_value_int_not_label]) >> simp[]
QED

Theorem compile_method_id_runtime_not_label[local]:
  compile_method_id_runtime ty v bytes4 sa = (op,sb) ==> !l. op <> Label l
Proof
  Cases_on `bytes4` >>
  simp[compile_method_id_runtime_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> gvs[] >>
  metis_tac[emit_op_safe_operand, safe_operand_def, alloc_buffer_not_label]
QED

Theorem builtin_method_id_not_label[local]:
  compile_builtin_dispatch_body f ce vt ty MethodId args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[])
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[compile_literal_vv_not_label] >>
  gvs[AllCaseEqs()]
  >~ [`as_stack_val _ _ = _`] >-
    (drule_at (Pos last) as_stack_val_not_label >>
     (impl_tac >- metis_tac[compile_method_id_runtime_not_label]) >> simp[]) >>
  drule_at (Pos last) as_ptr_val_not_label >>
  (impl_tac >- metis_tac[compile_method_id_runtime_not_label]) >> simp[]
QED

Theorem builtin_dispatch_body_not_label[local]:
  (!e t s op s'. MEM e args /\ well_typed_expr env e /\
    lower_value f ce t e s = (op,s') ==> !l. op <> Label l) /\
  well_typed_expr env (Builtin vt bi args) /\
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `bi` >> rpt strip_tac
  >~ [`Bop bop`] >- metis_tac[builtin_bop_not_label]
  >~ [`Acc item`] >- metis_tac[builtin_acc_not_label]
  >~ [`AsWeiValue denom`] >-
    metis_tac[builtin_as_wei_value_not_label]
  >~ [`Len`] >- metis_tac[builtin_len_not_label]
  >~ [`MethodId`] >- metis_tac[builtin_method_id_not_label]
  >~ [`MakeArray et bd`] >- metis_tac[builtin_make_array_not_label]
  >~ [`Concat n`] >- metis_tac[builtin_concat_not_label]
  >~ [`Uint2Str n`] >- metis_tac[builtin_uint2str_not_label]
  >~ [`Slice n`] >- metis_tac[builtin_slice_not_label]
  >~ [`CalldataSlice n`] >- metis_tac[builtin_slice_not_label]
  >> metis_tac[builtin_scalar_not_label, builtin_hash_not_label, builtin_ec_not_label]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Typed aggregate dispatcher operand dependency" else ()
  end) [compile_make_tuple_result_operand, compile_make_array_elems_result_operand,
         compile_make_array_result_operand, builtin_make_array_not_label,
         builtin_ec_not_label, builtin_concat_not_label, slice_out_buf_not_label,
         slice_result_not_label, builtin_slice_not_label, compile_uint2str_not_label,
         builtin_uint2str_not_label, compile_as_wei_value_decimal_not_label,
         compile_as_wei_value_int_not_label, builtin_as_wei_value_not_label,
         compile_method_id_runtime_not_label, builtin_method_id_not_label,
         builtin_dispatch_body_not_label];

Theorem compile_expr_not_label:
  (!ce ty e sa env vv sb.
    compile_expr ce ty e sa = (vv,sb) /\ well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
      ~(?l sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz))) ==>
    !l. vv_operand vv <> Label l) /\
  (!ce ann ty bi args sa env vv sb.
    compile_builtin_dispatch ce ann ty bi args sa = (vv,sb) /\
    well_typed_expr env (Builtin ann bi args) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
      ~(?l sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz))) ==>
    !l. vv_operand vv <> Label l) /\
  (!ce ann ty tb rt args sa env vv sb.
    compile_type_builtin_dispatch ce ann ty tb rt args sa = (vv,sb) /\
    well_typed_expr env (TypeBuiltin ann tb rt args) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
      ~(?l sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz))) ==>
    !l. vv_operand vv <> Label l)
Proof
  ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume compile_expr_not_label[expr]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule compile_expr_body_not_label >>
  goal_assum (drule_at (Pat `compile_expr_body`)) >>
  qexists_tac `env` >> simp[] >> conj_tac >-
    (rpt gen_tac >> simp[builtin_child_callback_def] >>
     Cases_on `list_size expr_size args < expr_size e` >> simp[] >-
       metis_tac[] >>
     simp[invalid_expr_call_def, LET_THM] >> strip_tac >>
     rpt (pairarg_tac >> gvs[vv_operand_def])) >>
  rpt gen_tac >> simp[type_child_callback_def] >>
  Cases_on `list_size expr_size args < expr_size e` >> simp[] >-
    metis_tac[] >>
  simp[invalid_expr_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[vv_operand_def])
QED

Resume compile_expr_not_label[builtin]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule builtin_dispatch_body_not_label >>
  goal_assum (drule_at (Pat `compile_builtin_dispatch_body`)) >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >>
  drule_at (Pos last) lower_value_child_not_label >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >-
    (conj_tac >- (qx_gen_tac `arg` >> rpt gen_tac >> strip_tac >>
                  qpat_x_assum `!e ce ty sa. _` (qspec_then `arg` mp_tac) >>
                  simp[] >> disch_then drule_all >> simp[]) >> simp[])) >> simp[]
QED
Resume compile_expr_not_label[type_builtin]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule type_builtin_dispatch_body_not_label >>
  goal_assum (drule_at (Pat `compile_type_builtin_dispatch_body`)) >>
  qexists_tac `env` >> simp[] >>
  rpt strip_tac >> drule_at (Pos last) lower_value_child_not_label >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >-
    (conj_tac >- (qx_gen_tac `arg` >> rpt gen_tac >> strip_tac >>
                  qpat_x_assum `!e ce ty sa. _` (qspec_then `arg` mp_tac) >>
                  simp[] >> disch_then drule_all >> simp[]) >> simp[])) >> simp[]
QED
Finalise compile_expr_not_label

Theorem lower_value_compile_expr_not_label:
  lower_value compile_expr ce ty e sa = (op,sb) /\ well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
    ~(?l sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz))) ==>
  !l. op <> Label l
Proof
  simp[lower_value_def, comp_bind_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  drule (cj 1 compile_expr_not_label) >>
  disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all unwrap_value_not_label >> simp[]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Typed compiler no-label dependency" else ()
  end) [compile_expr_not_label, lower_value_compile_expr_not_label];
