(* Typed compiler output operands, independently of global environment shape. *)
Theory exprTypedOperand
Ancestors
  exprWordOperand exprSafeOperand exprSafeOperandBuiltins
  exprLoweringProps freshWrites compileEnv emitHelper context
  exprLowering exprCallBounds vyperTypeSystem vyperValue vyperAST vyperTypeBuiltins
  builtinSimple builtinMath builtinHashing builtinMisc builtinBytes builtinSystem

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
  (!e ce t s vv s'. expr_size e < bound /\ f ce t e s = (vv,s') /\
     well_typed_expr env e ==> !l. vv_operand vv <> Label l) /\
  well_typed_expr env e /\
  lower_value (expr_child_callback bound f) ce t e sa = (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `expr_size e < bound`
  >- (simp[lower_value_def, expr_child_callback_def, comp_bind_def] >>
      rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
      qpat_x_assum `!e ce t s vv s'. _` drule_all >>
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
  rpt (pairarg_tac >> gvs[vv_operand_def])
QED

val _ = let val (ors,axs) = Tag.dest_tag (Thm.tag compile_call_not_label) in
  if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
  then raise Fail "General call operand dependency" else ()
end;
