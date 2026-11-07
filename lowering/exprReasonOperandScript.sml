(*
 * The value lowering hands out for a string reason (#637)
 *
 * The revert of a Raise or Assert with a reason encodes the reason's
 * compiled value: a memory or stack value (stmtSimReasonExpr's
 * reason_vv_ok) or a storage or transient pointer (stmtSimReasonStorage's
 * reason_storage_vv), or a pointer into code (reason_code_vv), which an
 * immutable gives.  With every local held through a variable pointer, a
 * well-typed string expression compiles to one of the three, the same one
 * at every compile state.
 *
 * TOP-LEVEL:
 *   reason_code_vv             — the reason's value is a pointer into code
 *   compile_expr_string_reason
 *   lower_compile_expr_not_label — lower_value's operand is no label
 *
 * Helper:
 *   reason_result_shape, reason_uniform_shape — the kind of value
 *                                compile_expr gives, at every compile state
 *   reason_typable             — an expression or a place the typing takes
 *)

Theory exprReasonOperand
Ancestors
  exprSimSource
  exprWordOperand exprOperandVar exprSafeOperand stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage exprLowering exprCallBounds compileEnv context vyperTypeSystem vyperAST

(* The reason's value_vv is a pointer to a value of a type that is not a
   word type (a string) in code: an immutable's value. *)
Definition reason_code_vv_def:
  reason_code_vv vv <=>
    ?t p. vv = LocatedValue t p /\ ~is_word_type t /\ p.ptr_location = LocCode
End

Definition reason_result_shape_def:
  (reason_result_shape t loc (StackValue t' op) <=>
    t' = t /\ loc = LocMemory /\ (!l. op <> Label l)) /\
  (reason_result_shape t loc (LocatedValue t' p) <=>
    t' = t /\ p.ptr_location = loc /\ (!l. p.ptr_operand <> Label l))
End

Theorem reason_result_shape_memory[local]:
  reason_result_shape t LocMemory vv /\ ~is_word_type t ==>
  reason_vv_ok vv
Proof
  cheat
QED

Theorem reason_result_shape_storage[local]:
  reason_result_shape t loc vv /\ ~is_word_type t /\
  (loc = LocStorage \/ loc = LocTransient) ==>
  reason_storage_vv vv
Proof
  cheat
QED

Theorem reason_result_shape_code[local]:
  reason_result_shape t LocCode vv /\ ~is_word_type t ==> reason_code_vv vv
Proof
  cheat
QED

Theorem reason_compile_name[local]:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  compile_name_vv cenv t id sa = (vv,sb) ==>
  reason_result_shape t LocMemory vv
Proof
  cheat
QED

Theorem reason_compile_toplevelname[local]:
  ?loc. (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
    !sa vv sb. compile_expr_body f g h cenv ty (TopLevelName t nsid) sa = (vv,sb) ==>
      reason_result_shape t loc vv
Proof
  cheat
QED

Theorem reason_pop_operand[local]:
  compile_dynarray_pop bop ws es is_ctor imm loc sa = (op,sb) ==>
  !l. op <> Label l
Proof
  cheat
QED

Theorem reason_projection_operand[local]:
  (compile_mapping_subscript bop key sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_tuple_subscript bop off sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_array_subscript bop idx dyn sc ws es is_signed load_opc sa = (op,sb) ==>
   !l. op <> Label l)
Proof
  cheat
QED

Theorem reason_compile_attribute[local]:
  (!sa vv sb. f cenv ty base_e sa = (vv,sb) ==>
     reason_result_shape bt loc vv) /\
  compile_attribute f cenv ret_ty ty base_e fld sa = (vv,sb) ==>
  reason_result_shape ret_ty loc vv
Proof
  cheat
QED

Theorem reason_compile_subscript[local]:
  (!sa vv sb. f cenv ty base_e sa = (vv,sb) ==>
     reason_result_shape bt loc vv) /\
  compile_subscript f cenv ret_ty ty base_e idx_e sa = (vv,sb) ==>
  reason_result_shape ret_ty loc vv
Proof
  cheat
QED

(* The location a target's pointer lives in comes from its root name, at
   every compile state. *)
Theorem reason_target_ptr_loc[local]:
  !bt. ?lo. (!l. lo = SOME l ==>
               l = LocMemory \/ l = LocStorage \/ l = LocTransient \/ l = LocCode) /\
    !sa r sb. compile_get_target_ptr cfn cenv bt sa = (r,sb) ==> FST (SND r) = lo
Proof
  cheat
QED

Theorem reason_compile_pop:
  ?loc. (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
    !sa vv sb. compile_expr_body f g h cenv ty (Pop t target) sa = (vv,sb) ==>
      reason_result_shape t loc vv
Proof
  cheat
QED

Theorem reason_alloc_operand[local]:
  compile_alloc_buffer sz sa = (buf,sb) ==> !l. buf.buf_operand <> Label l
Proof
  cheat
QED

Theorem reason_bytelike_operand[local]:
  compile_bytelike_literal bs maxlen sa = (buf,sb) ==>
  !l. buf.buf_operand <> Label l
Proof
  cheat
QED

Theorem reason_compile_literal:
  compile_literal_vv t lit sa = (vv,sb) ==>
  reason_result_shape t LocMemory vv
Proof
  cheat
QED

Theorem reason_compile_ifexp:
  compile_expr_body f g h cenv ty (IfExp t cond_e then_e else_e) sa = (vv,sb) ==>
  reason_result_shape t LocMemory vv
Proof
  cheat
QED

Theorem reason_compile_structlit:
  compile_expr_body f g h cenv ty (StructLit t nm fields) sa = (vv,sb) ==>
  reason_result_shape t LocMemory vv
Proof
  cheat
QED

Theorem reason_stack_result[local]:
  as_stack_val t res = (vv,sb) /\ word_result_ok sb vv ==>
  reason_result_shape t LocMemory vv
Proof
  cheat
QED

Theorem reason_builtin_scalar:
  (bi = Not \/ bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
   bi = Ceil \/ bi = Floor \/ bi = AddMod \/ bi = MulMod \/ bi = PowMod256 \/
   bi = ECRecover \/ bi = CalldataLen \/ (?item. bi = Env item)) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_builtin_hash:
  (bi = Keccak256 \/ bi = Sha256) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_builtin_len:
  compile_builtin_dispatch_body f cenv vt ty Len args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_builtin_bop:
  compile_builtin_dispatch_body f cenv vt ty (Bop bop) args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_ensure_memory_operand[local]:
  (!l. p <> Label l) /\
  compile_ensure_in_memory p loc bytes wc ctor imm sa = (op,sb) ==>
  !l. op <> Label l
Proof
  cheat
QED

Theorem reason_unwrap_operand[local]:
  reason_result_shape t loc vv /\ unwrap_value cenv vv sa = (op,sb) ==>
  !l. op <> Label l
Proof
  cheat
QED

Theorem reason_lower_operand[local]:
  (!sa vv sb. f cenv ty e sa = (vv,sb) ==>
     ?t loc. reason_result_shape t loc vv) /\
  lower_value f cenv ty e sa = (op,sb) ==>
  !l. op <> Label l
Proof
  cheat
QED

Theorem reason_convert_operand[local]:
  (!l. v <> Label l) /\ compile_type_convert v conv sa = (op,sb) ==>
  !l. op <> Label l
Proof
  cheat
QED

Theorem reason_widen_copy_operand[local]:
  compile_bytestring_widen_copy d v sz sa = (op,sb) ==> !l. op <> Label l
Proof
  cheat
QED

Theorem reason_type_builtin_convert[local]:
  (!sa op sb. lower_value f cenv (expr_type (HD args)) (HD args) sa = (op,sb)
               ==> !l. op <> Label l) /\
  compile_type_builtin_dispatch_body f cenv vt ty Convert rt args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_compile_named_modular[local]:
  (!ce rt at a bt b mt m s vv s'.
    compile_addmod_names ce rt at a bt b mt m s = (vv,s') ==>
    reason_result_shape rt LocMemory vv) /\
  (!ce rt at a bt b mt m s vv s'.
    compile_mulmod_names ce rt at a bt b mt m s = (vv,s') ==>
    reason_result_shape rt LocMemory vv) /\
  (!ce rt at a bt b s vv s'.
    compile_powmod256_names ce rt at a bt b s = (vv,s') ==>
    reason_result_shape rt LocMemory vv)
Proof
  cheat
QED

Theorem reason_slice_out_buf[local]:
  compile_slice_out_buf sz sa = ((buf,data),sb) ==> !l. buf <> Label l
Proof
  cheat
QED

Theorem reason_slice_data[local]:
  compile_slice_data len data start lenop sz sa = (op,sb) ==> !l. op <> Label l
Proof
  cheat
QED

Theorem reason_slice_adhoc[local]:
  (!start lenop sz sa op sb.
    compile_slice_calldata start lenop sz sa = (op,sb) ==> !l. op <> Label l) /\
  (!start lenop sz sa op sb.
    compile_slice_code start lenop sz sa = (op,sb) ==> !l. op <> Label l) /\
  (!addr start lenop buf data sa op sb.
    (!l. buf <> Label l) /\
    compile_slice_extcode addr start lenop buf data sa = (op,sb) ==>
    !l. op <> Label l)
Proof
  cheat
QED

Theorem reason_ec_points[local]:
  (!p q sa op sb. compile_ecadd_points p q sa = (op,sb) ==> !l. op <> Label l) /\
  (!p scalar sa op sb. compile_ecmul_point p scalar sa = (op,sb) ==>
                         !l. op <> Label l)
Proof
  cheat
QED

Theorem reason_uint2str[local]:
  compile_uint2str v digits sz sa = (op,sb) ==> !l. op <> Label l
Proof
  cheat
QED

Theorem reason_builtin_fresh:
  ((?n. bi = CalldataSlice n) \/ bi = ECAdd \/ bi = ECMul \/
   (?n. bi = Concat n) \/ (?n. bi = Slice n) \/ (?n. bi = Uint2Str n)) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_builtin_makearray:
  compile_builtin_dispatch_body f cenv vt ty (MakeArray et bd) args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_acc_operand[local]:
  (!sa op sb. lower_value f cenv (BaseT AddressT) e sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_acc f cenv e item sa = (op,sb) ==> !l. op <> Label l
Proof
  cheat
QED

Theorem reason_wei_operand[local]:
  (!v scale signed sa op sb. (!l. v <> Label l) /\
    compile_as_wei_value_int v scale signed sa = (op,sb) ==> !l. op <> Label l) /\
  (!v scale divisor sa op sb.
    compile_as_wei_value_decimal v scale divisor sa = (op,sb) ==> !l. op <> Label l)
Proof
  cheat
QED

Theorem reason_method_operand[local]:
  compile_method_id_runtime ty v flag sa = (op,sb) ==> !l. op <> Label l
Proof
  cheat
QED

Theorem reason_builtin_acc[local]:
  (!sa op sb. lower_value f cenv (BaseT AddressT) (HD args) sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_builtin_dispatch_body f cenv vt ty (Acc item) args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_builtin_as_wei_value[local]:
  (!sa op sb. lower_value f cenv (expr_type (HD args)) (HD args) sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_builtin_dispatch_body f cenv vt ty (AsWeiValue denom) args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_builtin_method_id:
  compile_builtin_dispatch_body f cenv vt ty MethodId args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_empty_operand[local]:
  compile_builtin_empty_complex sz bs sa = (buf,sb) ==> !l. buf.buf_operand <> Label l
Proof
  cheat
QED

Theorem reason_abi_encode_operand:
  lower_abi_encode ensure mid src info maxlen sa = (op,sb) ==> !l. op <> Label l
Proof
  cheat
QED

Theorem reason_abi_decode_operand[local]:
  lower_abi_decode data info mn mx sz sa = (op,sb) ==> !l. op <> Label l
Proof
  cheat
QED

Theorem reason_type_builtin_nonconvert[local]:
  tb <> Convert /\
  type_builtin_result_ok tenv tb vt rt (MAP expr_type args) /\
  compile_type_builtin_dispatch_body f cenv vt ty tb rt args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Theorem reason_default_return_operand[local]:
  (!l. result <> Label l) /\
  compile_default_return_path cenv rt dt buf result def addr skip mn mx info sa = (op,sb) ==>
  !l. op <> Label l
Proof
  cheat
QED

Theorem reason_external_call_operand[local]:
  compile_external_call_kwargs cenv addr vals tys memsz abisz mid retsz mn outsz
    static value gas skip hasdef def rt dt einfo dinfo sa = (op,sb) ==>
  !l. op <> Label l
Proof
  cheat
QED

Theorem reason_raw_call_outbuf_operand[local]:
  compile_raw_call_outbuf mx sa = ((out_val,out_ptr),sb) ==>
  !l. out_val <> Label l
Proof
  cheat
QED

Theorem reason_raw_call_finish_operand[local]:
  (!l. out_val <> Label l) /\
  compile_raw_call_finish addr data len gas value ct mx rof out_val out_ptr sa =
    (op,sb) ==>
  !l. op <> Label l
Proof
  cheat
QED

(* Both raw_call forms: splitting off a second argument is needed for the
   byte-string form and harmless for the msg.data one. *)
val reason_raw_call_tac =
  Cases_on `args` >-
    (simp[compile_call_def, LET_THM] >> strip_tac >>
     rpt (pairarg_tac >> gvs[]) >> gvs[reason_result_shape_def]) >>
  Cases_on `t` >> simp[compile_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), reason_result_shape_def, mk_ptr_def] >>
  metis_tac[reason_raw_call_finish_operand, reason_raw_call_outbuf_operand]

Theorem reason_compile_call:
  compile_call f cenv rt ty target args default_ret sa = (vv,sb) ==>
  reason_result_shape
    (lowered_value_type cenv (Call rt target args default_ret)) LocMemory vv
Proof
  cheat
QED





Theorem reason_builtin_dispatch_body[local]:
  (!t e sa op sb. MEM e args /\ lower_value f cenv t e sa = (op,sb) ==>
                   !l. op <> Label l) /\
  (((?item. bi = Acc item) \/ (?denom. bi = AsWeiValue denom)) ==> args <> []) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED




Theorem reason_type_builtin_dispatch_body[local]:
  (!t e sa op sb. MEM e args /\ lower_value f cenv t e sa = (op,sb) ==>
                   !l. op <> Label l) /\
  (tb = Convert ==> args <> []) /\
  type_builtin_result_ok tenv tb vt rt (MAP expr_type args) /\
  compile_type_builtin_dispatch_body f cenv vt ty tb rt args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  cheat
QED

Definition reason_uniform_shape_def:
  reason_uniform_shape f cenv ty e <=>
    ?loc t. (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
      (t = expr_type e \/ t = lowered_value_type cenv e) /\
      !sa vv sb. f cenv ty e sa = (vv,sb) ==>
        reason_result_shape t loc vv
End

Theorem reason_uniform_shape_intro[local]:
  (?loc. (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
     !sa vv sb. f cenv ty e sa = (vv,sb) ==>
       reason_result_shape (expr_type e) loc vv) ==>
  reason_uniform_shape f cenv ty e
Proof
  cheat
QED

Definition reason_typable_def:
  reason_typable env e <=>
    well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt
End

Theorem reason_typable_expr[local]:
  well_typed_expr env e ==> reason_typable env e
Proof
  cheat
QED

Theorem reason_typable_subscript[local]:
  reason_typable env (Subscript ann base_e idx_e) ==> reason_typable env base_e
Proof
  cheat
QED

Theorem reason_typable_attribute[local]:
  reason_typable env (Attribute ann base_e fld) ==> well_typed_expr env base_e
Proof
  cheat
QED

Theorem reason_typable_name[local]:
  reason_typable env (Name ann id) ==> FLOOKUP env.var_types id = SOME ann
Proof
  cheat
QED

Theorem reason_typable_builtin[local]:
  reason_typable env (Builtin ann bi args) ==> well_typed_expr env (Builtin ann bi args)
Proof
  cheat
QED

Theorem reason_typable_type_builtin[local]:
  reason_typable env (TypeBuiltin ann tb rt args) ==>
  well_typed_expr env (TypeBuiltin ann tb rt args)
Proof
  cheat
QED

Theorem reason_compile_expr_body[local]:
  (!e'. expr_size e' < expr_size e /\ reason_typable env e' ==>
         reason_uniform_shape f cenv ty e') /\
  (!ann bi args sa vv sb.
     well_typed_expr env (Builtin ann bi args) /\
     g cenv ann ty bi args sa = (vv,sb) ==>
     reason_result_shape ann LocMemory vv) /\
  (!ann tb rt args sa vv sb.
     well_typed_expr env (TypeBuiltin ann tb rt args) /\
     h cenv ann ty tb rt args sa = (vv,sb) ==>
     reason_result_shape ann LocMemory vv) /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  reason_typable env e ==>
  reason_uniform_shape (compile_expr_body f g h) cenv ty e
Proof
  cheat
QED



Theorem reason_compile_expr_builtin_shape_classify:
  compile_expr_body f g h cenv ty (Builtin ann bi args) sa = (vv,sb) ==>
  g cenv ann ty bi args sa = (vv,sb) \/ reason_result_shape ann LocMemory vv
Proof
  cheat
QED







Theorem reason_compile_uniform[local]:
  (!cenv ty e (sa:compile_state) env.
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
      reason_typable env e ==> reason_uniform_shape compile_expr cenv ty e) /\
  (!cenv ann ty bi args (sa:compile_state) env.
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
      well_typed_expr env (Builtin ann bi args) ==>
    !s vv s'. compile_builtin_dispatch cenv ann ty bi args s = (vv,s') ==>
      reason_result_shape ann LocMemory vv) /\
  (!cenv ann ty tb rt args (sa:compile_state) env.
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
      well_typed_expr env (TypeBuiltin ann tb rt args) ==>
    !s vv s'. compile_type_builtin_dispatch cenv ann ty tb rt args s = (vv,s') ==>
      reason_result_shape ann LocMemory vv)
Proof
  cheat
QED









Theorem compile_expr_reason_uniform[local]:
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
  reason_uniform_shape compile_expr cenv ty e
Proof
  cheat
QED

(* Why it holds: only TopLevelName, Pop (infer_array_location) and the
   base a Subscript or Attribute passes through give a location other
   than memory: storage, transient, or code for an immutable.  That
   location is a function of cenv and the shape of e, not of the compile
   state.  The operands are literals, emitted variables, or a local's
   PtrVar (Var p), which well_typed_expr reaches only for names in
   env.var_types; ConvBytestringCast passes its argument's operand on.
   Bases and arguments have any type, so an induction needs a statement
   about every expression, not only strings. *)
Theorem compile_expr_string_reason:
  !cenv env e n.
    well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    expr_type e = BaseT (StringT n) /\
    ~is_word_type (lowered_value_type cenv e) ==>
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_vv_ok vv) \/
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_storage_vv vv) \/
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_code_vv vv)
Proof
  cheat
QED

(* With every typed local held through a variable pointer, the operand
   lower_value hands out for a well-typed expression is no label: a literal,
   a variable, or a pointer that compile_expr_reason_uniform gives one of
   those two.  The Log arguments' suffix frames need it. *)
Theorem lower_compile_expr_not_label:
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
  !l. op <> Label l
Proof
  cheat
QED
