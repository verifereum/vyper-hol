(* Typed dispatch for the memory-checked scalar conversion suffixes. *)
Theory bodyMemTbConvertScalarDispatch
Ancestors
  bodyMemTbConvertScalarFlags bodyMemTbConvertScalarBytes
  bodyMemTbConvertScalarOutputs
  convertScalarDispatch convertScalarTyping exprSimConvert compileEnv
  exprSimHyps vyperTypeSystem vyperTyping vyperValue exprLowering
Libs intLib

Theorem scalar_fixed_typed_dispatch_mem:
  !ctx func cenv cx es1 m t tv v.
    valid_conversion (BaseT (BytesT (Fixed m))) t /\
    ~is_bytestring_type t /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m))) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT (BytesT (Fixed m))) t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_from_fixed >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  simp[]
  >- suspend "bool"
  >- suspend "signed"
  >- suspend "unsigned"
  >- suspend "address"
  >- suspend "decimal" >>
  suspend "fixed"
QED

Resume scalar_fixed_typed_dispatch_mem[bool]:
  simp[mk_convert_op_def, is_bytestring_type_def, convert_result_def,
       vyperValueOperationTheory.evaluate_convert_from_def,
       vyperValueOperationTheory.evaluate_convert_def] >>
  irule scalar_bytes_bool_frag_mem >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[signed]:
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule (Q.INST [`sg` |-> `T`] (SPEC_ALL scalar_bytes_integer_result_frag_mem) |> SRULE []) >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[unsigned]:
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule (Q.INST [`sg` |-> `F`] (SPEC_ALL scalar_bytes_integer_result_frag_mem) |> SRULE []) >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[address]:
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule scalar_bytes_address_result_frag_mem >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[decimal]:
  pure_rewrite_tac[scalar_fixed_decimal_mk_op] >>
  irule scalar_bytes_decimal_all_result_frag_mem >> simp[]
QED
Resume scalar_fixed_typed_dispatch_mem[fixed]:
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  irule scalar_bytes_fixed_result_frag_mem >> simp[]
QED
Finalise scalar_fixed_typed_dispatch_mem

Theorem scalar_address_typed_dispatch_mem:
  !ctx func cenv cx es1 t tv v.
    valid_conversion (BaseT AddressT) t /\ ~is_bytestring_type t /\
    evaluate_type (get_tenv cx) (BaseT AddressT) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (mk_convert_op (BaseT AddressT) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (BaseT AddressT) t v) es1
Proof
  rpt strip_tac >> drule_all scalar_conversion_from_address >> strip_tac >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  simp[mk_convert_op_def, is_bytestring_type_def]
  >- (irule scalar_address_uint_result_frag_mem >> simp[]) >>
  irule scalar_address_bytes_result_frag_mem >> simp[]
QED

Theorem scalar_flag_typed_dispatch_mem:
  !ctx func cenv cx es1 name t tv v.
    valid_conversion (FlagT name) t /\
    evaluate_type (get_tenv cx) (FlagT name) = SOME tv /\
    IS_SOME (evaluate_type (get_tenv cx) t) /\ value_has_type tv v ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (mk_convert_op (FlagT name) t))
      (typed_val_to_w256 tv v) t
      (convert_result cx (FlagT name) t v) es1
Proof
  rpt strip_tac >> drule scalar_conversion_from_flag >> strip_tac >>
  gvs[evaluate_type_def] >>
  Cases_on `FLOOKUP (get_tenv cx) name` >> gvs[] >>
  rename1 `FLOOKUP _ _ = SOME args` >> Cases_on `args` >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  simp[mk_convert_op_def, is_bytestring_type_def, type_bits_def, is_signed_type_def]
  >- suspend "signed"
  >- suspend "unsigned" >>
  irule scalar_flag_bytes_result_frag_mem
QED
Resume scalar_flag_typed_dispatch_mem[signed]:
  irule (Q.INST [`sg` |-> `T`] (SPEC_ALL scalar_flag_int_result_frag_mem) |> SRULE []) >>
  simp[] >> rename1 `payload < 2 ** members` >>
  `2 ** members <= 2 ** 256` by (irule bitTheory.TWOEXP_MONO2 >> simp[]) >>
  qpat_x_assum `2 ** members <= _` (mp_tac o CONV_RULE (RAND_CONV EVAL)) >>
  decide_tac
QED
Resume scalar_flag_typed_dispatch_mem[unsigned]:
  irule (Q.INST [`sg` |-> `F`] (SPEC_ALL scalar_flag_int_result_frag_mem) |> SRULE []) >>
  simp[] >> rename1 `payload < 2 ** members` >>
  `2 ** members <= 2 ** 256` by (irule bitTheory.TWOEXP_MONO2 >> simp[]) >>
  qpat_x_assum `2 ** members <= _` (mp_tac o CONV_RULE (RAND_CONV EVAL)) >>
  decide_tac
QED
Finalise scalar_flag_typed_dispatch_mem
