Theory createOperandSizeReject
Ancestors
  arithmetic list vyperCreate vyperState vyperValue vyperContext vfmConstants

Theorem raw_operands_size_reject:
  create_operand_layout RawCreate hs vs = xs /\
  dest_create_args RawCreate hs xs = SOME ops /\
  create_arg_ctor_types RawCreate hs tys = SOME ct /\
  ops.co_code_src = BytecodeCodeSource code /\
  encode_create_ctor_args (get_tenv cx) ct ops.co_ctor_args = SOME payload /\
  2 * max_code_size < LENGTH code + LENGTH payload ==>
  eval_create_operands cx RawCreate hs rof tys lit vs st =
    (INR (Error (RuntimeError "create initcode too large")), st)
Proof
  strip_tac >>
  simp[eval_create_operands_def, eval_create_def, build_create_code_def,
       raw_create_initcode_def, lift_option_type_def, bind_def,
       ignore_bind_def, get_accounts_def, check_def, assert_def,
       return_def, raise_def, NOT_LESS_EQUAL]
QED

Theorem blueprint_operands_size_reject:
  create_operand_layout (CreateFromBlueprint raw) hs vs = xs /\
  dest_create_args (CreateFromBlueprint raw) hs xs = SOME ops /\
  create_arg_ctor_types (CreateFromBlueprint raw) hs tys = SOME ct /\
  blueprint_prefix_size hs lit xs st.accounts = SOME n /\
  (if raw then ops.co_ctor_args = [BytesV payload]
   else encode_create_ctor_args (get_tenv cx) ct ops.co_ctor_args = SOME payload) /\
  2 * max_code_size < n + LENGTH payload ==>
  eval_create_operands cx (CreateFromBlueprint raw) hs rof tys lit vs st =
    (INR (Error (RuntimeError "create initcode too large")), st)
Proof
  strip_tac >>
  `dest_create_args (CreateFromBlueprint F) hs xs = SOME ops` by
    fs[dest_create_args_def] >>
  `?target offset. ops.co_code_src = AddressCodeSource target /\
                   ops.co_code_offset = SOME offset` by
    (Cases_on `ops.co_code_src` >> Cases_on `ops.co_code_offset` >>
     gvs[blueprint_prefix_size_def]) >>
  Cases_on `raw` >> fs[] >>
  simp[eval_create_operands_def, check_create_blueprint_def, eval_create_def,
       build_create_code_def, lift_option_def, lift_option_type_def,
       bind_def, ignore_bind_def, get_accounts_def, check_def, assert_def,
       return_def, raise_def, NOT_LESS_EQUAL]
QED
