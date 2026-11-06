Theory createSourceSizeBoundaryTest
Ancestors
  vyperCreate vyperState vyperValue vfmConstants byte
Libs
  wordsLib

Theorem raw_create_oversized_total_rejected:
  encode_create_ctor_args tenv tys ops.co_ctor_args = SOME args /\
  49152 < LENGTH bytecode + LENGTH args ==>
  OPTION_MAP (\info. info.cc_size_ok)
    (build_create_code tenv RawCreate
      (ops with co_code_src := BytecodeCodeSource bytecode)
      accounts tys blueprint_size) = SOME F
Proof
  rw[build_create_code_def, raw_create_initcode_def, max_code_size_def]
QED

Theorem raw_create_total_at_limit_accepted:
  encode_create_ctor_args tenv tys ops.co_ctor_args = SOME args /\
  LENGTH bytecode + LENGTH args = 49152 ==>
  OPTION_MAP (\info. info.cc_size_ok)
    (build_create_code tenv RawCreate
      (ops with co_code_src := BytecodeCodeSource bytecode)
      accounts tys blueprint_size) = SOME T
Proof
  rw[build_create_code_def, raw_create_initcode_def, max_code_size_def]
QED

Theorem oversized_create_rejected_before_oracle:
  dest_create_args kind has_salt vs = SOME ops /\
  create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys /\
  build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size =
    SOME info /\ info.cc_source_ok /\ ~info.cc_size_ok ==>
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st =
    (INR (Error (RuntimeError "create initcode too large")),st)
Proof
  strip_tac >>
  simp[eval_create_def, lift_option_type_def, bind_def, ignore_bind_def,
       get_accounts_def, check_def, assert_def, return_def, raise_def]
QED

(* Arbitrary st.outcomes and rof cover concrete and oracle modes, including
   an empty oracle queue, without consuming an outcome or recording a request. *)
Theorem raw_create_49184_rejected_before_oracle:
  eval_create cx RawCreate F rof
    [BaseT (BytesT (Dynamic 49152)); BaseT (UintT 256); BaseT (UintT 256)]
    [BytesV (REPLICATE 49152 0w); IntV 0; IntV 0] NONE st =
  (INR (Error (RuntimeError "create initcode too large")),st)
Proof
  `encode_create_ctor_args (get_tenv cx) [BaseT (UintT 256)] [IntV 0] =
   SOME (REPLICATE 32 0w)` by EVAL_TAC >>
  simp[eval_create_def, lift_option_type_def, bind_def, ignore_bind_def,
       get_accounts_def, check_def, assert_def, return_def, raise_def,
       dest_create_args_def, make_create_operands_def, dest_NumV_def,
       dest_BytesV_def, dest_optional_num_def, dest_optional_salt_def,
       create_arg_ctor_types_def, build_create_code_def,
       raw_create_initcode_def, max_code_size_def]
QED
