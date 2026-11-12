Theory deployOutcomesFreeBuiltinBody
Ancestors
  deployOutcomesFreeSelectors deployOutcomesFreeExprBody
  deployOutcomesFreeGenerators exprLowering list
  deployOutcomesFreeTypeBuiltinBody deployOutcomesFreeBinaryBuiltinBody
  deployOutcomesFreeAggregateBuiltinBody

(* Generator obligations are explicit, so this boundary is independent of
   their opcode-specific implementation proofs. *)
Theorem outcomes_free_builtin_unary_scalar:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!v ity st. Q st ==> Q (SND (compile_neg v ity st))) /\
  (!v st. Q st ==> Q (SND (compile_builtin_abs v st))) /\
  (!v st. Q st ==> Q (SND (compile_blockhash v st))) /\
  (!v st. Q st ==> Q (SND (compile_blobhash v st))) /\
  (!v d st. Q st ==> Q (SND (compile_ceil v d st))) /\
  (!v d st. Q st ==> Q (SND (compile_floor v d st))) /\
  (!v n sz st. Q st ==> Q (SND (compile_uint2str v n sz st))) /\
  (!v n sz st. Q st ==> Q (SND (compile_slice_calldata v n sz st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ty bi (MAP expr_type args) /\
  (bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
   bi = Ceil \/ bi = Floor \/ (?n. bi = Uint2Str n) \/
   (?n. bi = CalldataSlice n)) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >>
  `LENGTH args = 1` by metis_tac[outcomes_free_builtin_arities] >>
  `well_typed_expr env (HD args) /\
   ~supported_expr_exists constructor_call_root (HD args)` by
    (drule_all outcomes_free_typed_children >> strip_tac >>
     `args <> []` by (strip_tac >> gvs[]) >>
     drule_all outcomes_free_head >> simp[]) >>
  `!ity st. Q st ==> Q (SND (lower_value f ce ity (HD args) st))` by
    (rpt strip_tac >> irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
  Cases_on `bi` >> gvs[] >>
  simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[outcomes_free_as_stack_val, outcomes_free_as_ptr_val] >>
  metis_tac[pairTheory.SND]
QED

(* The type-builtin interface is outcomes_free_type_builtin_body from the
   imported TypeBuiltinBody theory; do not duplicate its statement here. *)
Theorem outcomes_free_builtin_body:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!v ity st. Q st ==> Q (SND (compile_neg v ity st))) /\
  (!v st. Q st ==> Q (SND (compile_builtin_abs v st))) /\
  (!v st. Q st ==> Q (SND (compile_blockhash v st))) /\
  (!v st. Q st ==> Q (SND (compile_blobhash v st))) /\
  (!v d st. Q st ==> Q (SND (compile_ceil v d st))) /\
  (!v d st. Q st ==> Q (SND (compile_floor v d st))) /\
  (!v n sz st. Q st ==> Q (SND (compile_uint2str v n sz st))) /\
  (!v n sz st. Q st ==> Q (SND (compile_slice_calldata v n sz st))) /\
  (!item st. Q st ==> Q (SND (compile_env_var item st))) /\
  (!st. Q st ==> Q (SND (compile_builtin_calldatasize st))) /\
  (!v ity st. Q st ==> Q (SND (compile_invert v ity ce st))) /\
  (!ops st. Q st ==> Q (SND (emit_op ISZERO ops st))) /\
  (!e item st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (compile_acc f ce e item st))) /\
  (!v loc st. Q st ==>
     Q (SND (compile_builtin_len ce.ce_is_ctor ce.ce_imm_alloca v loc st))) /\
  (!v m d st. Q st ==> Q (SND (compile_as_wei_value_decimal v m d st))) /\
  (!v m sg st. Q st ==> Q (SND (compile_as_wei_value_int v m sg st))) /\
  (!ity lit st. Q st ==> Q (SND (compile_literal_vv ity lit st))) /\
  (!ity v fixed st. Q st ==> Q (SND (compile_method_id_runtime ity v fixed st))) /\
  (!a b c st. Q st ==> Q (SND (compile_addmod a b c st))) /\
  (!a b c st. Q st ==> Q (SND (compile_mulmod a b c st))) /\
  (!a b st. Q st ==> Q (SND (compile_pow_mod256 a b st))) /\
  (!sz st. Q st ==> Q (SND (compile_alloc_buffer sz st))) /\
  (!ops st. Q st ==> Q (SND (emit_op ADD ops st))) /\
  (!ops st. Q st ==> Q (SND (emit_op MLOAD ops st))) /\
  (!ops st. Q st ==> Q (SND (emit_void MSTORE ops st))) /\
  (!es ptr infos off st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_concat f ce es ptr infos off st))) /\
  (!es ptr off st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_make_tuple f ce es ptr off st))) /\
  (!es ety sz lw ptr st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_make_array f ce es ety sz lw ptr st))) /\
  (!a b sz st. Q st ==> Q (SND (compile_slice_code a b sz st))) /\
  (!sz st. Q st ==> Q (SND (compile_slice_out_buf sz st))) /\
  (!a b c buf dat st. Q st ==> Q (SND (compile_slice_extcode a b c buf dat st))) /\
  (!a st. Q st ==> Q (SND (compile_bytestring_src a st))) /\
  (!a b c d sz st. Q st ==> Q (SND (compile_slice_data a b c d sz st))) /\
  (!v st. Q st ==> Q (SND (compile_keccak256_bytes v st))) /\
  (!v m st. Q st ==> Q (SND (compile_keccak256_bytesm v m st))) /\
  (!v st. Q st ==> Q (SND (compile_keccak256_word v st))) /\
  (!es st. EVERY (\e. well_typed_expr env e /\
      ~supported_expr_exists constructor_call_root e) es /\ Q st ==>
      Q (SND (compile_multi_exprs f ce es st))) /\
  (!v es st. Q st ==> Q (SND (compile_list_membership_in v es st))) /\
  (!v es st. Q st ==> Q (SND (compile_list_membership_notin v es st))) /\
  (!v arr ity flag st. Q st ==>
      Q (SND (compile_var_array_membership ce v arr ity flag st))) /\
  (!v st. Q st ==> Q (SND (compile_bytestring_hash v st))) /\
  (!ops st. Q st ==> Q (SND (emit_op EQ ops st))) /\
  (!op v w ity a b st. Q st ==> Q (SND (compile_binop op v w ity a b st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ty bi (MAP expr_type args) /\
  ~precompile_builtin bi /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >> Cases_on `bi` >> gvs[vyperInterpreterTheory.precompile_builtin_def]
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Bop _)`]
  >- (irule outcomes_free_builtin_binary >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Keccak256`]
  >- (irule outcomes_free_builtin_keccak >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Concat _)`]
  >- (irule outcomes_free_builtin_concat >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Slice _)`]
  >- (irule outcomes_free_builtin_slice >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _)`]
  >- (irule outcomes_free_builtin_make_array >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Env _)`]
  >- (irule outcomes_free_builtin_environment >> simp[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ CalldataLen`]
  >- (irule outcomes_free_builtin_environment >> simp[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Not`]
  >- (irule outcomes_free_builtin_remaining_unary >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Acc _)`]
  >- (irule outcomes_free_builtin_remaining_unary >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Len`]
  >- (irule outcomes_free_builtin_remaining_unary >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (AsWeiValue _)`]
  >- (irule outcomes_free_builtin_remaining_unary >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ MethodId`]
  >- (irule outcomes_free_builtin_remaining_unary >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ AddMod`]
  >- (irule outcomes_free_builtin_modular >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ MulMod`]
  >- (irule outcomes_free_builtin_modular >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ PowMod256`]
  >- (irule outcomes_free_builtin_modular >> simp[] >> metis_tac[]) >>
  irule outcomes_free_builtin_unary_scalar >> simp[] >> metis_tac[]
QED
