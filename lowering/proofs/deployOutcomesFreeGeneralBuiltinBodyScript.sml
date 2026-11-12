Theory deployOutcomesFreeGeneralBuiltinBody
Ancestors
  deployOutcomesFreeBuiltinBody deployOutcomesFreeSelectors
  deployOutcomesFreeExprBody deployOutcomesFreeGenerators exprLowering list
  deployOutcomesFreeBinaryBuiltinBody deployOutcomesFreeAggregateBuiltinBody

(* Source typing annotations need not equal either compilation annotation. *)
Theorem outcomes_free_builtin_unary_scalar_general:
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
  well_typed_builtin_app ann bi (MAP expr_type args) /\
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

Theorem outcomes_free_builtin_keccak_general:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!v st. Q st ==> Q (SND (compile_keccak256_bytes v st))) /\
  (!v m st. Q st ==> Q (SND (compile_keccak256_bytesm v m st))) /\
  (!v st. Q st ==> Q (SND (compile_keccak256_word v st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ann Keccak256 (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty Keccak256 args s))
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
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `is_bytestring_type (expr_type (HD args))`
  >- (simp[] >> pairarg_tac >> simp[outcomes_free_as_stack_val] >>
      metis_tac[pairTheory.SND]) >>
  simp[] >> Cases_on `expr_type (HD args)` >>
  simp[] >> rpt (CASE_TAC >> simp[]) >>
  pairarg_tac >> simp[outcomes_free_as_stack_val] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_builtin_modular_general:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!a b c st. Q st ==> Q (SND (compile_addmod a b c st))) /\
  (!a b c st. Q st ==> Q (SND (compile_mulmod a b c st))) /\
  (!a b st. Q st ==> Q (SND (compile_pow_mod256 a b st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ann bi (MAP expr_type args) /\
  (bi = AddMod \/ bi = MulMod \/ bi = PowMod256) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >>
  `!e ity st. MEM e args /\ Q st ==>
    Q (SND (lower_value f ce ity e st))` by
    (rpt strip_tac >>
     irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[] >>
     drule_all outcomes_free_typed_children >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `LENGTH args = 2 \/ LENGTH args = 3` by metis_tac[outcomes_free_builtin_arities] >>
  gvs[LENGTH_EQ_NUM_compute, vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[outcomes_free_as_stack_val]) >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_builtin_slice_general:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!sz st. Q st ==> Q (SND (compile_alloc_buffer sz st))) /\
  (!ops st. Q st ==> Q (SND (emit_void MSTORE ops st))) /\
  (!a b sz st. Q st ==> Q (SND (compile_slice_calldata a b sz st))) /\
  (!a b sz st. Q st ==> Q (SND (compile_slice_code a b sz st))) /\
  (!sz st. Q st ==> Q (SND (compile_slice_out_buf sz st))) /\
  (!a b c buf dat st. Q st ==> Q (SND (compile_slice_extcode a b c buf dat st))) /\
  (!a st. Q st ==> Q (SND (compile_bytestring_src a st))) /\
  (!a b c d sz st. Q st ==> Q (SND (compile_slice_data a b c d sz st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ann (Slice n) (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty (Slice n) args s))
Proof
  strip_tac >>
  `LENGTH args = 3` by metis_tac[outcomes_free_builtin_arities] >>
  `!e ity st. MEM e args /\ Q st ==>
    Q (SND (lower_value f ce ity e st))` by
    (rpt strip_tac >>
     irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[] >>
     drule_all outcomes_free_typed_children >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `is_extcode (HD args) ==> !ity st. Q st ==>
     Q (SND (lower_value f ce ity (extcode_addr_expr (HD args)) st))` by
    (rpt strip_tac >>
     `well_typed_expr env (HD args) /\
      ~supported_expr_exists constructor_call_root (HD args)` by
       (drule_all outcomes_free_typed_children >> strip_tac >>
        `args <> []` by (strip_tac >> gvs[]) >>
        drule_all outcomes_free_head >> simp[]) >>
     drule_all outcomes_free_extcode_address >> strip_tac >>
     irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
  qpat_x_assum `!e ity st. well_typed_expr _ _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!v st. Q st ==> Q (SND (unwrap_value _ _ _))` kall_tac >>
  gvs[LENGTH_EQ_NUM_compute] >>
  simp[compile_builtin_dispatch_body_def] >> rpt IF_CASES_TAC >>
  rpt (pairarg_tac >> simp[outcomes_free_as_ptr_val] >> rpt IF_CASES_TAC) >>
  `Q st1` by metis_tac[pairTheory.SND] >>
  `Q st2` by metis_tac[pairTheory.SND] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_builtin_remaining_unary_general:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
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
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ann bi (MAP expr_type args) /\
  (bi = Not \/ (?item. bi = Acc item) \/ bi = Len \/
   (?denom. bi = AsWeiValue denom) \/ bi = MethodId) /\ Q s ==>
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
  Cases_on `bi` >> gvs[] >> simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[outcomes_free_as_stack_val, outcomes_free_as_ptr_val]) >>
  rpt IF_CASES_TAC >> gvs[outcomes_free_as_stack_val, outcomes_free_as_ptr_val, AllCaseEqs()]
  >~ [`Q (SND (emit_op ISZERO [v] st1))`]
  >- (qpat_x_assum `!ops st. Q st ==> Q (SND (emit_op ISZERO ops st))`
        (qspecl_then [`[v]`, `st1`] mp_tac) >>
      qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
        (qspecl_then [`expr_type (HD args)`, `s`] mp_tac) >> gvs[])
  >~ [`Q (SND (compile_invert v ity ce st1))`]
  >- (qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
        (qspecl_then [`ity`, `s`] mp_tac) >> gvs[] >> strip_tac >> simp[])
  >~ [`Q (SND (compile_builtin_len _ _ _ _ st1))`]
  >- (qpat_x_assum `!e ity st. _`
        (qspecl_then [`HD args`, `ty`, `s`] mp_tac) >> gvs[] >> strip_tac >> simp[])
  >~ [`Q (SND (compile_as_wei_value_decimal _ _ _ st1))`]
  >- (qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
        (qspecl_then [`expr_type (HD args)`, `s`] mp_tac) >> gvs[] >> strip_tac >> simp[])
  >~ [`Q (SND (compile_as_wei_value_int _ _ _ st1))`]
  >- (qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
        (qspecl_then [`expr_type (HD args)`, `s`] mp_tac) >> gvs[] >> strip_tac >> simp[]) >>
  qpat_x_assum `!ity st. Q st ==> Q (SND (lower_value _ _ ity _ st))`
    (qspecl_then [`expr_type (HD args)`, `s`] mp_tac) >>
  gvs[] >> strip_tac >> Cases_on `method_id_literal (HD args)` >>
  simp[outcomes_free_as_stack_val, outcomes_free_as_ptr_val]
QED

Theorem outcomes_free_builtin_binary_general:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!es st. EVERY (\e. well_typed_expr env e /\
      ~supported_expr_exists constructor_call_root e) es /\ Q st ==>
      Q (SND (compile_multi_exprs f ce es st))) /\
  (!v es st. Q st ==> Q (SND (compile_list_membership_in v es st))) /\
  (!v es st. Q st ==> Q (SND (compile_list_membership_notin v es st))) /\
  (!v arr ity flag st. Q st ==>
      Q (SND (compile_var_array_membership ce v arr ity flag st))) /\
  (!v st. Q st ==> Q (SND (compile_bytestring_hash v st))) /\
  (!ops st. Q st ==> Q (SND (emit_op EQ ops st))) /\
  (!ops st. Q st ==> Q (SND (emit_op ISZERO ops st))) /\
  (!op v w ity a b st. Q st ==> Q (SND (compile_binop op v w ity a b st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\
  well_typed_builtin_app ann (Bop op) (MAP expr_type args) /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty (Bop op) args s))
Proof
  strip_tac >>
  `EVERY (\e. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e) args` by
    metis_tac[outcomes_free_typed_children] >>
  drule_all outcomes_free_binary_selectors >> strip_tac >>
  `!e ity st. (e = HD args \/ e = HD (TL args)) /\ Q st ==>
    Q (SND (lower_value f ce ity e st))` by
    (rpt strip_tac >> irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> gvs[]) >>
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `(op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args)))`
  >- (simp[] >> pairarg_tac >> simp[] >>
      `Q st1` by metis_tac[pairTheory.SND] >>
      Cases_on `HD (TL args)` >> simp[]
      >~ [`HD (TL args) = Builtin bty b es`]
      >- (Cases_on `b` >> simp[]
          >~ [`MakeArray a n`] >-
            (`EVERY (\e. well_typed_expr env e /\
                ~supported_expr_exists constructor_call_root e) es` by
               (gvs[] >> metis_tac[outcomes_free_make_array_children]) >>
             pairarg_tac >> simp[] >> `Q st2` by metis_tac[pairTheory.SND] >>
             Cases_on `op = In` >> simp[outcomes_free_as_stack_val]) >>
          pairarg_tac >> simp[outcomes_free_as_stack_val] >> fs[] >> metis_tac[pairTheory.SND]) >>
      pairarg_tac >> simp[outcomes_free_as_stack_val] >> fs[] >> metis_tac[pairTheory.SND]) >>
  simp[] >>
  Cases_on `is_bytestring_type (expr_type (HD args)) /\ (op = Eq \/ op = NotEq)`
  >- (`!e ity st. (e = HD args \/ e = HD (TL args)) /\ Q st ==>
        Q (SND (case bytestring_literal_hash e of
          SOME h => (Lit h, st)
        | NONE => (\(m, st'). compile_bytestring_hash m st')
                    (lower_value f ce ity e st)))` by
        (rpt strip_tac >> irule outcomes_free_literal_or_hash >> simp[]) >>
      simp[] >> pairarg_tac >> simp[] >> `Q st2` by metis_tac[pairTheory.SND] >>
      pairarg_tac >> simp[] >> `Q st4` by metis_tac[pairTheory.SND] >>
      Cases_on `op = Eq` >> simp[outcomes_free_as_stack_val] >>
      pairarg_tac >> simp[outcomes_free_as_stack_val] >> metis_tac[pairTheory.SND]) >>
  simp[] >> ntac 2 (pairarg_tac >> simp[outcomes_free_as_stack_val]) >>
  metis_tac[pairTheory.SND]
QED

(* All generator and callback contracts are retained from the original
   certificate. Only the source result annotation is generalized. *)
Theorem outcomes_free_builtin_body_general:
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
  well_typed_builtin_app ann bi (MAP expr_type args) /\
  ~precompile_builtin bi /\ Q s ==>
  Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >> Cases_on `bi` >> gvs[vyperInterpreterTheory.precompile_builtin_def]
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Bop _)`]
  >- (irule outcomes_free_builtin_binary_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Keccak256`]
  >- (irule outcomes_free_builtin_keccak_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Concat _)`]
  >- (irule outcomes_free_builtin_concat >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Slice _)`]
  >- (irule outcomes_free_builtin_slice_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _)`]
  >- (irule outcomes_free_builtin_make_array >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Env _)`]
  >- (irule outcomes_free_builtin_environment >> simp[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ CalldataLen`]
  >- (irule outcomes_free_builtin_environment >> simp[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Not`]
  >- (irule outcomes_free_builtin_remaining_unary_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Acc _)`]
  >- (irule outcomes_free_builtin_remaining_unary_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ Len`]
  >- (irule outcomes_free_builtin_remaining_unary_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (AsWeiValue _)`]
  >- (irule outcomes_free_builtin_remaining_unary_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ MethodId`]
  >- (irule outcomes_free_builtin_remaining_unary_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ AddMod`]
  >- (irule outcomes_free_builtin_modular_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ MulMod`]
  >- (irule outcomes_free_builtin_modular_general >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ PowMod256`]
  >- (irule outcomes_free_builtin_modular_general >> simp[] >> metis_tac[]) >>
  irule outcomes_free_builtin_unary_scalar_general >> simp[] >> metis_tac[]
QED
