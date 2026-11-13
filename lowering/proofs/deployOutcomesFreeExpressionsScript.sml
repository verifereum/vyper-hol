Theory deployOutcomesFreeExpressions
Ancestors
  deployOutcomesFreeLowering deployOutcomesFreeGenerators
  exprLowering exprCallBounds e2eDeployDefs supportedExprTraverse vyperTypeSystem
  deployOutcomesFreeExprBody deployOutcomesFreeBuiltinBody
  deployOutcomesFreeGeneralBuiltinBody
  deployOutcomesFreeExprGenerators deployOutcomesFreeBuiltinGenerators
  deployOutcomesFreeAggregateGenerators deployOutcomesFreeAbiGenerators
  deployOutcomesFreeTypeBuiltinBody deployOutcomesFreeSelectors compileEnv

(* Specialize the independently checked finite opcode certificates once. *)
val safe_generators = map
  (SRULE [DISJ_IMP_THM, FORALL_AND_THM] o
   Q.INST [`P` |-> `\op. op <> CALL /\ op <> STATICCALL /\
      op <> DELEGATECALL /\ op <> CREATE /\ op <> CREATE2 /\ op <> INVOKE`])
  [outcomes_free_emit_ops, outcomes_free_alloc_buffer,
   outcomes_free_ptr_load, outcomes_free_unwrap_value,
   outcomes_free_mapping_subscript, outcomes_free_keccak256_key,
   outcomes_free_tuple_subscript, outcomes_free_array_subscript,
   outcomes_free_dynarray_pop, outcomes_free_literal_vv, outcomes_free_name_vv,
   outcomes_free_ifexp_arm, outcomes_free_compile_addmod_names,
   outcomes_free_compile_mulmod_names, outcomes_free_compile_powmod256_names,
   outcomes_free_compile_neg, outcomes_free_compile_builtin_abs,
   outcomes_free_compile_blockhash, outcomes_free_compile_blobhash,
   outcomes_free_compile_ceil, outcomes_free_compile_floor,
   outcomes_free_compile_uint2str, outcomes_free_compile_slice_calldata,
   outcomes_free_compile_env_var, outcomes_free_compile_builtin_calldatasize,
   outcomes_free_compile_invert, outcomes_free_compile_builtin_len,
   outcomes_free_compile_as_wei_value_decimal, outcomes_free_compile_as_wei_value_int,
   outcomes_free_compile_method_id_runtime, outcomes_free_compile_addmod,
   outcomes_free_compile_mulmod, outcomes_free_compile_pow_mod256,
   outcomes_free_compile_slice_code, outcomes_free_compile_slice_out_buf,
   outcomes_free_compile_slice_extcode, outcomes_free_compile_bytestring_src,
   outcomes_free_compile_slice_data, outcomes_free_compile_keccak256_bytes,
   outcomes_free_compile_keccak256_bytesm, outcomes_free_compile_keccak256_word,
   outcomes_free_compile_list_membership_in, outcomes_free_compile_list_membership_notin,
   outcomes_free_compile_var_array_membership, outcomes_free_compile_bytestring_hash,
   outcomes_free_binop, outcomes_free_builtin_empty_complex,
   outcomes_free_bytestring_widen_copy, outcomes_free_lower_abi_encode,
   outcomes_free_type_convert, outcomes_free_extract32_load,
   outcomes_free_clamp_basetype, outcomes_free_store_memory];

val safe_simp = simp (safe_generators @
  [outcomes_free_fresh, outcomes_free_new_block, outcomes_free_lower_abi_decode]);

Theorem outcomes_free_typed_callback[local]:
  (!env e ce ty s. expr_size e < bound /\
    (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
      i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
      i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
      i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
      i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (f ce ty e s)))) ==>
  !env e ce ty s.
    (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
      i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
      i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
      i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
      i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (expr_child_callback bound f ce ty e s)))
Proof
  rpt strip_tac >> simp[expr_child_callback_def] >>
  IF_CASES_TAC >> simp[outcomes_free_invalid_expr_call] >> metis_tac[]
QED

Theorem outcomes_free_target_generators[local]:
  Q = (\s. EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)) /\
  (!env e ce ty s. (well_typed_expr env e \/
      (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (f ce ty e s))) ==>
  !t env vt ce s. type_place_target env t = SOME vt /\
    ~supported_target_exists constructor_call_root t /\ Q s ==>
    Q (SND (compile_get_target_ptr f ce t s))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule outcomes_free_typed_target_ptr >> simp[] >>
  gvs[] >> safe_simp >> conj_tac >- (first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

val safe_struct = SRULE [] (Q.INST
  [`P` |-> `\op. op <> CALL /\ op <> STATICCALL /\
    op <> DELEGATECALL /\ op <> CREATE /\ op <> CREATE2 /\ op <> INVOKE`]
  outcomes_free_struct_lit_typed);
Theorem outcomes_free_struct_generators[local]:
  Q = (\s. EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)) /\
  (!env e ce ty s. (well_typed_expr env e \/
      (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (f ce ty e s))) ==>
  !env fields ce ty buf off s.
    EVERY (\kv. well_typed_expr env (SND kv) /\
      ~supported_expr_exists constructor_call_root (SND kv)) fields /\ Q s ==>
    Q (SND (compile_struct_lit f ce ty fields buf off s))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  irule safe_struct >> simp[] >>
  conj_tac >- (simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  qexistsl [`env`, `constructor_call_root`] >> simp[] >> rpt strip_tac >>
  first_assum irule >> simp[] >> metis_tac[]
QED


Theorem outcomes_free_expr_generators[local]:
  Q = (\s. EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)) /\
  (!env e ce ty s. (well_typed_expr env e \/
      (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (f ce ty e s))) /\
  (!env ty bi args ce ct s. well_typed_expr env (Builtin ty bi args) /\
    ~supported_expr_exists constructor_call_root (Builtin ty bi args) /\ Q s ==>
    Q (SND (bc ce ty ct bi args s))) /\
  (!env ty tb rt args ce ct s. well_typed_expr env (TypeBuiltin ty tb rt args) /\
    ~supported_expr_exists constructor_call_root (TypeBuiltin ty tb rt args) /\ Q s ==>
    Q (SND (tc ce ty ct tb rt args s))) ==>
  !env e ce ty s. (well_typed_expr env e \/
      (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (compile_expr_body f bc tc ce ty e s))
Proof
  strip_tac >> gvs[] >> rpt gen_tac >> disch_tac >>
  irule (SRULE [] (Q.INST [`Q` |-> `\s. EVERY (\i.
    i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)`]
    outcomes_free_typed_expr_body)) >> simp[] >> safe_simp >>
  conj_tac >- (rpt strip_tac >> gvs[] >> safe_simp) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule (SRULE [] (Q.INST [`Q` |-> `\s. EVERY (\i.
      i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
      i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
      i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)`]
      outcomes_free_target_generators)) >> simp[] >>
    conj_tac >- (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule (SRULE [] (Q.INST [`Q` |-> `\s. EVERY (\i.
      i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
      i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
      i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)`]
      outcomes_free_struct_generators)) >> simp[] >>
    conj_tac >- (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >> metis_tac[]
QED

val safe_aggregates = map
  (SRULE [DISJ_IMP_THM, FORALL_AND_THM] o
   Q.INST [`P` |-> `\op. op <> CALL /\ op <> STATICCALL /\
      op <> DELEGATECALL /\ op <> CREATE /\ op <> CREATE2 /\ op <> INVOKE`])
  [cj 1 outcomes_free_aggregate_typed, cj 2 outcomes_free_aggregate_typed,
   cj 3 outcomes_free_aggregate_typed, cj 4 outcomes_free_aggregate_typed,
   outcomes_free_acc_typed, outcomes_free_multi_exprs_typed];

Theorem outcomes_free_builtin_generators[local]:
  Q = (\s. EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)) /\
  (!env e ce ty s. (well_typed_expr env e \/
      (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (f ce ty e s))) ==>
  !env args ce rt ty bi ety s. well_typed_expr env (Builtin ety bi args) /\
    ~supported_expr_exists constructor_call_root (Builtin ety bi args) /\ Q s ==>
    Q (SND (compile_builtin_dispatch_body f ce rt ty bi args s))
Proof
  strip_tac >> gvs[] >> rpt gen_tac >> strip_tac >>
  irule (SRULE [] (Q.INST [`ann` |-> `ety`, `Q` |-> `\s. EVERY (\i.
    i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)`]
    outcomes_free_builtin_body_general)) >>
  gvs[well_typed_expr_def, supported_expr_exists_def, constructor_call_root_def] >>
  safe_simp >> conj_tac >- suspend "generators" >> metis_tac[]
QED
Resume outcomes_free_builtin_generators[generators]:
  qexists_tac `env` >>
  `!env e ty st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\
     EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
       i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
       i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
     EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
       i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
       i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
       (state_insts (SND (f ce ty e st)))` by metis_tac[] >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule (List.nth (safe_aggregates, 4)) >> simp[] >>
    qexistsl [`env`, `constructor_call_root`] >> simp[] >> metis_tac[]) >>
  conj_tac >- (metis_tac[]) >>
  conj_tac >- (metis_tac[List.nth (safe_aggregates, 5)]) >>
  conj_tac >- (metis_tac[List.nth (safe_aggregates, 2)]) >>
  conj_tac >- (metis_tac[List.nth (safe_aggregates, 0)]) >>
  conj_tac >- (metis_tac[List.nth (safe_aggregates, 1)]) >> simp[]
QED
Finalise outcomes_free_builtin_generators

(* The dispatch only emits MSTORE; arbitrary emit_void preservation is not
   valid for the concrete invariant. This narrows that callback boundary. *)
Theorem outcomes_free_type_encode_mstore[local]:
  (!e ity st. well_typed_expr env e /\
     ~supported_expr_exists constructor_call_root e /\ Q st ==>
     Q (SND (f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!n st. Q st ==> Q (SND (compile_alloc_buffer n st))) /\
  (!vs st. Q st ==> Q (SND (emit_void MSTORE vs st))) /\
  (!(ensure:bool) mid v info sz st. Q st ==>
     Q (SND (lower_abi_encode ensure mid v info sz st))) /\
  (!es st. well_typed_exprs env es /\
     ~supported_exprs_exists constructor_call_root es /\ Q st ==>
     Q (SND (compile_abi_encode_args f ce es st))) /\
  (!v off vs st. Q st ==> Q (SND (compile_store_abi_tuple ce v off vs st))) /\
  well_typed_exprs env args /\
  ~supported_exprs_exists constructor_call_root args /\ Q s ==>
  Q (SND (compile_type_builtin_dispatch_body f ce rt ty
    (AbiEncode ensure mid) target_ty args s))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  IF_CASES_TAC
  >- (`well_typed_expr env (HD args) /\
       ~supported_expr_exists constructor_call_root (HD args)` by
        (drule_all outcomes_free_typed_children >> strip_tac >>
         `args <> []` by (strip_tac >> gvs[]) >>
         drule_all outcomes_free_head >> simp[]) >>
      `!ity st. Q st ==> Q (SND (lower_value f ce ity (HD args) st))` by
        (rpt strip_tac >>
         irule deployOutcomesFreeExprBodyTheory.outcomes_free_lower_value >> simp[]) >>
      IF_CASES_TAC >> rpt (pairarg_tac >> simp[]) >>
      simp[outcomes_free_as_ptr_val] >> metis_tac[pairTheory.SND]) >>
  rpt (pairarg_tac >> simp[]) >> simp[outcomes_free_as_ptr_val] >>
  metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_materialize[local]:
  (!n st. Q st ==> Q (SND (compile_alloc_buffer n st))) /\
  (!v st. Q st ==> Q (SND (unwrap_value ce v st))) /\
  (!a b ty sty st. Q st ==> Q (SND (compile_store_memory ce a b ty sty st))) /\
  Q s ==> Q (SND (compile_materialize_vv ce ty vv s))
Proof
  strip_tac >> simp[compile_materialize_vv_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> metis_tac[pairTheory.SND]
QED

val safe_type_bodies = map
  (SRULE [] o Q.INST [`Q` |-> `\s. EVERY (\i.
    i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)`])
  [outcomes_free_type_builtin_constants, outcomes_free_type_builtin_convert,
   outcomes_free_type_builtin_extract32, outcomes_free_type_builtin_decode,
   outcomes_free_type_encode_mstore, outcomes_free_materialize];

val safe_abi = map
  (SRULE [DISJ_IMP_THM, FORALL_AND_THM] o
   Q.INST [`P` |-> `\op. op <> CALL /\ op <> STATICCALL /\
      op <> DELEGATECALL /\ op <> CREATE /\ op <> CREATE2 /\ op <> INVOKE`])
  [outcomes_free_store_abi_tuple, outcomes_free_abi_encode_args_typed];

Theorem outcomes_free_type_generators[local]:
  Q = (\s. EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)) /\
  (!env e ce ty s. (well_typed_expr env e \/
      (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (f ce ty e s))) ==>
  !env args ce rt ty tb target_ty ety s.
    well_typed_expr env (TypeBuiltin ety tb target_ty args) /\
    ~supported_expr_exists constructor_call_root (TypeBuiltin ety tb target_ty args) /\ Q s ==>
    Q (SND (compile_type_builtin_dispatch_body f ce rt ty tb target_ty args s))
Proof
  strip_tac >> gvs[] >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_expr_def, supported_expr_exists_def, constructor_call_root_def] >>
  Cases_on `tb`
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Convert`] >-
    (irule (List.nth (safe_type_bodies, 1)) >> safe_simp >> metis_tac[])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ Extract32`] >-
    (irule (List.nth (safe_type_bodies, 2)) >> safe_simp >> metis_tac[])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ (AbiDecode _)`] >-
    (irule (List.nth (safe_type_bodies, 3)) >> safe_simp >> metis_tac[])
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ (AbiEncode _ _)`] >-
    suspend "encode" >>
  irule (List.nth (safe_type_bodies, 0)) >> safe_simp
QED

Resume outcomes_free_type_generators[encode]:
  irule (List.nth (safe_type_bodies, 4)) >> safe_simp >> simp safe_abi >>
  qexists_tac `env` >> simp[] >>
  conj_tac >- (metis_tac[]) >> rpt gen_tac >> strip_tac >>
  irule (List.nth (safe_abi, 1)) >> simp[] >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule (List.nth (safe_type_bodies, 5)) >> safe_simp) >>
  qexistsl [`env`, `constructor_call_root`] >> simp[] >>
  conj_tac >- (metis_tac[]) >>
  metis_tac[outcomes_free_typed_children]
QED
Finalise outcomes_free_type_generators

Theorem outcomes_free_expr_rank[local]:
  Q = (\s. EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)) ==>
  !n.
  (!e env ce ty s. 2 * expr_size e + 2 = n /\
    (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
    ~supported_expr_exists constructor_call_root e /\ Q s ==>
    Q (SND (compile_expr ce ty e s))) /\
  (!args env ce rt ty bi s. 2 * list_size expr_size args + 1 = n /\
    well_typed_expr env (Builtin rt bi args) /\
    ~supported_expr_exists constructor_call_root (Builtin rt bi args) /\ Q s ==>
    Q (SND (compile_builtin_dispatch ce rt ty bi args s))) /\
  (!args env ce rt ty tb target_ty s. 2 * list_size expr_size args + 1 = n /\
    well_typed_expr env (TypeBuiltin rt tb target_ty args) /\
    ~supported_expr_exists constructor_call_root (TypeBuiltin rt tb target_ty args) /\ Q s ==>
    Q (SND (compile_type_builtin_dispatch ce rt ty tb target_ty args s)))
Proof
  disch_tac >> completeInduct_on `n` >> conj_tac
  >- suspend "expr" >> conj_tac
  >- suspend "builtin" >> suspend "type"
QED

Resume outcomes_free_expr_rank[expr]:
  rpt gen_tac >> disch_tac >> pure_once_rewrite_tac [cj 1 compile_expr_raw_def] >>
  irule outcomes_free_expr_generators >>
  conj_tac >- (metis_tac[]) >>
  conj_tac >- suspend "expr_callback" >>
  conj_tac >- suspend "builtin_callback" >>
  conj_tac >- suspend "type_callback" >> metis_tac[]
QED

Resume outcomes_free_expr_rank[builtin]:
  rpt gen_tac >> strip_tac >> pure_once_rewrite_tac [cj 2 compile_expr_raw_def] >>
  irule outcomes_free_builtin_generators >>
  conj_tac >- (metis_tac[]) >>
  conj_tac >- suspend "builtin_expr_callback" >> metis_tac[]
QED

Resume outcomes_free_expr_rank[type]:
  rpt gen_tac >> strip_tac >> pure_once_rewrite_tac [cj 3 compile_expr_raw_def] >>
  pure_rewrite_tac [COND_CLAUSES] >> irule outcomes_free_type_generators >>
  conj_tac >- (metis_tac[]) >>
  conj_tac >- suspend "type_expr_callback" >> metis_tac[]
QED

Resume outcomes_free_expr_rank[expr_callback]:
  rpt gen_tac >> disch_tac >>
  pure_rewrite_tac [expr_child_callback_def] >> BETA_TAC >> IF_CASES_TAC
  >- (qpat_x_assum `!m. _` (qspec_then `2 * expr_size e' + 2` mp_tac) >>
      (impl_tac >- (gvs[])) >> disch_then (mp_tac o cj 1) >> metis_tac[]) >>
  gvs[] >> simp[outcomes_free_invalid_expr_call]
QED
Resume outcomes_free_expr_rank[builtin_callback]:
  rpt gen_tac >> disch_tac >>
  pure_rewrite_tac [builtin_child_callback_def] >> BETA_TAC >> IF_CASES_TAC
  >- (qpat_x_assum `!m. _`
        (qspec_then `2 * list_size expr_size args + 1` mp_tac) >>
      (impl_tac >- (gvs[])) >> disch_then (mp_tac o cj 2) >> metis_tac[]) >>
  gvs[] >> simp[outcomes_free_invalid_expr_call]
QED
Resume outcomes_free_expr_rank[type_callback]:
  rpt gen_tac >> disch_tac >>
  pure_rewrite_tac [type_child_callback_def] >> BETA_TAC >> IF_CASES_TAC
  >- (qpat_x_assum `!m. _`
        (qspec_then `2 * list_size expr_size args + 1` mp_tac) >>
      (impl_tac >- (gvs[])) >> disch_then (mp_tac o cj 3) >> metis_tac[]) >>
  gvs[] >> simp[outcomes_free_invalid_expr_call]
QED
Resume outcomes_free_expr_rank[builtin_expr_callback]:
  rpt gen_tac >> disch_tac >>
  pure_rewrite_tac [expr_child_callback_def] >> BETA_TAC >> IF_CASES_TAC
  >- (rename1 `compile_expr ce ty e st` >>
      qpat_x_assum `!m. _` (qspec_then `2 * expr_size e + 2` mp_tac) >>
      (impl_tac >- (gvs[])) >> disch_then (mp_tac o cj 1) >> metis_tac[]) >>
  gvs[] >> simp[outcomes_free_invalid_expr_call]
QED
Resume outcomes_free_expr_rank[type_expr_callback]:
  rpt gen_tac >> disch_tac >>
  pure_rewrite_tac [expr_child_callback_def] >> BETA_TAC >> IF_CASES_TAC
  >- (rename1 `compile_expr ce ty e st` >>
      qpat_x_assum `!m. _` (qspec_then `2 * expr_size e + 2` mp_tac) >>
      (impl_tac >- (gvs[])) >> disch_then (mp_tac o cj 1) >> metis_tac[]) >>
  gvs[] >> simp[outcomes_free_invalid_expr_call]
QED
Finalise outcomes_free_expr_rank

(* The rank is internal; consumers only need the typed source boundary. *)
Theorem outcomes_free_compile_expr:
  !env ce ty e s.
    ~supported_expr_exists constructor_call_root e /\
    (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (state_insts s) ==>
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      (state_insts (SND (compile_expr ce ty e s)))
Proof
  rpt strip_tac >>
  mp_tac (SRULE [] (Q.INST [`Q` |-> `\s. EVERY (\i.
    i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)`]
    outcomes_free_expr_rank)) >>
  disch_then (qspec_then `2 * expr_size e + 2` (mp_tac o cj 1)) >>
  gvs[] >> metis_tac[]
QED

Theorem outcomes_free_compile_get_target_ptr:
  !env ce t vt s.
    type_place_target env t = SOME vt /\
    ~supported_target_exists constructor_call_root t /\
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (state_insts s) ==>
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE])
      (state_insts (SND (compile_get_target_ptr compile_expr ce t s)))
Proof
  rpt strip_tac >> gvs[] >>
  irule (SRULE [] (Q.INST [`Q` |-> `\s. EVERY (\i.
    i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s)`]
    outcomes_free_target_generators)) >>
  simp[] >> conj_tac
  >- (metis_tac[SRULE [] outcomes_free_compile_expr]) >> metis_tac[]
QED
