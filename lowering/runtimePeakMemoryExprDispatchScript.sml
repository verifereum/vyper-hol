(* Builtin and expression dispatch preserve the completed allocation windows. *)
Theory runtimePeakMemoryExprDispatch
Ancestors
  runtimePeakMemoryExpr runtimePeakMemoryArity runtimePeakMemorySourceGate runtimePeakMemoryBuiltins
  exprValueWrapperStateProps
  runtimePeakMemoryAbi runtimePeakMemoryCode exprLowering exprCallBounds
  exprCallbackContracts exprSimHypsDefs exprCallbackSupport loweringShapeProps
  boolChainOperandsSupported supportedExprTraverse vyperAST
  builtinSimple compileEnv context emitHelper venomInst list arithmetic

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer, dalloca_windows_ptr_access])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

Theorem builtin_operand_members[local]:
  (1 <= LENGTH xs ==> MEM (HD xs) xs) /\
  (2 <= LENGTH xs ==> MEM (HD (TL xs)) xs)
Proof
  Cases_on `xs` >> simp[] >> Cases_on `t` >> simp[]
QED

val window_state_rule = SIMP_RULE (srw_ss()) [dalloca_windows_result_state];

fun finish_window_state thms =
  let
    val stages = map (irule o window_state_rule)
      (map DISCH_ALL (CONJUNCTS (UNDISCH dalloca_windows_emit_helpers)) @
       [dalloca_windows_lower_value, dalloca_windows_alloc_buffer,
        dalloca_windows_unwrap_value, dalloca_windows_new_block] @
       CONJUNCTS dalloca_windows_fresh @ thms)
  in
    RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
    rpt (FIRST
      (CHANGED_TAC (simp[dalloca_windows_state_wrappers, builtin_operand_members, EL_MEM]) ::
       gen_tac :: conj_tac :: strip_tac :: first_assum irule :: stages))
  end;

Theorem dalloca_windows_acc:
  preserves_dalloca_windows window (cfn cenv (BaseT AddressT) e) ==>
  preserves_dalloca_windows window (compile_acc cfn cenv e item)
Proof
  Cases_on `item` >> Cases_on `is_self_addr e` >>
  simp[dalloca_windows_result_state, compile_acc_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >> finish_window_state []
QED

Theorem dalloca_windows_array_membership:
  preserves_dalloca_windows window (compile_var_array_membership cenv n vv ty is_in)
Proof
  simp[compile_var_array_membership_def] >>
  windows_tac [dalloca_windows_array_membership_loop]
QED

Theorem dalloca_windows_bytestring_widen_copy:
  preserves_dalloca_windows window (compile_bytestring_widen_copy dst_sz v src_sz)
Proof
  simp[compile_bytestring_widen_copy_def] >> windows_tac [dalloca_windows_copy_memory]
QED

Theorem dalloca_windows_builtin_dispatch_body:
  builtin_arity bi <= LENGTH args /\
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) /\
  (!ct e. MEM e args /\ is_extcode e ==>
    preserves_dalloca_windows window (cfn cenv ct (extcode_addr_expr e))) /\
  (!ann el_ty bnd elems. MEM (Builtin ann (MakeArray el_ty bnd) elems) args ==>
    preserves_dalloca_windows window (compile_multi_exprs cfn cenv elems)) /\
  (!d n e. bi = BoolChain d n /\ MEM e (bool_chain_operands d (n - 1) (HD args)) ==>
    preserves_dalloca_windows window (cfn cenv (BaseT BoolT) e)) ==>
  preserves_dalloca_windows window (compile_builtin_dispatch_body cfn cenv rt ty bi args)
Proof
  `!es d result exit_lbl.
     (!e. MEM e es ==> preserves_dalloca_windows window (cfn cenv (BaseT BoolT) e)) ==>
     preserves_dalloca_windows window (compile_bool_chain_ops cfn cenv d result exit_lbl es)` by
    (Induct_on `es` >- simp[compile_bool_chain_ops_def, dalloca_windows_return] >>
     Cases_on `es` >> simp[] >> rpt strip_tac >>
     simp[compile_bool_chain_ops_def] >>
     windows_tac [dalloca_windows_lower_value] >>
     first_x_assum irule >> rpt strip_tac >> first_assum irule >> gvs[MEM]) >>
  Cases_on `bi = NamedConst`
  >- (gvs[dalloca_windows_result_state, compile_builtin_dispatch_body_def, builtin_arity_def,
          dalloca_windows_state_wrappers, LET_THM, pairTheory.UNCURRY] >>
      rpt strip_tac >> Cases_on `is_word_type rt` >>
      finish_window_state []) >>
  Cases_on `?d n. bi = BoolChain d n`
  >- (gvs[] >> rpt strip_tac >>
      `preserves_dalloca_windows window
         (compile_bool_chain_ops cfn cenv d result exit_lbl
            (bool_chain_operands d (n - 1) (HD args)))` by metis_tac[] >>
      simp[dalloca_windows_result_state, compile_builtin_dispatch_body_def, LET_THM,
           pairTheory.UNCURRY] >>
      finish_window_state []) >>
  Cases_on `bi` >>
  gvs[dalloca_windows_result_state, compile_builtin_dispatch_body_def, builtin_arity_def,
       dalloca_windows_state_wrappers, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >>
  TRY (`MEM (HD args) args` by simp[builtin_operand_members]) >>
  TRY (`MEM (HD (TL args)) args` by simp[builtin_operand_members]) >>
  windows_tac [] >> gvs[] >>
  finish_window_state
    (List.concat (map CONJUNCTS
      [dalloca_windows_base_operations, dalloca_windows_hash_ops,
       dalloca_windows_bytes_ops, dalloca_windows_list_membership,
       dalloca_windows_simple_values]) @
     [dalloca_windows_acc, dalloca_windows_binop, dalloca_windows_array_membership,
      dalloca_windows_concat, dalloca_windows_make_tuple, dalloca_windows_make_array,
      REWRITE_RULE [GSYM compile_builtin_len_def] (cj 1 dalloca_windows_ptr_access)]) >>
  rpt (first_assum irule >> simp[]) >>
  simp[EL_MEM, builtin_operand_members] >> metis_tac[]
QED

Theorem dalloca_windows_type_builtin_dispatch_body:
  type_builtin_arity tb <= LENGTH args /\
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_type_builtin_dispatch_body cfn cenv vt ty tb rt args)
Proof
  strip_tac >>
  `preserves_dalloca_windows window (compile_abi_encode_args cfn cenv args)` by
    metis_tac[dalloca_windows_abi_encode_args] >>
  Cases_on `tb` >>
  fs[dalloca_windows_result_state, compile_type_builtin_dispatch_body_def,
       type_builtin_arity_def, dalloca_windows_state_wrappers, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >> windows_tac [] >> gvs[] >>
  finish_window_state
    (List.concat (map CONJUNCTS
      [dalloca_windows_base_operations, dalloca_windows_bytes_ops]) @
     [dalloca_windows_convert, dalloca_windows_bytestring_widen_copy,
      dalloca_windows_lower_abi_encode, dalloca_windows_lower_abi_decode,
      dalloca_windows_abi_encode_payload, dalloca_windows_clamp_basetype]) >>
  rpt (first_assum irule >> simp[]) >>
  simp[EL_MEM, builtin_operand_members]
QED

Theorem expr_dispatch_defaults_gate[local]:
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
    compile_env_blueprint_free cenv) /\
  compile_env_builtin_arity cenv ==>
  !name n.
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
      compile_env_blueprint_free (cenv_without_defaults cenv name)) /\
    compile_env_builtin_arity (cenv_without_defaults cenv name) /\
    (!e. MEM e (omitted_defaults cenv name n) ==>
         (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
           ~supported_expr_exists blueprint_create_root e) /\
         ~supported_expr_exists short_builtin_args e)
Proof
  strip_tac >> rpt gen_tac >>
  drule (SIMP_RULE (srw_ss()) [EVERY_MEM] omitted_defaults_builtin_arity) >>
  strip_tac >>
  Cases_on `!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1` >>
  fs[] >- metis_tac[] >>
  drule (SIMP_RULE (srw_ss()) [EVERY_MEM] omitted_defaults_blueprint_free) >>
  metis_tac[]
QED

Theorem dalloca_windows_expr_call[local]:
  (!ct env e. (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free env) /\ compile_env_builtin_arity env /\
              (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root e) /\
              ~supported_expr_exists short_builtin_args e ==>
     preserves_dalloca_windows window (cfn env ct e)) /\
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free cenv) /\ compile_env_builtin_arity cenv /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root (Call rt target args d)) /\
  ~supported_expr_exists short_builtin_args (Call rt target args d) ==>
  preserves_dalloca_windows window (compile_call cfn cenv rt ty target args d)
Proof
  strip_tac >>
  `!ct e. MEM e (call_callback_children args d) ==>
     preserves_dalloca_windows window (cfn cenv ct e)` by
    (rpt strip_tac >> first_assum irule >> simp[] >>
     metis_tac[call_callback_child_supported]) >>
  Q.SUBGOAL_THEN
    `(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) \/
     (!raw salted rof order. target <> CreateTarget (CreateFromBlueprint raw) salted rof order)`
    assume_tac
  >- (Cases_on `!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1` >>
      fs[supported_expr_exists_def, blueprint_create_root_def]) >>
  irule dalloca_windows_compile_call >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_assum irule >>
      simp[call_callback_children_def, MEM_APPEND, MEM_FLAT, MEM_MAP] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> first_assum irule >> simp[call_callback_children_def]) >>
  rpt strip_tac >> rename1 `MEM e (omitted_defaults cenv (nsid_to_string id) (LENGTH args))` >>
  drule_all expr_dispatch_defaults_gate >>
  disch_then (qspecl_then [`nsid_to_string id`, `LENGTH args`] strip_assume_tac) >>
  first_assum irule >> simp[] >> metis_tac[]
QED

Theorem dalloca_windows_modular_names:
  preserves_dalloca_windows window (compile_addmod_names cenv rt aty a bty b mty m) /\
  preserves_dalloca_windows window (compile_mulmod_names cenv rt aty a bty b mty m) /\
  preserves_dalloca_windows window (compile_powmod256_names cenv rt aty a bty b)
Proof
  simp[dalloca_windows_result_state, compile_addmod_names_def, compile_mulmod_names_def,
       compile_powmod256_names_def, dalloca_windows_state_wrappers, LET_THM,
       pairTheory.UNCURRY] >>
  rpt strip_tac >>
  finish_window_state (List.concat (map CONJUNCTS
    [dalloca_windows_base_operations, dalloca_windows_simple_values]))
QED

Theorem supported_expr_exists_nested[local]:
  (!p e. supported_expr_exists (supported_expr_exists p) e = supported_expr_exists p e) /\
  (!p t. supported_target_exists (supported_expr_exists p) t = supported_target_exists p t) /\
  (!p es. supported_exprs_exists (supported_expr_exists p) es = supported_exprs_exists p es) /\
  (!p opt. supported_opt_exists (supported_expr_exists p) opt = supported_opt_exists p opt) /\
  (!p fs. supported_fields_exists (supported_expr_exists p) fs = supported_fields_exists p fs)
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  simp[supported_expr_exists_def] >> metis_tac[]
QED

Theorem supported_target_contains_expr:
  supported_target_exists ($= e) target /\ supported_expr_exists p e ==>
  supported_target_exists p target
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`$= e`, `target`, `supported_expr_exists p`]
    (cj 2 supported_expr_exists_mono)) >>
  simp[supported_expr_exists_nested]
QED

Theorem dalloca_windows_expr_body[local]:
  (!env ct e. (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free env) /\ compile_env_builtin_arity env /\
              (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root e) /\
              ~supported_expr_exists short_builtin_args e ==>
     preserves_dalloca_windows window (cfn env ct e)) /\
  (!ann bi args. e = Builtin ann bi args ==>
      preserves_dalloca_windows window (bfn cenv ann ty bi args)) /\
  (!ann tb rt args. e = TypeBuiltin ann tb rt args ==>
      preserves_dalloca_windows window (tfn cenv ann ty tb rt args)) /\
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free cenv) /\ compile_env_builtin_arity cenv /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root e) /\
  ~supported_expr_exists short_builtin_args e ==>
  preserves_dalloca_windows window (compile_expr_body cfn bfn tfn cenv ty e)
Proof
  strip_tac >> Cases_on `e` >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (Call ann target args d)`] >-
    (`compile_expr_body cfn bfn tfn cenv ty (Call ann target args d) =
       compile_call cfn cenv ann ty target args d` by
       simp[FUN_EQ_THM, compile_expr_body_def, expr_type_def] >>
     pop_assum SUBST1_TAC >> irule dalloca_windows_expr_call >> metis_tac[]) >>
  gvs[supported_expr_exists_def] >>
  simp[dalloca_windows_result_state] >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (Builtin ann bi args) _`] >-
    (Cases_on `names_builtin bi args` >-
       (qpat_x_assum `names_builtin bi args` mp_tac >>
        map_every qid_spec_tac [`args`, `bi`] >>
        recInduct names_builtin_ind >>
        simp[names_builtin_def, compile_expr_body_def, expr_type_def,
             SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
               dalloca_windows_modular_names]) >>
     simp[compile_expr_body_builtin_dispatch] >> finish_window_state []) >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >-
    (simp[compile_expr_body_def, expr_type_def, LET_THM, pairTheory.UNCURRY] >>
     rpt strip_tac >> COND_CASES_TAC >> simp[] >>
     finish_window_state [cj 3 dalloca_windows_simple_values]) >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (TopLevelName _ _) _`] >-
    (simp[compile_expr_body_def, expr_type_def, LET_THM, pairTheory.UNCURRY] >>
     rpt strip_tac >> windows_tac [] >> finish_window_state []) >>
  simp[compile_expr_body_def, expr_type_def, LET_THM, pairTheory.UNCURRY] >>
  simp (map window_state_rule (CONJUNCTS dalloca_windows_simple_values)) >>
  rpt strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
  all_tac >~ [`compile_subscript _ _ _ _ _ _ _`] >-
    (irule (window_state_rule dalloca_windows_compile_subscript) >> metis_tac[]) >>
  all_tac >~ [`compile_attribute _ _ _ _ _ _ _`] >-
    (irule (window_state_rule dalloca_windows_compile_attribute) >> metis_tac[]) >>
  all_tac >~ [`compile_struct_lit _ _ _ _ _ _ _`] >-
    (irule (window_state_rule dalloca_windows_compile_struct_lit) >>
     simp[window_state_rule dalloca_windows_alloc_buffer] >>
     rpt strip_tac >> first_assum irule >> simp[] >>
     fs[supported_fields_exists_every, EXISTS_MEM, MEM_MAP, combinTheory.o_DEF] >>
     metis_tac[]) >>
  all_tac >~ [`compile_dynarray_pop _ _ _ _ _ _ _`] >-
    (irule (window_state_rule (cj 4 dalloca_windows_indexing)) >>
     irule (window_state_rule dalloca_windows_get_target_ptr) >> simp[] >>
     rpt strip_tac >> first_assum irule >> simp[] >>
     metis_tac[supported_target_contains_expr]) >>
  metis_tac[]
QED

Theorem dalloca_windows_invalid_expr_call:
  preserves_dalloca_windows window (invalid_expr_call ty)
Proof
  simp[dalloca_windows_result_state, invalid_expr_call_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >> finish_window_state []
QED

Theorem dalloca_windows_expr_child[local]:
  (!e cenv ty st. expr_size e + cenv_defaults_size cenv < bound ==>
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free cenv) /\ compile_env_builtin_arity cenv /\
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root e) /\
    ~supported_expr_exists short_builtin_args e /\
    compiler_dalloca_windows window st ==>
    compiler_dalloca_windows window (SND (compile_expr cenv ty e st))) ==>
  !e cenv ty.
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free cenv) /\ compile_env_builtin_arity cenv /\
    (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root e) /\
    ~supported_expr_exists short_builtin_args e ==>
    preserves_dalloca_windows window (expr_child_callback bound compile_expr cenv ty e)
Proof
  simp[dalloca_windows_result_state, expr_child_callback_def] >>
  rpt strip_tac >> COND_CASES_TAC >> simp[] >>
  TRY (first_assum irule >> simp[] >> NO_TAC) >>
  finish_window_state [dalloca_windows_invalid_expr_call]
QED

Theorem dalloca_windows_builtin_children[local]:
  (!e ct. (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root e) /\
          ~supported_expr_exists short_builtin_args e ==>
          preserves_dalloca_windows window (cfn cenv ct e)) /\
  builtin_arity bi <= LENGTH args /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_exprs_exists blueprint_create_root args) /\
  ~supported_exprs_exists short_builtin_args args ==>
  preserves_dalloca_windows window (compile_builtin_dispatch_body cfn cenv rt ty bi args)
Proof
  strip_tac >>
  `!e ct. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)` by
    metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
  irule dalloca_windows_builtin_dispatch_body >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[builtin_arity_def] >>
      `MEM (HD args) args` by simp[builtin_operand_members] >>
      qpat_assum `!e ct. (_ /\ _) ==> preserves_dalloca_windows window (cfn cenv ct e)` irule >>
      `!p. ~supported_exprs_exists p args ==> ~supported_expr_exists p e` by
        (gen_tac >> disch_tac >>
         `~supported_expr_exists p (HD args)` by
           metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
         `EVERY (\child. ~supported_expr_exists p child)
            (bool_chain_operands d (n - 1) (HD args))` by
           (irule bool_chain_operands_supported >> simp[]) >>
         fs[EVERY_MEM]) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!e ct. (_ /\ _) ==> preserves_dalloca_windows window (cfn cenv ct e)` irule >>
      metis_tac[expr_shape_extcode_addr, supported_exprs_exists_every, EXISTS_MEM]) >>
  rpt strip_tac >> irule dalloca_windows_multi_exprs >>
  rpt strip_tac >>
  qpat_assum `!e ct. (_ /\ _) ==> preserves_dalloca_windows window (cfn cenv ct e)` irule >>
  metis_tac[supported_exprs_exists_every, EXISTS_MEM, supported_expr_exists_def]
QED

Theorem dalloca_windows_compile_expr_mutual[local]:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) ==>
  ((!ce ty e st.
     (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free ce) /\ compile_env_builtin_arity ce /\
     (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root e) /\
     ~supported_expr_exists short_builtin_args e /\
     compiler_dalloca_windows window st ==>
     compiler_dalloca_windows window (SND (compile_expr ce ty e st))) /\
   (!ce rt ty bi args st.
     (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free ce) /\ compile_env_builtin_arity ce /\
     builtin_arity bi <= LENGTH args /\
     (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_exprs_exists blueprint_create_root args) /\
     ~supported_exprs_exists short_builtin_args args /\
     compiler_dalloca_windows window st ==>
     compiler_dalloca_windows window (SND (compile_builtin_dispatch ce rt ty bi args st))) /\
   (!ce vt ty tb rt args st.
     (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free ce) /\ compile_env_builtin_arity ce /\
     type_builtin_arity tb <= LENGTH args /\
     (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_exprs_exists blueprint_create_root args) /\
     ~supported_exprs_exists short_builtin_args args /\
     compiler_dalloca_windows window st ==>
     compiler_dalloca_windows window
       (SND (compile_type_builtin_dispatch ce vt ty tb rt args st))))
Proof
  strip_tac >> ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [NOT_CLAUSES, AND_CLAUSES]) >> rpt strip_tac >>
  first_assum (assume_tac o MATCH_MP dalloca_windows_expr_child) >>
  simp[Once compile_expr_raw_def, Excl "expr_child_callback_def",
       Excl "builtin_child_callback_def", Excl "type_child_callback_def"] >>
  CONV_TAC (DEPTH_CONV ETA_CONV)
  >- (irule (window_state_rule dalloca_windows_expr_body) >>
      fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
         Excl "type_child_callback_def"] >>
      conj_tac >- (RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
                   metis_tac[]) >>
      conj_tac >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
        fs[builtin_child_callback_def, supported_expr_exists_def, short_builtin_args_def,
           expr_size_def] >>
        rpt strip_tac >> first_assum irule >> simp[] >> metis_tac[]) >>
      rpt gen_tac >> disch_then SUBST_ALL_TAC >>
      fs[type_child_callback_def, supported_expr_exists_def, short_builtin_args_def,
         expr_size_def] >>
      rpt strip_tac >> first_assum irule >> simp[] >> metis_tac[])
  >- (irule (window_state_rule dalloca_windows_builtin_children) >>
      fs[Excl "expr_child_callback_def"] >>
      RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >> metis_tac[]) >>
  irule (window_state_rule dalloca_windows_type_builtin_dispatch_body) >>
  fs[Excl "expr_child_callback_def", supported_exprs_exists_every, EXISTS_MEM] >>
  RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >> metis_tac[]
QED

Theorem dalloca_windows_compile_expr:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        compile_env_blueprint_free cenv) /\ compile_env_builtin_arity cenv /\
  (~(!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
        ~supported_expr_exists blueprint_create_root e) /\
  ~supported_expr_exists short_builtin_args e ==>
  preserves_dalloca_windows window (compile_expr cenv ty e)
Proof
  simp[dalloca_windows_result_state] >>
  metis_tac[dalloca_windows_compile_expr_mutual]
QED
