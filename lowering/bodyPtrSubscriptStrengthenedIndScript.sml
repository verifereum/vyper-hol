(* Conditional evaluation-induction kernel, independent of the target. *)
Theory bodyPtrSubscriptStrengthenedInd
Ancestors
  bodyPtrCtrlCases bodyPtrExitCases bodyPtrAssignCases bodyPtrLogCases
  bodyPtrIntCallCase bodyPtrCallCases exprSimPtr
  bodyPtrIfExp bodyPtrStructLit bodyPtrPop
  bodyPtrBop bodyPtrBopIn bodyPtrMakeArray bodyPtrWordBuiltins
  bodyPtrEnvBuiltins bodyPtrHashBuiltins bodyPtrBytestringBuiltins
  bodyPtrPrecompileBuiltins bodyPtrTypeBuiltins bodyPtrAbiEncode bodyPtrAbiDecode
  bodyPtrPreds bodyPtrDefs bodySim exprSimSource supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem independent_builtin_ptr_case[local]:
  !cx ty bt es.
    (!s x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
       body_exprs_ptr_ok cx es) /\
    (!s x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s =
       (INL x,t) /\ bt = Len ==>
       body_expr_ptr_ok cx (HD es)) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  `builtin_args_length_ok bt (LENGTH es) /\ bt <> Len /\ bt <> Env MsgGas ==>
   body_exprs_ptr_ok cx es` by
    (strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def]) >>
  Cases_on `bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/ (?i. bt = Acc i) \/
             bt = BlockHash \/ bt = BlobHash \/ bt = MethodId`
  >- metis_tac[env_builtin_expr_ptr_ok] >>
  Cases_on `?bop. bt = Bop bop`
  >- (gvs[] >> Cases_on `bop = In \/ bop = NotIn`
      >- (irule bop_in_expr_ptr_ok >> gvs[]) >>
      irule bop_expr_ptr_ok >> gvs[]) >>
  Cases_on `bt` >> gvs[] >>
  FIRST (map (fn th => irule th >> simp[] >> NO_TAC)
    [make_array_expr_ptr_ok, word_builtin_expr_ptr_ok,
     hash_builtin_expr_ptr_ok, bytestring_builtin_expr_ptr_ok,
     precompile_builtin_expr_ptr_ok])
QED

Theorem independent_type_builtin_ptr_case[local]:
  !cx ty tb typ es.
    (!s x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s = (INL x,t) ==>
       body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin ty tb typ es)
Proof
  rpt gen_tac >> strip_tac >>
  `type_builtin_args_length_ok tb (LENGTH es) ==> body_exprs_ptr_ok cx es` by
    (strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def]) >>
  Cases_on `tb`
  >~ [`AbiEncode _ _`] >- (irule abi_encode_expr_ptr_ok >> simp[])
  >~ [`AbiDecode _`] >- (irule abi_decode_expr_ptr_ok >> simp[]) >>
  irule type_builtin_expr_ptr_ok >> simp[]
QED

Theorem independent_leaf_ptr_case[local]:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_ptr_ok cx e
Proof
  rpt gen_tac >> disch_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env e es` by
    (simp[expr_sim_pre_body] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[int_calls_expr_def]) >>
  metis_tac[leaf_expr_sim_ptr]
QED

Theorem strengthened_expr_ptr_induction:
  !J.
    (!cx e. J cx e ==> body_expr_ptr_ok cx e) /\
    (!cx e. (~(?a b k. e = Subscript a b k) /\
             ~(?a b f. e = Attribute a b f)) /\
            body_expr_ptr_ok cx e ==> J cx e) /\
    (!cx a b k.
       (!s r t. eval_expr cx b s = (INL r,t) ==> J cx k) /\ J cx b ==>
       J cx (Subscript a b k)) /\
    (!cx a b f. J cx b ==> J cx (Attribute a b f)) ==>
    !cx e. J cx e
Proof
  gen_tac >> strip_tac >>
  qpat_x_assum `!cx e. _ ==> body_expr_ptr_ok cx e` (mk_asm "project") >>
  qpat_x_assum `!cx e. _ ==> J cx e` (mk_asm "lift") >>
  qpat_x_assum `!cx a b k. _ ==> J cx (Subscript a b k)` (mk_asm "sub") >>
  qpat_x_assum `!cx a b f. _ ==> J cx (Attribute a b f)` (mk_asm "attr") >>
  qspecl_then [`body_stmt_ptr_ok`, `body_stmts_ptr_ok`, `body_iterator_ptr_ok`,
    `body_for_ptr_ok`, `J`, `body_exprs_ptr_ok`, `body_base_target_ptr_ok`,
    `body_base_target_ptr_ok`, `body_tuple_target_ptr_ok`,
    `body_tuple_targets_ptr_ok`, `body_results_ptr_ok`] mp_tac evaluate_ind >>
  (impl_tac >- (rpt conj_tac
    >- suspend "c00" >- suspend "c01" >- suspend "c02" >- suspend "c03"
    >- suspend "c04" >- suspend "c05" >- suspend "c06" >- suspend "c07"
    >- suspend "c08" >- suspend "c09" >- suspend "c10" >- suspend "c11"
    >- suspend "c12" >- suspend "c13" >- suspend "c14" >- suspend "c15"
    >- suspend "c16" >- suspend "c17" >- suspend "c18" >- suspend "c19"
    >- suspend "c20" >- suspend "c21" >- suspend "c22" >- suspend "c23"
    >- suspend "c24" >- suspend "c25" >- suspend "c26" >- suspend "c27"
    >- suspend "c28" >- suspend "c29" >- suspend "c30" >- suspend "c31"
    >- suspend "c32" >- suspend "c33" >- suspend "c34" >- suspend "c35"
    >- suspend "c36" >- suspend "c37" >- suspend "c38" >- suspend "c39"
    >- suspend "c40" >- suspend "c41" >- suspend "c42" >- suspend "c43"
    >- suspend "c44" >- suspend "c45" >- suspend "c46" >- suspend "c47"
    >- suspend "c48" >- suspend "c49" >- suspend "c50" >- suspend "c51"
    >- suspend "c52" >- suspend "c53" >- suspend "c54" >- suspend "c55"
    >- suspend "c56" >- suspend "c57" >- suspend "c58" >- suspend "c59"
    >- suspend "c60" >- suspend "c61" >> suspend "c62")) >> simp[]
QED

Resume strengthened_expr_ptr_induction[c00]: MATCH_ACCEPT_TAC body_pass_case_ptr
QED
Resume strengthened_expr_ptr_induction[c01]: MATCH_ACCEPT_TAC body_continue_case_ptr
QED
Resume strengthened_expr_ptr_induction[c02]: MATCH_ACCEPT_TAC body_break_case_ptr
QED
Resume strengthened_expr_ptr_induction[c03]: MATCH_ACCEPT_TAC body_return_none_case_ptr
QED
Resume strengthened_expr_ptr_induction[c04]:
  rpt strip_tac >> irule body_return_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c05]: MATCH_ACCEPT_TAC body_raise_bare_case_ptr
QED
Resume strengthened_expr_ptr_induction[c06]: MATCH_ACCEPT_TAC body_raise_unreachable_case_ptr
QED
Resume strengthened_expr_ptr_induction[c07]:
  rpt strip_tac >> irule body_raise_reason_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c08]:
  rw[body_stmt_ptr_ok_def, supported_stmt_def, supported_raise_reason_def]
QED
Resume strengthened_expr_ptr_induction[c09]:
  rpt strip_tac >> irule body_assert_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c10]:
  rpt strip_tac >> irule body_assert_unreachable_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c11]:
  rpt strip_tac >> irule body_assert_reason_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c12]:
  rw[body_stmt_ptr_ok_def, supported_stmt_def, supported_assert_reason_def]
QED

Resume strengthened_expr_ptr_induction[c13]: MATCH_ACCEPT_TAC body_log_case_ptr
QED
Resume strengthened_expr_ptr_induction[c14]:
  rpt strip_tac >> irule body_annassign_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c15]:
  rpt strip_tac >> irule body_append_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c16]:
  rpt strip_tac >> irule body_assign_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c17]:
  rpt strip_tac >> irule body_assign_tuple_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c18]:
  rpt strip_tac >> irule body_augassign_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c19]:
  rpt strip_tac >> irule body_if_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c20]: MATCH_ACCEPT_TAC body_for_case_ptr
QED
Resume strengthened_expr_ptr_induction[c21]:
  rpt strip_tac >> irule body_expr_stmt_case_ptr >>
  asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c22]: MATCH_ACCEPT_TAC body_stmts_nil_case_ptr
QED
Resume strengthened_expr_ptr_induction[c23]: MATCH_ACCEPT_TAC body_stmts_cons_case_ptr
QED
Resume strengthened_expr_ptr_induction[c24]:
  simp[body_iterator_ptr_ok_def] >> asm "project" ACCEPT_TAC
QED
Resume strengthened_expr_ptr_induction[c25]:
  rw[body_iterator_ptr_ok_def] >> asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c26]: simp[body_for_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c27]:
  rw[body_for_ptr_ok_def] >> first_x_assum irule >>
  simp[push_scope_with_var_def, return_def]
QED

Resume strengthened_expr_ptr_induction[c28]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule independent_leaf_ptr_case >> simp[]
QED
Resume strengthened_expr_ptr_induction[c29]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule independent_leaf_ptr_case >> simp[]
QED
Resume strengthened_expr_ptr_induction[c30]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule independent_leaf_ptr_case >> simp[]
QED
Resume strengthened_expr_ptr_induction[c31]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule ifexp_expr_ptr_ok >> asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c32]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule independent_leaf_ptr_case >> simp[]
QED
Resume strengthened_expr_ptr_induction[c33]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule structlit_expr_ptr_ok >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c34]:
  rpt strip_tac >> asm "sub" irule >> simp[] >> first_assum ACCEPT_TAC
QED
Resume strengthened_expr_ptr_induction[c35]:
  rpt strip_tac >> asm "attr" irule >> simp[]
QED
Resume strengthened_expr_ptr_induction[c36]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule independent_builtin_ptr_case >> asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c37]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule pop_expr_ptr_ok >> simp[]
QED
Resume strengthened_expr_ptr_induction[c38]:
  rpt strip_tac >> asm "lift" irule >> simp[] >>
  irule independent_type_builtin_ptr_case >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c39]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_send_case_ptr >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c40]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_extcall_case_ptr >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c41]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_intcall_case_ptr >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume strengthened_expr_ptr_induction[c42]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_raw_call_case_ptr >> simp[]
QED
Resume strengthened_expr_ptr_induction[c43]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_raw_call_calldata_case_ptr >> simp[]
QED
Resume strengthened_expr_ptr_induction[c44]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_raw_log_case_ptr >> simp[]
QED
Resume strengthened_expr_ptr_induction[c45]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_raw_revert_case_ptr >> simp[]
QED
Resume strengthened_expr_ptr_induction[c46]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_selfdestruct_case_ptr >> simp[]
QED
Resume strengthened_expr_ptr_induction[c47]:
  rpt strip_tac >> asm "lift" irule >> simp[] >> irule body_create_case_ptr >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume strengthened_expr_ptr_induction[c48]: simp[body_exprs_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c49]:
  rw[body_exprs_ptr_ok_def] >> asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c50]: simp[body_base_target_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c51]: simp[body_base_target_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c52]: simp[body_base_target_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c53]:
  rw[body_base_target_ptr_ok_def] >> asm_x "project" mp_tac >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c54]: simp[]
QED
Resume strengthened_expr_ptr_induction[c55]: simp[body_tuple_target_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c56]: simp[body_tuple_target_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c57]: simp[body_tuple_target_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c58]:
  rw[body_tuple_target_ptr_ok_def] >> metis_tac[]
QED
Resume strengthened_expr_ptr_induction[c59]: simp[body_tuple_target_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c60]: simp[body_tuple_target_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c61]: simp[body_results_ptr_ok_def]
QED
Resume strengthened_expr_ptr_induction[c62]:
  rw[body_results_ptr_ok_def] >> asm_x "project" mp_tac >> metis_tac[]
QED

Finalise strengthened_expr_ptr_induction
