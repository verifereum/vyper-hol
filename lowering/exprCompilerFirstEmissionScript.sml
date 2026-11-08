(* Simultaneous first-emission closure of the expression compiler. *)
Theory exprCompilerFirstEmission
Ancestors
  compilerFirstEmission exprPlaceFirstEmission
  guardedCallbackFirstEmission literalNameFirstEmission targetPointerFirstEmission
  accountFirstEmission abiOuterFirstEmission typeConvertFirstEmission
  exprCallFirstEmission exprAggregateFirstEmission arithmeticFirstEmission
  builtinHashFirstEmission builtinScalarFirstEmission builtinBytesFirstEmission
  membershipFirstEmission
  builtinPrefixFirstEmission exprValueFirstEmission conditionalConversionFirstEmission
  entryConditionalFirstEmission contextFirstEmission exprLowering fragExec compileEnv emitHelper venomInst context

Theorem expr_ifexp_arm_appends[local]:
  cs_appends (compile_ifexp_arm ce rt at vv)
Proof
  rewrite_tac[compile_ifexp_arm_def] >> IF_CASES_TAC
  >- metis_tac[first_emission_unwrap_value, cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[compile_alloc_buffer_def, cs_appends_bind, cs_appends_emit_helpers, cs_appends_return] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- metis_tac[first_emission_unwrap_value, cs_appends_def] >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- metis_tac[first_emission_store_memory, cs_appends_def] >>
  simp[cs_appends_return]
QED

Theorem expr_pair_let_extends[local]:
  (!a v b. m a = (v,b) ==> cs_extends a b) /\
  (!v b w c. k v b = (w,c) ==> cs_extends b c) ==>
  !a w c. pair$UNCURRY k (m a) = (w,c) ==> cs_extends a c
Proof
  rpt strip_tac >> Cases_on `m a` >> gvs[] >>
  metis_tac[cs_extends_trans]
QED

(* The analogous facts in bodyBoundLabels are local to that theory. *)
Theorem expr_fe_list_case_constant[local]:
  list_CASE xs p (\h t. p) = (p:bool)
Proof
  Cases_on `xs` >> simp[]
QED

Theorem expr_fe_expr_case_constant[local]:
  expr_CASE e (\a b. p) (\a b. p) (\a b d. p)
    (\a b d f. p) (\a b. p) (\a b d. p) (\a b d. p)
    (\a b d. p) (\a b d. p) (\a b d f. p) (\a b. p) (\a b d f. p) = (p:bool)
Proof
  Cases_on `e` >> simp[]
QED

Theorem expr_builtin_result_predicate[local]:
  (!rt bi es. P (g ce rt ty bi es a)) /\
  (!rt at an bt bn mt mn. P (compile_addmod_names ce rt at an bt bn mt mn a)) /\
  (!rt at an bt bn mt mn. P (compile_mulmod_names ce rt at an bt bn mt mn a)) /\
  (!rt at an bt bn. P (compile_powmod256_names ce rt at an bt bn a)) ==>
  P (compile_expr_body f g h ce ty (Builtin ann bi es) a)
Proof
  strip_tac >> Cases_on `bi` >>
  simp([compile_expr_body_def, LET_THM,
        expr_fe_list_case_constant, expr_fe_expr_case_constant] @
       map TypeBase.case_rand_of [``:'a list``, ``:expr``])
QED

Theorem expr_result_state_predicate[local]:
  (!x b. m = (x,b) ==> R b) = R (SND m)
Proof
  Cases_on `m` >> simp[]
QED

Theorem expr_builtin_state_predicate[local]:
  (!rt bi es x b. g ce rt ty bi es a = (x,b) ==> R b) /\
  (!rt at an bt bn mt mn x b.
    compile_addmod_names ce rt at an bt bn mt mn a = (x,b) ==> R b) /\
  (!rt at an bt bn mt mn x b.
    compile_mulmod_names ce rt at an bt bn mt mn a = (x,b) ==> R b) /\
  (!rt at an bt bn x b.
    compile_powmod256_names ce rt at an bt bn a = (x,b) ==> R b) ==>
  !x b. compile_expr_body f g h ce ty (Builtin ann bi es) a = (x,b) ==> R b
Proof
  pure_rewrite_tac[expr_result_state_predicate] >>
  MATCH_ACCEPT_TAC (Q.INST [`P` |-> `\r. R (SND r)`]
    expr_builtin_result_predicate |> BETA_RULE)
QED

Theorem expr_stack_state_rule[local]:
  (!a x b. m a = (x,b) ==> R a b) ==>
  !a x b. as_stack_val ty (m a) = (x,b) ==> R a b
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[as_stack_val_def] >> metis_tac[]
QED

Theorem expr_ptr_state_rule[local]:
  (!a x b. m a = (x,b) ==> R a b) ==>
  !a x b. as_ptr_val ty loc (m a) = (x,b) ==> R a b
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m a` >>
  simp[as_ptr_val_def] >> metis_tac[]
QED

Theorem expr_membership_state_rule[local]:
  (!a x b. d a = (x,b) ==> R a b) /\
  (!es a x b. l es a = (x,b) ==> R a b) ==>
  !a x b. (case e of Builtin _ (MakeArray _ _) es => l es a | _ => d a) = (x,b) ==>
    R a b
Proof
  strip_tac >> Cases_on `e` >> simp[] >>
  rename1 `builtin_CASE bi` >> Cases_on `bi` >> simp[] >> metis_tac[]
QED

Theorem first_emission_expr_compilers:
  (!ce ty e a x b. compile_expr ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce rt ty bi es a x b. compile_builtin_dispatch ce rt ty bi es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce vt ty tb rt es a x b. compile_type_builtin_dispatch ce vt ty tb rt es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac
  >- suspend "expression"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume first_emission_expr_compilers[expression]:
  rpt gen_tac >> strip_tac >> qid_spec_tac `a` >>
  mp_tac (Q.ISPECL [`expr_size e`, `compile_expr`]
    (Q.GENL [`bound`, `cfn`] first_emission_expr_child_callback)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  mp_tac (Q.ISPECL [`expr_size e`, `compile_builtin_dispatch`]
    (Q.GENL [`bound`, `dispatch`] first_emission_builtin_child_callback)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  mp_tac (Q.ISPECL [`expr_size e`, `compile_type_builtin_dispatch`]
    (Q.GENL [`bound`, `dispatch`] first_emission_type_child_callback)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  ntac 3 (pop_last_assum kall_tac) >>
  once_rewrite_tac[compile_expr_raw_def] >> Cases_on `e`
  >~ [`Literal t l`] >- (simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
      MATCH_ACCEPT_TAC first_emission_literal_vv)
  >~ [`Name t n`] >- (simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
      MATCH_ACCEPT_TAC first_emission_name_vv)
  >~ [`IfExp t c l r`] >- suspend "ifexp"
  >~ [`Builtin t bi es`] >- suspend "builtin_expr"
  >~ [`TypeBuiltin t tb rt es`] >- suspend "type_expr"
  >~ [`Subscript t l r`] >- suspend "subscript"
  >~ [`Attribute t l fld`] >- suspend "attribute"
  >~ [`StructLit t n fs`] >- suspend "struct"
  >~ [`FlagMember t n m`] >- suspend "flag"
  >~ [`TopLevelName t n`] >- suspend "topname"
  >~ [`Call t target es d`] >- suspend "call"
  >~ [`Pop t target`] >- suspend "pop"
QED

Resume first_emission_expr_compilers[flag]:
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM, cs_extends_refl]
QED

Resume first_emission_expr_compilers[type_expr]:
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM,
    Excl "type_child_callback_def", Excl "builtin_child_callback_def",
    Excl "expr_child_callback_def"] >>
  rpt gen_tac >> strip_tac >>
  gvs[Excl "type_child_callback_def", Excl "builtin_child_callback_def",
      Excl "expr_child_callback_def", SF ETA_ss] >>
  first_x_assum drule >> simp[]
QED

Resume first_emission_expr_compilers[subscript]:
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  match_mp_tac first_emission_subscript >>
  fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
     Excl "type_child_callback_def", SF ETA_ss] >> metis_tac[]
QED

Resume first_emission_expr_compilers[attribute]:
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  match_mp_tac first_emission_attribute >>
  fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
     Excl "type_child_callback_def", SF ETA_ss] >> metis_tac[]
QED

Resume first_emission_expr_compilers[ifexp]:
  ntac 2 (pop_assum kall_tac) >>
  fs[Excl "expr_child_callback_def", SF ETA_ss] >>
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM, SF ETA_ss,
    Excl "expr_child_callback_def"] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> rpt gen_tac >> MATCH_ACCEPT_TAC first_emission_fresh) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> rpt gen_tac >> MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> rpt gen_tac >> MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> rpt gen_tac >> MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >>
  gen_tac >> once_rewrite_tac[state_pair_let_bind] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> map_every qid_spec_tac [`b'`, `x'`, `st6`] >>
  rpt (ho_match_mp_tac expr_pair_let_extends >> conj_tac
    >- metis_tac[cs_appends_prims, cs_appends_emit_helpers,
                 expr_ifexp_arm_appends, cs_appends_def] >> gen_tac) >>
  rpt gen_tac >> IF_CASES_TAC >> simp[cs_extends_refl]
QED

Resume first_emission_expr_compilers[call]:
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
     Excl "type_child_callback_def", SF ETA_ss] >>
  Cases_on `target`
  >~ [`IntCall fid`] >- (match_mp_tac first_emission_intcall >> metis_tac[])
  >~ [`ExtCall static skip sig opts`] >- (PairCases_on `sig` >>
      match_mp_tac first_emission_extcall >> metis_tac[])
  >~ [`Send gas`] >- (match_mp_tac first_emission_send >> metis_tac[])
  >~ [`RawCallTarget flags`] >- (match_mp_tac first_emission_rawcall >> metis_tac[cs_appends_def])
  >~ [`RawCallCalldataTarget flags`] >- (match_mp_tac first_emission_rawcall_calldata >> metis_tac[cs_appends_def])
  >~ [`CreateTarget ck salt rof n`] >- suspend "create_wrap"
  >~ [`RawLog`] >- suspend "rawlog"
  >~ [`RawRevert`] >- suspend "rawrevert"
  >~ [`SelfDestructTarget`] >- suspend "selfdestruct"
QED

Resume first_emission_expr_compilers[topname]:
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_module_vars n`
  >- (simp_tac (srw_ss()) [] >>
      ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
      simp[cs_extends_refl]) >>
  Cases_on `x` >> simp[cs_extends_refl] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
  simp[cs_extends_refl] >> rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >>
  simp[] >> metis_tac[]
QED

Resume first_emission_expr_compilers[struct]:
  fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
     Excl "type_child_callback_def", SF ETA_ss] >>
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (simp_tac bool_ss [compile_alloc_buffer_def] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
      simp[comp_return_def, cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_struct_lit >> metis_tac[cs_appends_def]) >>
  simp[cs_extends_refl]
QED

Resume first_emission_expr_compilers[pop]:
  fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
     Excl "type_child_callback_def", SF ETA_ss] >>
  simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_get_target_ptr >> metis_tac[]) >>
  gen_tac >> PairCases_on `v` >> simp_tac (srw_ss()) [] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_dynarray_pop >>
  simp[cs_extends_refl]
QED

Resume first_emission_expr_compilers[rawlog]:
  match_mp_tac first_emission_rawlog_call >>
  fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
     Excl "type_child_callback_def", SF ETA_ss] >> metis_tac[]
QED

Resume first_emission_expr_compilers[rawrevert]:
  match_mp_tac first_emission_rawrevert_call >>
  fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
     Excl "type_child_callback_def", SF ETA_ss] >> metis_tac[]
QED

Resume first_emission_expr_compilers[selfdestruct]:
  simp_tac (srw_ss()) [compile_call_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
  simp[cs_extends_refl]
QED

Resume first_emission_expr_compilers[create_wrap]:
  simp_tac (srw_ss()) [compile_call_def] >>
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `as_stack_val rt (m a)` >>
  Cases_on `m a` >> simp[as_stack_val_def] >> strip_tac >>
  `!ce ty e. cs_appends (expr_child_callback
    (call_target_size (CreateTarget ck salt rof n) +
     (type_size t + (list_size expr_size es + (option_size expr_size d + 1))))
     compile_expr ce ty e)` by metis_tac[cs_appends_def] >>
  gvs[Abbr `m`, Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
      Excl "type_child_callback_def", SF ETA_ss] >>
  irule first_emission_create_call >> metis_tac[]
QED

Resume first_emission_expr_compilers[builtin_expr]:
  fs[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
     Excl "type_child_callback_def", SF ETA_ss] >>
  gen_tac >>
  ho_match_mp_tac expr_builtin_state_predicate >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[first_emission_addmod_names]
  >- metis_tac[first_emission_mulmod_names]
  >> metis_tac[first_emission_powmod256_names]
QED

Resume first_emission_expr_compilers[builtin]:
  rpt gen_tac >> strip_tac >> qid_spec_tac `a` >>
  mp_tac (Q.ISPECL [`list_size expr_size es`, `compile_expr`]
    (Q.GENL [`bound`, `cfn`] first_emission_expr_child_callback)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  pop_last_assum kall_tac >>
  once_rewrite_tac[compile_expr_raw_def] >>
  Cases_on `bi`
  >~ [`Len`] >- suspend "bi_len"
  >~ [`CalldataLen`] >- suspend "bi_calldatalen"
  >~ [`CalldataSlice n`] >- suspend "bi_calldataslice"
  >~ [`Not`] >- suspend "bi_not"
  >~ [`Neg`] >- suspend "bi_neg"
  >~ [`Abs`] >- suspend "bi_abs"
  >~ [`Bop op`] >- suspend "bi_bop"
  >~ [`Env item`] >- suspend "bi_env"
  >~ [`Acc item`] >- suspend "bi_acc"
  >~ [`Keccak256`] >- suspend "bi_keccak"
  >~ [`Sha256`] >- suspend "bi_sha"
  >~ [`BlockHash`] >- suspend "bi_blockhash"
  >~ [`BlobHash`] >- suspend "bi_blobhash"
  >~ [`AddMod`] >- suspend "bi_addmod"
  >~ [`MulMod`] >- suspend "bi_mulmod"
  >~ [`Ceil`] >- suspend "bi_ceil"
  >~ [`Floor`] >- suspend "bi_floor"
  >~ [`PowMod256`] >- suspend "bi_powmod"
  >~ [`ECRecover`] >- suspend "bi_ecrecover"
  >~ [`ECAdd`] >- suspend "bi_ecadd"
  >~ [`ECMul`] >- suspend "bi_ecmul"
  >~ [`Concat n`] >- suspend "bi_concat"
  >~ [`Slice n`] >- suspend "bi_slice"
  >~ [`Uint2Str n`] >- suspend "bi_uint2str"
  >~ [`AsWeiValue d`] >- suspend "bi_wei"
  >~ [`MethodId`] >- suspend "bi_methodid"
  >~ [`MakeArray et bd`] >- suspend "bi_makearray"
QED

Resume first_emission_expr_compilers[bi_len]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >>
  MATCH_ACCEPT_TAC first_emission_builtin_len
QED

Resume first_emission_expr_compilers[bi_calldatalen]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def] >>
  ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >>
  MATCH_ACCEPT_TAC first_emission_builtin_calldatasize
QED

Resume first_emission_expr_compilers[bi_calldataslice]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >>
  MATCH_ACCEPT_TAC first_emission_slice_calldata
QED

Resume first_emission_expr_compilers[bi_neg]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_neg
QED

Resume first_emission_expr_compilers[bi_abs]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_builtin_abs
QED

Resume first_emission_expr_compilers[bi_blockhash]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_blockhash
QED

Resume first_emission_expr_compilers[bi_blobhash]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_blobhash
QED

Resume first_emission_expr_compilers[bi_ceil]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_ceil
QED

Resume first_emission_expr_compilers[bi_floor]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_floor
QED

Resume first_emission_expr_compilers[bi_uint2str]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_uint2str
QED

Resume first_emission_expr_compilers[bi_env]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def] >>
  ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_env_var
QED

Resume first_emission_expr_compilers[bi_acc]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac expr_stack_state_rule >>
  match_mp_tac first_emission_acc >> metis_tac[]
QED

Resume first_emission_expr_compilers[bi_not]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> Cases_on `expr_type (HD es) = BaseT BoolT` >>
  asm_simp_tac bool_ss []
  >- (ho_match_mp_tac expr_stack_state_rule >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_invert
QED

Resume first_emission_expr_compilers[type_builtin]:
  rpt gen_tac >> simp_tac bool_ss [] >> strip_tac >> qid_spec_tac `a` >>
  mp_tac (Q.ISPECL [`list_size expr_size es`, `compile_expr`]
    (Q.GENL [`bound`, `cfn`] first_emission_expr_child_callback)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  pop_last_assum kall_tac >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp_tac (srw_ss()) [SF ETA_ss, Excl "expr_child_callback_def"] >>
  Cases_on `tb`
  >~ [`Convert`] >- (match_mp_tac first_emission_type_builtin_convert >> metis_tac[])
  >~ [`AbiDecode uw`] >- (match_mp_tac first_emission_type_abi_decode >> metis_tac[])
  >~ [`AbiEncode en mid`] >- (match_mp_tac first_emission_type_abi_encode >> metis_tac[cs_appends_def])
  >~ [`Empty`] >- suspend "tb_empty"
  >~ [`Extract32`] >- suspend "tb_extract"
  >> (Cases_on `type_bounds rt` >>
      simp[compile_type_builtin_dispatch_body_def, LET_THM, cs_extends_refl])
QED

Resume first_emission_expr_compilers[bi_addmod]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ntac 3 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >> gen_tac) >>
  ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_addmod
QED

Resume first_emission_expr_compilers[bi_mulmod]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ntac 3 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >> gen_tac) >>
  ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_mulmod
QED

Resume first_emission_expr_compilers[bi_powmod]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ntac 2 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >> gen_tac) >>
  ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_pow_mod256
QED

Resume first_emission_expr_compilers[bi_ecrecover]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ntac 4 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >> gen_tac) >>
  ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_ecrecover
QED

Resume first_emission_expr_compilers[bi_ecadd]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ntac 2 (ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- metis_tac[] >> gen_tac >>
    ho_match_mp_tac first_emission_pair_let >> conj_tac
    >- MATCH_ACCEPT_TAC first_emission_unwrap_value >> gen_tac) >>
  ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_ecadd_points
QED

Resume first_emission_expr_compilers[bi_ecmul]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_unwrap_value >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_ecmul_point
QED

Resume first_emission_expr_compilers[bi_wei]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> Cases_on `is_decimal_type (expr_type (HD es))` >>
  asm_simp_tac bool_ss []
  >- (ho_match_mp_tac expr_stack_state_rule >>
      ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_as_wei_value_decimal) >>
  ho_match_mp_tac expr_stack_state_rule >>
  MATCH_ACCEPT_TAC first_emission_as_wei_value_int
QED

Resume first_emission_expr_compilers[tb_empty]:
  simp_tac (srw_ss()) [compile_type_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `is_word_type rt` >> asm_simp_tac bool_ss []
  >- simp[cs_extends_refl] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_builtin_empty_complex >>
  simp[cs_extends_refl]
QED

Resume first_emission_expr_compilers[tb_extract]:
  simp_tac (srw_ss()) [compile_type_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_bytestring_src) >>
  gen_tac >> PairCases_on `v` >> simp_tac (srw_ss()) [] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_extract32_load) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  suspend "tb_extract_clamp"
QED

Resume first_emission_expr_compilers[bi_keccak]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  Cases_on `is_bytestring_type (expr_type (HD es))` >> asm_simp_tac bool_ss []
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
      ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_keccak256_bytes) >>
  Cases_on `expr_type (HD es)` >> simp_tac (srw_ss()) [] >>
  FIRST [
    (rename1 `BaseT bt` >> Cases_on `bt` >> simp_tac (srw_ss()) [] >>
     FIRST [(rename1 `BytesT bd` >> Cases_on `bd` >> simp_tac (srw_ss()) []), all_tac]),
    all_tac] >>
  (ho_match_mp_tac first_emission_pair_let >> conj_tac
   >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
   gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
   ho_match_mp_tac first_emission_strong >>
   FIRST [MATCH_ACCEPT_TAC first_emission_keccak256_bytesm,
          MATCH_ACCEPT_TAC first_emission_keccak256_word])
QED

Resume first_emission_expr_compilers[bi_sha]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  Cases_on `is_bytestring_type (expr_type (HD es))` >> asm_simp_tac bool_ss []
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
      gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
      ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_sha256_bytes) >>
  Cases_on `expr_type (HD es)` >> simp_tac (srw_ss()) [] >>
  FIRST [
    (rename1 `BaseT bt` >> Cases_on `bt` >> simp_tac (srw_ss()) [] >>
     FIRST [(rename1 `BytesT bd` >> Cases_on `bd` >> simp_tac (srw_ss()) []), all_tac]),
    all_tac] >>
  (ho_match_mp_tac first_emission_pair_let >> conj_tac
   >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
   gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
   ho_match_mp_tac first_emission_strong >>
   FIRST [MATCH_ACCEPT_TAC first_emission_sha256_bytesm,
          MATCH_ACCEPT_TAC first_emission_sha256_word])
QED

Resume first_emission_expr_compilers[bi_methodid]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  Cases_on `method_id_literal (HD es)` >> simp_tac (srw_ss()) []
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
      gen_tac >> Cases_on `rt = BaseT (BytesT (Fixed 4))` >> asm_simp_tac bool_ss []
      >- (ho_match_mp_tac expr_stack_state_rule >>
          ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_method_id_runtime) >>
      ho_match_mp_tac expr_ptr_state_rule >>
      ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_method_id_runtime) >>
  MATCH_ACCEPT_TAC first_emission_literal_vv
QED

Resume first_emission_expr_compilers[bi_makearray]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  Cases_on `et` >> simp_tac (srw_ss()) [] >>
  (ho_match_mp_tac first_emission_pair_let >> conj_tac
   >- (rewrite_tac[compile_alloc_buffer_def] >>
       ho_match_mp_tac first_emission_bind >> conj_tac
       >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
           drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
       gen_tac >> metis_tac[first_emission_return]) >>
   gen_tac >> ho_match_mp_tac expr_ptr_state_rule)
  >- (match_mp_tac first_emission_make_tuple >> metis_tac[cs_appends_def]) >>
  match_mp_tac first_emission_make_array >> metis_tac[cs_appends_def]
QED

Resume first_emission_expr_compilers[bi_concat]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (rewrite_tac[compile_alloc_buffer_def] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
      gen_tac >> metis_tac[first_emission_return]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (rewrite_tac[compile_alloc_buffer_def] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
      gen_tac >> metis_tac[first_emission_return]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_concat >> metis_tac[cs_appends_def]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
  simp[cs_extends_refl]
QED

Resume first_emission_expr_compilers[bi_slice]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  Cases_on `is_msg_data (HD es)` >> asm_simp_tac bool_ss []
  >- suspend "slice_calldata" >>
  Cases_on `is_self_code (HD es)` >> asm_simp_tac bool_ss []
  >- suspend "slice_code" >>
  Cases_on `is_extcode (HD es)` >> asm_simp_tac bool_ss []
  >- suspend "slice_extcode" >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> Cases_on `is_bytestring_type (expr_type (HD es))` >> asm_simp_tac bool_ss []
  >- suspend "slice_bytes" >> suspend "slice_fixed"
QED

Resume first_emission_expr_compilers[slice_calldata]:
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_slice_calldata
QED

Resume first_emission_expr_compilers[slice_code]:
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_slice_code
QED

Resume first_emission_expr_compilers[slice_extcode]:
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_slice_out_buf) >>
  PairCases >> simp_tac (srw_ss()) [] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_slice_extcode
QED

Resume first_emission_expr_compilers[slice_bytes]:
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_bytestring_src) >>
  PairCases >> simp_tac (srw_ss()) [] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_slice_data
QED

Resume first_emission_expr_compilers[slice_fixed]:
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (rewrite_tac[compile_alloc_buffer_def] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
      gen_tac >> metis_tac[first_emission_return]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_ptr_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_slice_data
QED

Resume first_emission_expr_compilers[bi_bop]:
  simp_tac (srw_ss()) [compile_builtin_dispatch_body_def, LET_THM,
    Excl "expr_child_callback_def", SF ETA_ss] >>
  Cases_on `(op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL es)))` >>
  asm_simp_tac bool_ss []
  >- suspend "bop_membership" >>
  Cases_on `is_bytestring_type (expr_type (HD es)) /\ (op = Eq \/ op = NotEq)` >>
  asm_simp_tac bool_ss []
  >- suspend "bop_bytes" >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_binop
QED

Resume first_emission_expr_compilers[bop_bytes]:
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_bytestring_hash) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_bytestring_hash) >>
  gen_tac >> Cases_on `op = Eq` >> asm_simp_tac bool_ss []
  >- (ho_match_mp_tac expr_stack_state_rule >>
      ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]
QED

Resume first_emission_expr_compilers[bop_membership]:
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> metis_tac[]) >>
  gen_tac >> ho_match_mp_tac expr_membership_state_rule >> conj_tac
  >- (ho_match_mp_tac first_emission_pair_let >> conj_tac
      >- metis_tac[] >>
      gen_tac >> ho_match_mp_tac expr_stack_state_rule >>
      ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_var_array_membership) >>
  gen_tac >> ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_multi_exprs >> metis_tac[]) >>
  gen_tac >> Cases_on `op = In` >> asm_simp_tac bool_ss [] >>
  (ho_match_mp_tac expr_stack_state_rule >>
   FIRST [MATCH_ACCEPT_TAC first_emission_list_membership_in,
          MATCH_ACCEPT_TAC first_emission_list_membership_notin])
QED

Resume first_emission_expr_compilers[tb_extract_clamp]:
  map_every qid_spec_tac [`rt`, `raw`] >>
  recInduct compile_clamp_basetype_ind >>
  simp_tac bool_ss [compile_clamp_basetype_def] >> rpt conj_tac >> rpt gen_tac
  >- suspend "clamp_fixed"
  >- suspend "clamp_addr"
  >- suspend "clamp_uint"
  >- suspend "clamp_int"
  >> metis_tac[first_emission_return]
QED

Resume first_emission_expr_compilers[clamp_fixed]:
  map_every qid_spec_tac [`b'`, `x`, `st4`] >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- (rpt (ho_match_mp_tac first_emission_bind >> conj_tac
        >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
            drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >> gen_tac) >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
          drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
      metis_tac[first_emission_return]) >>
  metis_tac[first_emission_return]
QED

Resume first_emission_expr_compilers[clamp_addr]:
  map_every qid_spec_tac [`b'`, `x`, `st4`] >>
  rpt (ho_match_mp_tac first_emission_bind >> conj_tac
    >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
        drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >> gen_tac) >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
  metis_tac[first_emission_return]
QED

Resume first_emission_expr_compilers[clamp_uint]:
  map_every qid_spec_tac [`b'`, `x`, `st4`] >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- (simp_tac bool_ss [clamp_and_return_def, compile_clamp_def, LET_THM] >>
      pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_cond >> conj_tac >>
          (rpt (ho_match_mp_tac first_emission_bind >> conj_tac
            >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
                drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >> gen_tac) >>
           ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
           drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[])) >>
      metis_tac[first_emission_return]) >>
  metis_tac[first_emission_return]
QED

Resume first_emission_expr_compilers[clamp_int]:
  map_every qid_spec_tac [`b'`, `x`, `st4`] >>
  ho_match_mp_tac first_emission_cond >> conj_tac
  >- (simp_tac bool_ss [clamp_and_return_def, compile_clamp_def, LET_THM] >>
      pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_cond >> conj_tac >>
          (rpt (ho_match_mp_tac first_emission_bind >> conj_tac
            >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
                drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >> gen_tac) >>
           ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
           drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[])) >>
      metis_tac[first_emission_return]) >>
  metis_tac[first_emission_return]
QED

Finalise first_emission_expr_compilers
