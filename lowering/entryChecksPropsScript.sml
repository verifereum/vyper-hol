(*
 * Entry checks against the source (#639)
 *
 * compile_entry_checks emits, at an external function's entry, a payable
 * check (CALLVALUE is zero unless the function is payable) and a minimum
 * calldata size check (CALLDATASIZE is at least min_calldata_size).  Here
 * the two checks meet the source: calldata that encodes the call is long
 * enough, so the size check falls through, and a call sending value to a
 * nonpayable function reverts on both sides, as send_call_value's
 * check (mut = Payable) fails in the source.
 *
 * min_calldata_size is 4 plus the ABI head sizes of the required
 * arguments, as Python's _emit_entry_checks takes it
 * (SELECTOR_BYTES + calldata_args_t.abi_type.static_size()).
 *
 * TOP-LEVEL:
 *   compile_entry_checks_frag — the two checks as a fragment: they fall
 *     through, changing only fresh variables, when the value check and the
 *     size check pass, and revert otherwise
 *   compile_entry_checks_pass — with value allowed and the calldata long
 *     enough, the checks fall through
 *   compile_entry_checks_value_revert — a nonpayable function's checks
 *     revert when value is sent
 *   calldata_encodes_min_calldata_size — calldata that encodes a call with
 *     typed arguments is at least min_calldata_size bytes long
 *   valid_vyper_call_min_calldata_size — the same for the function
 *     valid_vyper_call selects, at the env package_external_fn builds
 *   call_external_nonpayable_value — the source fails with a RuntimeError,
 *     machine unchanged and no requests, when value is sent to a nonpayable
 *     function
 *   entry_checks_pass — from the S1 premises, a call that sends no value to
 *     a nonpayable function, or any value to a payable one, falls through
 *     the selected function's entry checks
 *   entry_checks_nonpayable_value — from the S1 premises, a call that sends
 *     value to a nonpayable function reverts at its entry checks, and
 *     external_call_result_rel relates that to the source's failure
 *   fallback_checks_nonpayable_value — the same for a nonpayable,
 *     non-nonreentrant fallback and its own CALLVALUE check
 *
 * Helpers: cds_check_prefix_structure, step_cds_check_ops, cds_check_run,
 *   cds_check_frag, payable_cds_frag, enc_tuple_heads_length,
 *   map_uncurry_snd, source_typing_ok_type_keys_distinct,
 *   call_external_function_nonpayable_value.
 *)
Theory entryChecksProps
Ancestors
  arithmetic list rich_list words finite_map
  entryDispatchProps entryDecodePlanProps entryDecodeProps
  moduleLoweringProps exprLoweringProps emitHelperProps fragExec
  compileVyper moduleLowering compileEnv selectorDispatch contractABI
  venomState venomInst venomExecSemantics
  valueEncodingProofs vyperABIRoundtrip
  e2eDefs vyperLoweringCorrect vyperTypeContractSoundness
  vyperInterpreter vyperContext vyperState vyperTypeContract
Libs
  wordsLib

(* ===== The size check ===== *)

Theorem cds_check_prefix_structure[local]:
  emit_op CALLDATASIZE [] st0 = (cd, st1) /\
  emit_op LT [cd; Lit (n2w m)] st1 = (lt, st2) /\
  emit_op ISZERO [lt] st2 = (ok, st3) /\
  emit_void ASSERT [ok] st3 = ((), st4) ==>
  st4.cs_blocks = st0.cs_blocks /\
  st4.cs_current_bb = st0.cs_current_bb /\
  isPREFIX st0.cs_current_insts st4.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st0 st4)
Proof
  strip_tac >>
  imp_res_tac emit_op_extends >>
  drule emit_void_extends >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC, mk_inst_def,
       is_terminator_def]
QED

(* The four opcodes' steps, apart from step_inst_base's case split. *)
Theorem step_cds_check_ops[local]:
  step_inst_base (mk_inst id CALLDATASIZE ops outs) s =
    exec_read0 (\s. n2w (LENGTH s.vs_call_ctx.cc_calldata))
      (mk_inst id CALLDATASIZE ops outs) s /\
  step_inst_base (mk_inst id LT ops outs) s =
    exec_pure2 (\x y. bool_to_word (w2n x < w2n y))
      (mk_inst id LT ops outs) s /\
  step_inst_base (mk_inst id ISZERO ops outs) s =
    exec_pure1 (\x. bool_to_word (x = 0w)) (mk_inst id ISZERO ops outs) s /\
  step_inst_base (mk_inst id ASSERT [a] []) s =
    case eval_operand a s of
      SOME c => if c = 0w then
                  Abort Revert_abort (revert_state (set_returndata [] s))
                else OK s
    | NONE => Error "undefined operand"
Proof
  rpt conj_tac >> simp[step_inst_base_def, mk_inst_def]
QED

(* The four instructions run to the end when the calldata is not shorter
   than m (as LT compares words), and revert otherwise. *)
Theorem cds_check_run[local]:
  emit_op CALLDATASIZE [] st0 = (cd, st1) /\
  emit_op LT [cd; Lit (n2w m)] st1 = (lt, st2) /\
  emit_op ISZERO [lt] st2 = (ok, st3) /\
  emit_void ASSERT [ok] st3 = ((), st4) /\
  fresh_vars_wrt st0 s0 ==>
  (?t. run_inst_seq (emitted_insts st0 st4) s0 = OK t /\
       vars_pc_only s0 t /\ fresh_vars_wrt st4 t /\
       (!x. not_fresh_at st0 x ==> lookup_var x t = lookup_var x s0) /\
       ~(w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
         w2n (n2w m : bytes32))) \/
  (?t. run_inst_seq (emitted_insts st0 st4) s0 = Abort Revert_abort t /\
       w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
       w2n (n2w m : bytes32))
Proof
  strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts st0 st4 =
    emitted_insts st0 st1 ++ emitted_insts st1 st2 ++
    emitted_insts st2 st3 ++ emitted_insts st3 st4` by
    simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  gvs[] >>
  simp[run_inst_seq_def, step_cds_check_ops] >>
  simp[exec_read0_def, exec_pure1_def, exec_pure2_def, mk_inst_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> simp[vars_pc_only_def] >>
  conj_tac
  >- (fs[fresh_vars_wrt_def] >> rpt strip_tac >> fs[]) >>
  rw[FLOOKUP_UPDATE] >> gvs[not_fresh_at_def]
QED

Theorem cds_check_frag[local]:
  emit_op CALLDATASIZE [] st0 = (cd, st1) /\
  emit_op LT [cd; Lit (n2w m)] st1 = (lt, st2) /\
  emit_op ISZERO [lt] st2 = (ok, st3) /\
  emit_void ASSERT [ok] st3 = ((), st4) /\
  fresh_vars_wrt st0 s0 ==>
  frag_exec ctx st0 st4 (\s. s = s0)
    (\t. vars_pc_only s0 t /\ fresh_vars_wrt st4 t /\
         (!x. not_fresh_at st0 x ==> lookup_var x t = lookup_var x s0) /\
         ~(w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
           w2n (n2w m : bytes32)))
    (\r. ?t. r = Abort Revert_abort t /\
             w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
             w2n (n2w m : bytes32))
Proof
  strip_tac >>
  drule_all cds_check_prefix_structure >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all cds_check_run >> strip_tac
  >- (disj1_tac >> goal_assum $ drule_at Any >>
      simp[vars_pc_only_inst_idx, control_moves_keep_vars] >>
      gvs[fresh_vars_wrt_def]) >>
  disj2_tac >> goal_assum $ drule_at Any >> fs[]
QED

(* The payable check followed by the size check. *)
Theorem payable_cds_frag[local]:
  emit_op CALLVALUE [] st = (cv, st1) /\ emit_op ISZERO [cv] st1 = (nv, st2) /\
  emit_void ASSERT [nv] st2 = ((), st3) /\
  emit_op CALLDATASIZE [] st3 = (cd, st4) /\
  emit_op LT [cd; Lit (n2w m)] st4 = (lt, st5) /\
  emit_op ISZERO [lt] st5 = (ok, st6) /\ emit_void ASSERT [ok] st6 = ((), st7) /\
  fresh_vars_wrt st s0 ==>
  frag_exec ctx st st7 (\s. s = s0)
    (\t. vars_pc_only s0 t /\ fresh_vars_wrt st7 t /\
         (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
         s0.vs_call_ctx.cc_callvalue = 0w /\
         ~(w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
           w2n (n2w m : bytes32)))
    (\r. ?t. r = Abort Revert_abort t /\
         (s0.vs_call_ctx.cc_callvalue <> 0w \/
          w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
          w2n (n2w m : bytes32)))
Proof
  strip_tac >>
  `cs_extends st st1 /\ cs_extends st1 st2 /\ cs_extends st2 st3 /\
   cs_extends st3 st4 /\ cs_extends st4 st5 /\ cs_extends st5 st6 /\
   cs_extends st6 st7` by
    (rpt conj_tac >> metis_tac[cs_appends_def, cs_appends_emit_helpers]) >>
  `cs_extends st st3 /\ cs_extends st3 st7` by metis_tac[cs_extends_trans] >>
  `st.cs_next_var <= st3.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >> gvs[]) >>
  drule_all payable_check_frag >> disch_then (assume_tac o SPEC_ALL) >>
  first_x_assum (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = s0`,
    `\r. ?t. r = Abort Revert_abort t /\
         (s0.vs_call_ctx.cc_callvalue <> 0w \/
          w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
          w2n (n2w m : bytes32))`] mp_tac) >>
  impl_tac >- rw[] >> strip_tac >>
  first_x_assum (irule o MATCH_MP frag_exec_then) >> simp[] >>
  rpt strip_tac >>
  `t.vs_call_ctx = s0.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
  drule_all cds_check_frag >> disch_then (assume_tac o SPEC_ALL) >>
  first_x_assum (mp_tac o MATCH_MP frag_exec_weaken) >>
  disch_then irule >> rw[] >> gvs[]
  >- metis_tac[vars_pc_only_trans] >>
  `not_fresh_at st3 x` by fs[not_fresh_at_def] >>
  metis_tac[]
QED

(* ===== The two checks ===== *)

(* compile_entry_checks: the payable check unless the function is payable,
   then the size check when min_cds is past the selector.  They fall
   through, changing only fresh variables, when both pass, and revert when
   one fails.  LT compares words, so the size check is stated on them. *)
Theorem compile_entry_checks_frag:
  !min_cds is_payable st st' ctx s0.
    compile_entry_checks min_cds is_payable st = ((), st') /\
    fresh_vars_wrt st s0 ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only s0 t /\ fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
           (is_payable \/ s0.vs_call_ctx.cc_callvalue = 0w) /\
           (4 < min_cds ==>
            ~(w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
              w2n (n2w min_cds : bytes32))))
      (\r. ?t. r = Abort Revert_abort t /\
           ((~is_payable /\ s0.vs_call_ctx.cc_callvalue <> 0w) \/
            (4 < min_cds /\
             w2n (n2w (LENGTH s0.vs_call_ctx.cc_calldata) : bytes32) <
             w2n (n2w min_cds : bytes32))))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_payable` >> Cases_on `4 < min_cds` >>
  gvs[comp_return_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
  >~ [`emit_op CALLVALUE _ _ = _`, `emit_op CALLDATASIZE _ _ = _`]
  >- (drule_all payable_cds_frag >> disch_then (assume_tac o SPEC_ALL) >>
      first_x_assum (mp_tac o MATCH_MP frag_exec_weaken) >>
      disch_then irule >> rw[] >> gvs[])
  >~ [`emit_op CALLVALUE _ _ = _`]
  >- (drule_all payable_check_frag >> disch_then (ACCEPT_TAC o SPEC_ALL))
  >~ [`emit_op CALLDATASIZE _ _ = _`]
  >- (drule_all cds_check_frag >> disch_then (assume_tac o SPEC_ALL) >>
      first_x_assum (mp_tac o MATCH_MP frag_exec_weaken) >>
      disch_then irule >> rw[] >> gvs[]) >>
  irule frag_exec_refl >> simp[vars_pc_only_refl]
QED

Theorem compile_entry_checks_pass:
  !min_cds is_payable st st' ctx s0.
    compile_entry_checks min_cds is_payable st = ((), st') /\
    fresh_vars_wrt st s0 /\
    (is_payable \/ s0.vs_call_ctx.cc_callvalue = 0w) /\
    min_cds <= LENGTH s0.vs_call_ctx.cc_calldata /\
    LENGTH s0.vs_call_ctx.cc_calldata < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only s0 t /\ fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0))
      (\r. F)
Proof
  rpt strip_tac >>
  `min_cds < dimword (:256)` by decide_tac >>
  drule_all compile_entry_checks_frag >>
  disch_then (qspec_then `ctx` assume_tac) >>
  first_x_assum (mp_tac o MATCH_MP frag_exec_weaken) >>
  disch_then irule >> rw[] >> gvs[]
QED

Theorem compile_entry_checks_value_revert:
  !min_cds st st' ctx s0.
    compile_entry_checks min_cds F st = ((), st') /\
    fresh_vars_wrt st s0 /\ s0.vs_call_ctx.cc_callvalue <> 0w ==>
    frag_exec ctx st st' (\s. s = s0) (\t. F)
      (\r. ?t. r = Abort Revert_abort t)
Proof
  rpt strip_tac >>
  drule_all compile_entry_checks_frag >>
  disch_then (qspec_then `ctx` assume_tac) >>
  first_x_assum (mp_tac o MATCH_MP frag_exec_weaken) >>
  disch_then irule >> rw[] >> gvs[]
QED

(* ===== The calldata is long enough ===== *)

(* A tuple encoding is at least as long as its heads. *)
Theorem enc_tuple_heads_length[local]:
  !ts vs. LENGTH ts = LENGTH vs ==>
    SUM (MAP2 abi_head_size ts vs) <= LENGTH (enc (Tuple ts) (ListV vs))
Proof
  rpt strip_tac >>
  qspecl_then [`ts`, `vs`, `head_lengths ts 0`, `0`, `[]`, `[]`] mp_tac
    enc_tuple_heads >>
  simp[] >> strip_tac >>
  `SUM (MAP2 abi_head_size ts vs) = LENGTH (FLAT hs)` by
    (simp[LENGTH_FLAT] >> AP_TERM_TAC >> irule LIST_EQ >>
     simp[EL_MAP, EL_MAP2]) >>
  simp[enc_def] >>
  qpat_x_assum `enc_tuple _ _ _ _ _ _ = _` (fn th => REWRITE_TAC [th]) >>
  simp[]
QED

Theorem map_uncurry_snd[local]:
  !f l. MAP (\(x:'a, y:'b). f y) l = MAP f (MAP SND l)
Proof
  gen_tac >> Induct >> simp[pairTheory.FORALL_PROD]
QED

(* Calldata that encodes a call with typed arguments holds the selector
   and the head of every argument, so it is at least min_calldata_size
   long when no argument is left to a default. *)
Theorem calldata_encodes_min_calldata_size:
  !cenv tenv fname args vals cd.
    dec_cenv_agrees cenv tenv /\
    calldata_encodes tenv fname (MAP SND args) vals cd /\
    LENGTH vals = LENGTH args /\
    (!j. j < LENGTH args ==>
         ?tv. evaluate_type tenv (SND (EL j args)) = SOME tv /\
              value_has_type tv (EL j vals)) ==>
    min_calldata_size cenv args 0 <= LENGTH cd
Proof
  rpt strip_tac >>
  `TAKE (LENGTH vals) (MAP SND args) = MAP SND args` by
    simp[TAKE_LENGTH_ID_rwt] >>
  gvs[calldata_encodes_def, min_calldata_size_def, map_uncurry_snd,
      function_selector_length] >>
  rename1 `vyper_to_abi_list _ _ _ = SOME avs` >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  qspecl_then [`cenv`, `tenv`, `MAP SND args`, `vals`, `avs`, `LENGTH args`]
    mp_tac decode_head_offset >>
  impl_tac >- simp[EL_MAP] >>
  simp[vyper_to_abi_types_length, TAKE_LENGTH_ID_rwt] >> strip_tac >>
  qspecl_then [`vyper_to_abi_types tenv (MAP SND args)`, `avs`] mp_tac
    enc_tuple_heads_length >>
  simp[vyper_to_abi_types_length] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `SUM (MAP g _) <= _` >>
  `g = abi_embedded_static_size cenv.ce_struct_fields` by
    simp[Abbr `g`, FUN_EQ_THM] >>
  gvs[]
QED

(* The checker keeps type names distinct. *)
Theorem source_typing_ok_type_keys_distinct[local]:
  source_typing_ok tops am tx ==>
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))
Proof
  rw[source_typing_ok_def, check_contract_def, AllCaseEqs()] >>
  fs[contract_namespaces_ok_def, contract_keys_def]
QED

(* The function valid_vyper_call selects takes all its arguments from the
   calldata, so the calldata is at least the min_calldata_size its
   package checks for. *)
Theorem valid_vyper_call_min_calldata_size:
  !tops am tx cd ret mut args stmts ut nkm rr lbl cenv pos_args min_cds rest.
    source_typing_ok tops am tx /\
    valid_vyper_call tops tx cd ret /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, stmts) /\
    package_external_fn tops ut nkm
      (mut, F, rr, tx.function_name, args, [], ret, stmts) =
      (lbl, cenv, pos_args, min_cds, rest) ==>
    min_cds <= LENGTH cd
Proof
  rpt strip_tac >>
  drule source_typing_ok_type_keys_distinct >> strip_tac >>
  drule_all package_external_fn_dec_cenv_agrees >> strip_tac >>
  `min_cds = min_calldata_size cenv args 0` by
    (qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp[package_external_fn_def] >> rw[] >> simp[]) >>
  gvs[valid_vyper_call_def, optionTheory.IS_SOME_EXISTS] >>
  irule calldata_encodes_min_calldata_size >>
  qexistsl_tac [`tx.function_name`, `type_env tops`, `tx.args`] >> simp[] >>
  rpt strip_tac >>
  drule_all bind_arguments_word_arg >> simp[]
QED

(* ===== The source side of a call that sends value ===== *)

Theorem call_external_function_nonpayable_value[local]:
  mut <> Payable /\ cx.txn.value <> 0 /\ ~cx.in_deploy ==>
  ?msg. call_external_function orc am cx F mut ts all_mods args dflts vals
          stmts ret = (INR (Error (RuntimeError msg)), am, [])
Proof
  strip_tac >>
  gvs[call_external_function_def, bind_def, ignore_bind_def, return_def,
      send_call_value_def, check_def, assert_def, LET_THM] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

(* Value sent to a nonpayable function: the source fails with a
   RuntimeError (send_call_value's check, or an earlier setup failure),
   leaving the machine as it was and making no requests. *)
Theorem call_external_nonpayable_value:
  !orc am tx tops mut args dflts ret stmts.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, dflts, ret, stmts) /\
    mut <> Payable /\ tx.value <> 0 ==>
    ?msg. call_external orc am tx = (INR (Error (RuntimeError msg)), am, [])
Proof
  rw[source_deployment_rel_def] >>
  simp[call_external_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def] >>
  qmatch_goalsub_abbrev_tac `call_external_function orc am cx` >>
  `?msg. call_external_function orc am cx F mut tops [(NONE, tops)] args
          dflts tx.args stmts ret = (INR (Error (RuntimeError msg)), am, [])` by
    (irule call_external_function_nonpayable_value >> simp[Abbr `cx`]) >>
  simp[]
QED

(* ===== From the S1 premises ===== *)

(* A call that sends no value to a nonpayable function, or any value to a
   payable one, falls through the entry checks of the function the source
   selects: the calldata encodes the call, so it is long enough. *)
Theorem entry_checks_pass:
  !tops am tx ret ut nkm mut rr args stmts lbl cenv pos_args min_cds
   is_payable rest st st' ctx s0 tc bc.
    source_typing_ok tops am tx /\
    valid_vyper_call tops tx s0.vs_call_ctx.cc_calldata ret /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, stmts) /\
    package_external_fn tops ut nkm
      (mut, F, rr, tx.function_name, args, [], ret, stmts) =
      (lbl, cenv, pos_args, min_cds, is_payable, rest) /\
    compile_entry_checks min_cds is_payable st = ((), st') /\
    fresh_vars_wrt st s0 /\ call_ctx_rel tx s0.vs_call_ctx tc bc /\
    (mut = Payable \/ tx.value = 0) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only s0 t /\ fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0))
      (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all valid_vyper_call_min_calldata_size >> strip_tac >>
  `call_tx_well_typed tx` by fs[source_typing_ok_def] >>
  drule_all call_ctx_rel_calldata_length >> strip_tac >>
  `is_payable = (mut = Payable)` by
    (qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp[package_external_fn_def] >> rw[] >> simp[]) >>
  drule compile_entry_checks_pass >> disch_then irule >>
  gvs[call_ctx_rel_def]
QED

(* A call that sends value to a nonpayable function reverts at the entry
   checks of the function the source selects, and the source fails with a
   RuntimeError: external_call_result_rel's runtime-failure case. *)
Theorem entry_checks_nonpayable_value:
  !tops am tx orc ret ut nkm mut rr args dflts stmts lbl cenv pos_args
   min_cds is_payable rest st st' ctx s0 tc bc.
    call_tx_well_typed tx /\ source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, dflts, ret, stmts) /\
    package_external_fn tops ut nkm
      (mut, F, rr, tx.function_name, args, dflts, ret, stmts) =
      (lbl, cenv, pos_args, min_cds, is_payable, rest) /\
    compile_entry_checks min_cds is_payable st = ((), st') /\
    fresh_vars_wrt st s0 /\ call_ctx_rel tx s0.vs_call_ctx tc bc /\
    mut <> Payable /\ tx.value <> 0 ==>
    frag_exec ctx st st' (\s. s = s0) (\t. F)
      (\r. ?t. r = Abort Revert_abort t /\
               external_call_result_rel tops ret tx
                 (call_external orc am tx) r)
Proof
  rpt gen_tac >> strip_tac >>
  `~is_payable` by
    (qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp[package_external_fn_def] >> rw[] >> simp[]) >>
  `s0.vs_call_ctx.cc_callvalue <> 0w` by
    gvs[call_ctx_rel_def, call_tx_well_typed_def, dimword_def] >>
  gvs[] >>
  drule_all compile_entry_checks_value_revert >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all call_external_nonpayable_value >>
  disch_then (qspec_then `orc` strip_assume_tac) >>
  first_x_assum (mp_tac o MATCH_MP frag_exec_weaken) >>
  disch_then irule >> rw[] >>
  simp[external_call_result_rel_def]
QED

(* The same for the fallback, whose CALLVALUE check comes before its
   guarded body (compile_fallback_body), for a fallback that is not
   nonreentrant. *)
Theorem fallback_checks_nonpayable_value:
  !tops am tx orc target ut nkm exts ints fb ctor cenv is_payable nkey ut'
   iv fbody rt st st' ctx s0 tc bc.
    call_tx_well_typed tx /\ source_deployment_rel tops am tx /\
    tx.function_name = "__default__" /\
    classify_functions tops = (exts, ints, fb, ctor) /\
    (!mut typ x. ~MEM (VariableDecl Public mut "__default__" typ x) tops) /\
    (!b kt vt x. ~MEM (HashMapDecl Public b "__default__" kt vt x) tops) /\
    set_fallback_package_target target (package_fallback_fn tops ut nkm fb) =
      SOME (cenv, is_payable, F, nkey, ut', iv, fbody, rt) /\
    compile_fallback_body cenv is_payable F nkey ut' iv fbody rt st =
      ((), st') /\
    fresh_vars_wrt st s0 /\ call_ctx_rel tx s0.vs_call_ctx tc bc /\
    ~is_payable /\ tx.value <> 0 ==>
    ?sm. compile_guarded_body cenv F nkey ut' iv fbody rt sm = ((), st') /\
         frag_exec ctx st sm (\s. s = s0) (\t. F)
           (\r. ?t. r = Abort Revert_abort t /\
                    !ret. external_call_result_rel tops ret tx
                            (call_external orc am tx) r)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tops`, `NONE`, `target`, `ut`, `nkm`, `exts`, `ints`, `fb`,
               `ctor`] mp_tac fallback_package_lookup >>
  simp[] >> strip_tac >>
  `s0.vs_call_ctx.cc_callvalue <> 0w` by
    gvs[call_ctx_rel_def, call_tx_well_typed_def, dimword_def] >>
  `?msg. call_external orc am tx = (INR (Error (RuntimeError msg)), am, [])`
    by (irule call_external_nonpayable_value >> gvs[] >> metis_tac[]) >>
  drule compile_fallback_body_entry >> strip_tac >>
  qexists_tac `sm` >> simp[] >>
  first_x_assum (qspecl_then [`ctx`, `s0`] mp_tac) >> simp[] >>
  strip_tac >> first_x_assum (mp_tac o MATCH_MP frag_exec_weaken) >>
  disch_then irule >> rw[] >>
  gvs[external_call_result_rel_def]
QED
