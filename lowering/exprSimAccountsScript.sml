(*
 * Expression simulation: the account reads (#636, Builtins row 6)
 *
 * x.balance, x.codesize, x.codehash, x.is_contract and x.address of an
 * address x.  The lowering (compile_acc) lowers x as an address, then reads
 * the account with BALANCE, EXTCODESIZE, EXTCODEHASH, or EXTCODESIZE and
 * GT 0, or hands out x itself for .address.  The source reads the account
 * at the same address from its accounts, which state_rel's accounts_rel
 * makes Venom's: exprSimUnop's compile_unop_sim with the address operand.
 * The account opcodes are no fresh_write_op, so their code is no
 * straight_fresh action: unop_frag_read_then runs the read by
 * emit_op_frag, then straight-line code on its result.
 *
 * TOP-LEVEL:
 *   compile_acc_read_case  — expr_vv_case of an account read other than
 *                            .code
 *   lower_value_acc        — how an account read lowers
 *   compile_acc_frag       — unop_frag of each read's code
 *   compile_acc_stack      — an account read compiles to a StackValue
 *
 * Helpers: unop_frag_read_then (unop_frag of one account read, then
 *   straight-line code), unop_frag_read (the read alone),
 *   comp_bind_comp_return, address_word_w2w (the account address Venom
 *   reads from the address's word), account_item_type_word.
 *
 * .code is not here: the lowering emits INVALID for it (compile_acc), so
 * the read's simulation does not hold; exprSimBuiltins leaves it cheated.
 * A .code operand is only meant for slice, whose lowering copies the code
 * itself.
 *)

Theory exprSimAccounts
Ancestors
  exprUnopSimDefs exprUnopStraight exprSimUnopCompose
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  loweringPosts
  list rich_list words integer_word byte
  fragExec freshWrites varsExt loweringSlice  exprSimHyps exprSimUnop
  exprSimOperators exprSimWordBuiltins exprBopLowering exprLowering
  emitHelper emitHelperProps compileEnv exprLoweringProps accountsRelProps
  valueEncoding
  valueEncodingProofs venomExecSemantics venomInst venomState venomMemProps
  vyperAST vyperInterpreter vyperContext vyperValue vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeBytesCrypto vfmState
Libs
  pairLib wordsLib

(* ===== The fragment ===== *)

(* The account address Venom reads (w2w of the operand) is the source's
   (word_of_bytes_be of the address's bytes). *)
Theorem address_word_w2w:
  !bs. LENGTH bs = 20 ==>
       (w2w (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) : address) =
       word_of_bytes_be bs
Proof
  rpt strip_tac >> simp[typed_val_to_w256_def] >>
  `(word_of_bytes_be (PAD_LEFT 0w 32 bs) : bytes32) =
     w2w (word_of_bytes_be bs : 160 word)` by
    (qspec_then `bs` mp_tac
       (w2w_word_of_bytes_be_pad_left
          |> INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]) >>
     simp[dividesTheory.compute_divides]) >>
  pop_assum SUBST1_TAC >> simp[w2w_w2w, WORD_ALL_BITS]
QED

Theorem emit_op_extends_next_var:
  !opc ops sa v sb.
    emit_op opc ops sa = (v, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> drule emit_op_extends >> rpt strip_tac
  >- (irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND3]) >>
  gvs[]
QED


(* The account reads are no fresh_write_op (they read the accounts), so
   their code is no straight_fresh action: one read by emit_op_frag, then
   straight-line code g on its result. *)
Theorem unop_frag_read_then:
  !ctx func cenv cx opc g w1 r t v w es0.
    opc <> INVOKE /\ ~is_terminator opc /\ is_word_type t /\
    (!c. straight_fresh (g c)) /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          w = typed_val_to_w256 tv v) /\
    (!x ss n out.
       eval_operand x ss = SOME w1 /\ stmt_state_rel ctx func cenv cx es0 ss ==>
       step_inst_base (mk_inst n opc [x] [out]) ss =
         OK (update_var out r ss)) /\
    (!c sa sb op ss.
       g c sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       eval_operand c ss = SOME r ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
             eval_operand op ss' = SOME w) ==>
    unop_frag ctx func cenv cx (\x. comp_bind (emit_op opc [x]) g) w1 t
      (INL v) es0
Proof
  rpt gen_tac >> strip_tac >> simp[unop_frag_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >> simp[comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op opc [x] sa = (c, s1)` >>
  `opc <> GAS` by
    (strip_tac >> gvs[] >>
     `stmt_state_rel ctx func cenv cx es0
        (s0 with <|vs_gas_readings := [1w]; vs_inst_idx := s0.vs_inst_idx|>)` by
       (first_assum (mp_then Any
          (qspecl_then [`[1w]`, `s0.vs_inst_idx`, `es0.gas_obs`] mp_tac)
          msg_gas_state_frame) >>
        simp[]) >>
     first_x_assum (qspecl_then [`x`,
        `s0 with <|vs_gas_readings := [1w]; vs_inst_idx := s0.vs_inst_idx|>`,
        `0`, `"o"`] mp_tac) >>
     `!ss. step_inst_base (mk_inst 0 GAS [x] ["o"]) ss =
           exec_gas (mk_inst 0 GAS [x] ["o"]) ss` by
       (gen_tac >> simp[Once venomExecSemanticsTheory.step_inst_base_def, mk_inst_def]) >>
     pop_assum (fn th => REWRITE_TAC [th]) >>
     `eval_operand x
        (s0 with <|vs_gas_readings := [1w]; vs_inst_idx := s0.vs_inst_idx|>) = SOME w1` by
       (Cases_on `x` >> gvs[eval_operand_def, lookup_var_def]) >>
     strip_tac >> first_x_assum (drule_then mp_tac) >> simp[] >>
     simp[venomExecSemanticsTheory.exec_gas_def, mk_inst_def,
          venomStateTheory.update_var_def,
          venomStateTheory.venom_state_component_equality]) >>
  `sa.cs_next_var <= s1.cs_next_var /\ cs_extends sa s1 /\
   (!z. c = Var z ==> not_fresh_at s1 z)` by
    (drule emit_op_extends_next_var >> drule emitted_insts_emit_op >>
     rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
    metis_tac[straight_fresh_cs_extends] >>
  `fn_has_code s1 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `!z. not_fresh_at sa z ==> z <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es0.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `c = Var out /\ s1.cs_current_bb = sa.cs_current_bb /\
   LENGTH s1.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[Abbr `out`, emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `gas_path ctx func s0 0
     (OK ((update_var out r s0) with vs_inst_idx := SUC s0.vs_inst_idx))` by
    (qunabbrev_tac `out` >> irule emitHelperPropsTheory.emit_op_zero_path >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`[x]`, `c`, `opc`, `s1`] >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qabbrev_tac `u = (update_var out r s0) with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `stmt_state_rel ctx func cenv cx es0 u` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `eval_operand c u = SOME r` by
    simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `~u.vs_halted /\ u.vs_current_bb = s1.cs_current_bb /\
   u.vs_inst_idx = LENGTH s1.cs_current_insts` by
    simp[Abbr `u`, update_var_def] >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  `eval_operand c (drop_fresh s1 u) = SOME r` by
    (qspecl_then [`c`, `s1`, `u`] mp_tac eval_operand_drop_fresh >>
     asm_simp_tac bool_ss []) >>
  qpat_x_assum `!c sa sb op ss. _`
    (qspecl_then [`c`, `s1`, `sb`, `op`, `drop_fresh s1 u`] mp_tac) >>
  asm_simp_tac bool_ss [fresh_vars_wrt_drop_fresh] >> strip_tac >>
  `straight_fresh (g c)` by simp[] >>
  drule_all fragGasFreshTheory.straight_fresh_clean_success_path >> strip_tac >>
  first_x_assum (qspec_then `ctx` strip_assume_tac) >>
  drule_all fragGasFreshTheory.straight_fresh_run_post >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  qexists_tac `OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  conj_tac
  >- (`gas_marked_path F ctx func s0 (0 + 0)
         (OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts))` suffices_by simp[] >>
      irule fragGasModeTheory.gas_marked_path_then >> qexists_tac `u` >>
      simp[fragGasModeTheory.gas_marked_path_def]) >>
  simp[] >> conj_tac >- (simp[expr_val_rel_def] >> metis_tac[]) >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> res_tac >> simp[] >>
      gvs[Abbr `u`, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE])
  >- (rpt strip_tac >> first_x_assum drule >>
      gvs[Abbr `u`, update_var_def])
  >- gvs[Abbr `u`, update_var_def] >>
  gvs[Abbr `u`, update_var_def]
QED

Theorem comp_bind_comp_return:
  !m. comp_bind m comp_return = m
Proof
  rw[FUN_EQ_THM, comp_bind_def, comp_return_def] >> pairarg_tac >> simp[]
QED

(* unop_frag_read_then with nothing after the read. *)
Theorem unop_frag_read:
  !ctx func cenv cx opc w1 r t v es0.
    opc <> INVOKE /\ ~is_terminator opc /\ is_word_type t /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          r = typed_val_to_w256 tv v) /\
    (!x ss n out.
       eval_operand x ss = SOME w1 /\ stmt_state_rel ctx func cenv cx es0 ss ==>
       step_inst_base (mk_inst n opc [x] [out]) ss =
         OK (update_var out r ss)) ==>
    unop_frag ctx func cenv cx (\x. emit_op opc [x]) w1 t (INL v) es0
Proof
  rpt strip_tac >>
  `(\x. emit_op opc [x]) = (\x. comp_bind (emit_op opc [x]) comp_return)` by
    simp[FUN_EQ_THM, comp_bind_comp_return] >>
  pop_assum SUBST1_TAC >> irule unop_frag_read_then >>
  simp[straight_fresh_return] >>
  qexists_tac `r` >>
  simp[comp_return_def, emitted_insts_refl, run_inst_seq_def] >>
  qexists_tac `r` >> asm_simp_tac bool_ss []
QED

(* Each read but .code: its code from the address's word, against the
   source's evaluate_account_op on the account at the address. *)
Theorem compile_acc_frag:
  !ctx func cenv cx item bs es0.
    item <> Code /\ LENGTH bs = 20 /\ accounts_well_typed es0.accounts ==>
    unop_frag ctx func cenv cx
      (\x. case item of
             Balance => emit_op BALANCE [x]
           | Codesize => emit_op EXTCODESIZE [x]
           | Codehash => emit_op EXTCODEHASH [x]
           | IsContract =>
               comp_bind (emit_op EXTCODESIZE [x])
                 (\c. emit_op GT [c; Lit 0w])
           | Address => comp_return x
           | Code => comp_return x)
      (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
      (account_item_type item)
      (unop_result cx (account_item_type item) (Acc item) [BaseT AddressT]
         (BytesV bs) es0) es0
Proof
  rpt strip_tac >>
  simp[unop_result_def, evaluate_builtin_def] >>
  qabbrev_tac `a = lookup_account (word_of_bytes_be bs) es0.accounts` >>
  `a.balance < 2 ** 256 /\ LENGTH a.code <= 24576` by
    gvs[Abbr `a`, accounts_well_typed_def, account_well_typed_def] >>
  drule address_word_w2w >> strip_tac >>
  Cases_on `item` >> gvs[]
  >~ [`comp_return`]
  >- (irule unop_frag_straight >>
      simp[account_item_type_def, vyperValueTheory.evaluate_type_def,
           evaluate_account_op_def, is_word_type_def, straight_fresh_return,
           comp_return_def, emitted_insts_refl, run_inst_seq_def])
  >~ [`comp_bind`]
  >- (irule unop_frag_read_then >>
      simp[account_item_type_def, vyperValueTheory.evaluate_type_def,
           evaluate_account_op_def, is_word_type_def, is_terminator_def,
           typed_val_to_w256_def, val_to_w256_def, straight_fresh_emit_op,
           fresh_write_op_def] >>
      qexists_tac `n2w (LENGTH a.code)` >>
      rpt strip_tac
      >~ [`step_inst_base`]
      >- (`!addr. (lookup_account addr ss.vs_accounts).code =
                  (lookup_account addr es0.accounts).code` by
            (fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
             metis_tac[accounts_agree_lookup]) >>
          gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
              typed_val_to_w256_def, Abbr `a`]) >>
      drule emit_op_GT_correct >>
      disch_then (qspecl_then [`n2w (LENGTH a.code)`, `0w`, `ss`] mp_tac) >>
      impl_tac >- gvs[eval_operand_def] >>
      strip_tac >> gvs[] >>
      `LENGTH a.code < dimword (:256)` by fs[dimword_def] >>
      Cases_on `a.code` >> gvs[bool_to_word_def]) >>
  irule unop_frag_read >>
  simp[account_item_type_def, vyperValueTheory.evaluate_type_def,
       evaluate_account_op_def, is_word_type_def, is_terminator_def] >>
  rpt strip_tac >>
  `!addr. (lookup_account addr ss.vs_accounts).balance =
          (lookup_account addr es0.accounts).balance /\
          (lookup_account addr ss.vs_accounts).code =
          (lookup_account addr es0.accounts).code /\
          (lookup_account addr ss.vs_accounts).nonce =
          (lookup_account addr es0.accounts).nonce` by
    (fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
     metis_tac[accounts_agree_lookup]) >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, Abbr `a`] >>
  simp[typed_val_to_w256_def, val_to_w256_def, i2w_def] >>
  rw[PAD_RIGHT, LENGTH_Keccak_256_w64, word_of_bytes_be_def,
     word_of_bytes_replicate_zero] >>
  gvs[vfmStateTheory.account_empty_def]
QED

(* ===== The lowering ===== *)

Theorem lower_value_acc:
  !cenv ty ann item e1 sa op sb.
    lower_value compile_expr cenv ty (Builtin ann (Acc item) [e1]) sa =
      (op, sb) /\ item <> Code ==>
    ?x s1.
      lower_value compile_expr cenv (BaseT AddressT) e1 sa = (x, s1) /\
      (case item of
         Balance => emit_op BALANCE [x]
       | Codesize => emit_op EXTCODESIZE [x]
       | Codehash => emit_op EXTCODEHASH [x]
       | IsContract =>
           comp_bind (emit_op EXTCODESIZE [x]) (\c. emit_op GT [c; Lit 0w])
       | Address => comp_return x
       | Code => comp_return x) s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_unary_builtin] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  Cases_on `item` >> gvs[compile_acc_def] >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def,
              comp_bind_def]
QED

Theorem names_builtin_acc[local]:
  !item args. ~names_builtin (Acc item) args
Proof
  `!bt args. names_builtin bt args ==> !item. bt <> Acc item` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_acc_stack:
  !cenv ty ann item args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann (Acc item) args) sa =
              (StackValue t op, sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_acc] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, as_stack_val_pair]
QED

Theorem account_item_type_word:
  !item. item <> Code ==> is_word_type (account_item_type item)
Proof
  Cases >> simp[account_item_type_def, is_word_type_def]
QED

(* ===== The case lemma ===== *)

(* An account read other than .code: compile_unop_sim with the address
   operand lowered as an address, and compile_acc_frag. *)
Theorem compile_acc_read_case:
  !nocalls ctx func cenv cx ann item args.
    item <> Code /\ exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Acc item) args)
Proof
  rpt strip_tac >> irule expr_vv_case_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_acc_stack] >>
  rw[expr_sim_case_def] >>
  `?e1. args = [e1] /\ ann = account_item_type item /\
        expr_type e1 = BaseT AddressT` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >>
  `expr_body_pre cenv cx env e1 es /\
   expr_sim ctx func cenv cx (BaseT AddressT) e1 es` by
    metis_tac[unop_operand_sim] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `account_item_type item`,
               `Acc item`, `e1`, `BaseT AddressT`,
               `\x. case item of
                      Balance => emit_op BALANCE [x]
                    | Codesize => emit_op EXTCODESIZE [x]
                    | Codehash => emit_op EXTCODEHASH [x]
                    | IsContract =>
                        comp_bind (emit_op EXTCODESIZE [x])
                          (\c. emit_op GT [c; Lit 0w])
                    | Address => comp_return x
                    | Code => comp_return x`, `es`]
    mp_tac compile_unop_sim >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[account_item_type_word]
    >- simp[is_word_type_def]
    >- (rpt strip_tac >> drule_all lower_value_acc >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
        simp[is_word_type_def])
    >- (rpt gen_tac >> strip_tac >>
        Cases_on `item` >> gvs[comp_return_def, cs_extends_refl, comp_bind_def] >>
        rpt (pairarg_tac >> gvs[]) >>
        imp_res_tac emit_op_extends_next_var >>
        metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS])
    >- simp[] >>
    rpt strip_tac >>
    `expr_body_pre cenv cx env e1 (es with gas_obs := gs1)` by simp[] >>
    qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`, `v1`,
                 `es1`] mp_tac expr_body_pre_word_value >>
    simp[is_word_type_def] >> strip_tac >>
    gvs[vyperValueTheory.evaluate_type_def] >>
    Cases_on `v1` >> gvs[value_has_type_def] >>
    irule compile_acc_frag >> simp[] >>
    `expr_body_pre cenv cx env e1 (es with gas_obs := gs1)` by simp[] >>
    drule_all expr_body_pre_eval >> simp[expr_sim_inv_def]) >>
  simp[]
QED
