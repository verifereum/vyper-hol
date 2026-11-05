(* Account read semantics, separated from pointer-path composition. *)
Theory bodyPtrEnvBuiltinsAccountReads
Ancestors
  exprSimAccounts accountsRelProps codegenRel contextCodegenRel
  compileEnv exprLoweringProps
  venomExecSemantics venomInst venomState vfmState valueEncoding
  vyperValue vyperInterpreter vyperTypeInvariants vyperTypeBytesCrypto
  list rich_list words integer_word byte vyperContext vyperTypeSystem
  valueEncodingProofs

Theorem account_read_frame:
  stmt_state_rel ctx fn cenv cx es s ==>
  !addr.
    (lookup_account addr s.vs_accounts).balance =
      (lookup_account addr es.accounts).balance /\
    (lookup_account addr s.vs_accounts).code =
      (lookup_account addr es.accounts).code /\
    (lookup_account addr s.vs_accounts).nonce =
      (lookup_account addr es.accounts).nonce
Proof
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  metis_tac[accounts_agree_lookup]
QED

Theorem account_read_typed_step:
  MEM (item,opc) [(Balance,BALANCE); (Codesize,EXTCODESIZE); (Codehash,EXTCODEHASH)] /\
  LENGTH bs = 20 /\
  eval_operand arg s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  stmt_state_rel ctx fn cenv cx es s /\
  evaluate_type (get_tenv cx) (account_item_type item) = SOME tv ==>
  step_inst_base (mk_inst id opc [arg] [out]) s =
    OK (update_var out (typed_val_to_w256 tv
      (evaluate_account_op item bs
        (lookup_account (word_of_bytes_be bs) es.accounts))) s)
Proof
  simp[] >> strip_tac >> gvs[] >>
  gvs[account_item_type_def, evaluate_type_def] >>
  drule_all account_read_frame >> strip_tac >>
  drule address_word_w2w >> strip_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
  simp[evaluate_account_op_def, typed_val_to_w256_def, val_to_w256_def, i2w_def] >>
  rw[PAD_RIGHT, LENGTH_Keccak_256_w64, word_of_bytes_be_def,
     word_of_bytes_replicate_zero] >>
  gvs[account_empty_def]
QED

Theorem account_iscontract_gt_step:
  LENGTH code < dimword (:256) /\
  eval_operand arg s = SOME (n2w (LENGTH code)) ==>
  step_inst_base (mk_inst id GT [arg; Lit 0w] [out]) s =
    OK (update_var out (bool_to_word (code <> [])) s)
Proof
  strip_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `code` >> gvs[bool_to_word_def]
QED

Theorem account_codesize_encoding:
  typed_val_to_w256 (BaseTV (UintT 256))
    (evaluate_account_op Codesize bs a) = n2w (LENGTH a.code)
Proof
  simp[evaluate_account_op_def, typed_val_to_w256_def, val_to_w256_def, i2w_def]
QED

Theorem account_iscontract_encoding:
  evaluate_type (get_tenv cx) (account_item_type IsContract) = SOME tv ==>
  typed_val_to_w256 tv (evaluate_account_op IsContract bs a) =
    bool_to_word (a.code <> [])
Proof
  Cases_on `a.code = []` >>
  simp[account_item_type_def, evaluate_type_def, evaluate_account_op_def,
       typed_val_to_w256_def, val_to_w256_def, bool_to_word_def]
QED
