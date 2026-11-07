Theory entryDispatcherCode
Ancestors
  entryBuiltinCode entryAggregateCode entryValueCode entryArithmeticCode entryLocationValueCode
  entryCodePredicate entryContextCodePredicate exprLowering supportedExprForms

Theorem entry_supported_binop_no_membership[local]:
  supported_binop op ty rhs lit nn ==> op <> In /\ op <> NotIn
Proof
  Cases_on `op` >> simp[supported_binop_def]
QED

Theorem entry_code_comparison_hash[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_bytestring_hash p)
Proof
  simp[compile_bytestring_hash_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_dispatch_array[local]:
  (!e ce et. MEM e args ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty (MakeArray o' b) args)
Proof
  strip_tac >> rw[entry_preserves_code_def] >> Cases_on `o'` >>
  gvs[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_alloc_buffer)
  >~ [`compile_make_tuple _ _ _ _ _ _ = _`]
  >- (drule entry_code_make_tuple >>
      disch_then (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))) >>
  drule entry_code_make_array >>
  disch_then (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
QED


Theorem entry_code_dispatch_env[local]:
  supported_builtin_form tops ret_ty (Env e) args ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty (Env e) args)
Proof
  simp[supported_builtin_form_def] >> strip_tac >> gvs[] >>
  rw[entry_preserves_code_def, compile_builtin_dispatch_body_def, as_stack_val_def] >>
  Cases_on `compile_env_var e st` >> gvs[as_stack_val_def] >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_env_var)
QED

Theorem entry_code_dispatch_unary[local]:
  supported_builtin_form tops ret_ty bi [a] /\
  (!ce et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et a)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty bi [a])
Proof
  Cases_on `bi` >> simp[supported_builtin_form_def] >> rpt strip_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _`]
  >- (irule entry_code_dispatch_array >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Acc item) _`]
  >- (rw[entry_preserves_code_def, compile_builtin_dispatch_body_def] >>
      Cases_on `item` >> gvs[compile_acc_def] >>
      gvs[oneline as_stack_val_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      `!et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
         (lower_value cfn cenv et a)` by
        (gen_tac >> irule entry_code_lower_value >> simp[]) >>
      pop_assum (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th)) >>
      map_every (fn opc => imp_res_tac (SRULE [entry_preserves_code_def]
        (Q.INST [`opc` |-> opc] entry_code_emit_op)))
        [`BALANCE`, `EXTCODEHASH`, `EXTCODESIZE`, `GT`]) >>
  rw[entry_preserves_code_def, compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `!et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
     (lower_value cfn cenv et a)` by
    (gen_tac >> irule entry_code_lower_value >> simp[]) >>
  pop_assum (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th)) >>
  gvs[oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
    [entry_code_invert, entry_code_neg, entry_code_builtin_abs,
     entry_code_blobhash, entry_code_blockhash, entry_code_as_wei_value_int,
     entry_code_as_wei_value_decimal, entry_code_slice_calldata, entry_code_uint2str] >>
  imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> `ISZERO`] entry_code_emit_op))
QED

Theorem entry_code_dispatch_binary[local]:
  supported_builtin_form tops ret_ty bi [a;b] /\
  (!e ce et. MEM e [a;b] ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty bi [a;b])
Proof
  Cases_on `bi` >> simp[supported_builtin_form_def] >> rpt strip_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _`]
  >- (irule entry_code_dispatch_array >> simp[] >> metis_tac[]) >>
  imp_res_tac entry_supported_binop_no_membership >>
  rw[entry_preserves_code_def, compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  `!e ce et. e = a \/ e = b ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (lower_value cfn ce et e)` by
    (rpt strip_tac >> irule entry_code_lower_value >> simp[]) >>
  pop_assum (fn th => map_every (fn e =>
    imp_res_tac (SRULE [entry_preserves_code_def] (Q.SPEC e th))) [`a`, `b`]) >>
  qpat_x_assum `!e ce et. _ ==> entry_preserves_code _ _`
    (fn th => map_every (fn e =>
      imp_res_tac (SRULE [entry_preserves_code_def] (Q.SPEC e th))) [`a`, `b`]) >>
  map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
    [entry_code_unwrap_value, entry_code_ecadd_points, entry_code_ecmul_point,
     entry_code_pow_mod256, entry_code_binop] >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_comparison_hash) >>
  map_every (fn opc => imp_res_tac (SRULE [entry_preserves_code_def]
    (Q.INST [`opc` |-> opc] entry_code_emit_op))) [`EQ`, `ISZERO`] >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]
QED

Theorem entry_code_dispatch_ternary[local]:
  supported_builtin_form tops ret_ty bi [a;b;c] /\
  (!e ce et. MEM e [a;b;c] ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty bi [a;b;c])
Proof
  Cases_on `bi` >> simp[supported_builtin_form_def] >> rpt strip_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _`]
  >- (irule entry_code_dispatch_array >> simp[] >> metis_tac[]) >>
  rw[entry_preserves_code_def, compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  `!e ce et. e = a \/ e = b \/ e = c ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (lower_value cfn ce et e)` by
    (rpt strip_tac >> irule entry_code_lower_value >> simp[]) >>
  pop_assum (fn th => map_every (fn e =>
    imp_res_tac (SRULE [entry_preserves_code_def] (Q.SPEC e th))) [`a`, `b`, `c`]) >>
  map_every (fn th => imp_res_tac (SRULE [entry_preserves_code_def] th))
    [entry_code_addmod, entry_code_mulmod] >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]
QED

Theorem entry_code_dispatch_quaternary[local]:
  supported_builtin_form tops ret_ty bi [a;b;c;d] /\
  (!e ce et. MEM e [a;b;c;d] ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty bi [a;b;c;d])
Proof
  Cases_on `bi` >> simp[supported_builtin_form_def] >> rpt strip_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _`]
  >- (irule entry_code_dispatch_array >> simp[] >> metis_tac[]) >>
  rw[entry_preserves_code_def, compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  `!e ce et. e = a \/ e = b \/ e = c \/ e = d ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (lower_value cfn ce et e)` by
    (rpt strip_tac >> irule entry_code_lower_value >> simp[]) >>
  pop_assum (fn th => map_every (fn e =>
    imp_res_tac (SRULE [entry_preserves_code_def] (Q.SPEC e th))) [`a`, `b`, `c`, `d`]) >>
  imp_res_tac (SRULE [entry_preserves_code_def] entry_code_ecrecover) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]
QED

Theorem entry_code_builtin_dispatch_body:
  supported_builtin_form tops ret_ty bi args /\
  (!e ce et. MEM e args ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_builtin_dispatch_body cfn cenv ret_ty ty bi args)
Proof
  Cases_on `bi` >> simp[supported_builtin_form_def] >> rpt strip_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _`]
  >- (irule entry_code_dispatch_array >> simp[] >> metis_tac[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Env _) _`]
  >- (irule entry_code_dispatch_env >> simp[supported_builtin_form_def] >> metis_tac[]) >>
  namedCases_on `args` ["", "a rest"] >> gvs[] >>
  namedCases_on `rest` ["", "b rest2"] >> gvs[]
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ _ [a]`],
    irule entry_code_dispatch_unary >> simp[supported_builtin_form_def] >> metis_tac[]) >>
  namedCases_on `rest2` ["", "c rest3"] >> gvs[]
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ _ [a;b]`],
    irule entry_code_dispatch_binary >> simp[supported_builtin_form_def] >> metis_tac[]) >>
  namedCases_on `rest3` ["", "d rest4"] >> gvs[]
  >>~- ([`compile_builtin_dispatch_body _ _ _ _ _ [a;b;c]`],
    irule entry_code_dispatch_ternary >> simp[supported_builtin_form_def] >> metis_tac[]) >>
  Cases_on `rest4` >> gvs[] >>
  irule entry_code_dispatch_quaternary >> simp[supported_builtin_form_def] >> metis_tac[]
QED
