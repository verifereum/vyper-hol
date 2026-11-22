(* The calldata member-address fragment contains no dynamic allocation. *)
Theory calldataMemberAddressCheck
Ancestors
  abiEncoder exprLoweringProps compileEnv emitHelper venomInst rich_list

Theorem calldata_member_address_non_dalloca:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) st = ((ep,dp),mid) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts st mid)
Proof
  Cases_on `dyn` >>
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED
