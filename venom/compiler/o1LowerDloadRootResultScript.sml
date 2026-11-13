Theory o1LowerDloadRootResult
Ancestors
  o1ContractSimplifyCfg o1PassLift o1PassContract venomExecSemantics venomInst

Theorem ld_root_result_shape:
  o1_ctx_shape C ==>
  (?e. run_context fuel C vs = Error e) \/
  (?s. run_context fuel C vs = Halt s) \/
  (?a s. run_context fuel C vs = Abort a s)
Proof
  strip_tac >>
  `!t. run_context fuel C vs <> OK t` by
    (simp[run_context_def, run_function_def] >>
     Cases_on `C.ctx_entry` >> simp[] >>
     Cases_on `lookup_function x C.ctx_functions` >> simp[] >>
     Cases_on `fn_entry_label x'` >> simp[run_blocks_not_OK]) >>
  `!vals t. run_context fuel C vs <> IntRet vals t` by
    (drule o1_ctx_shape_no_intret >> simp[]) >>
  Cases_on `run_context fuel C vs` >> gvs[]
QED
