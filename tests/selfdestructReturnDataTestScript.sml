Theory selfdestructReturnDataTest
Ancestors
  venomExecSemantics venomInst venomState asmSem list

Theorem venom_selfdestruct_clears_old_return_data:
  !s.
    ~s.vs_call_ctx.cc_static ==>
    ?t.
      step_inst_base (mk_inst 0 SELFDESTRUCT [Lit 0w] [])
        (s with vs_returndata := [1w]) = Halt t /\
      t.vs_returndata = []
Proof
  rpt strip_tac >>
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def,
       halt_state_def, set_returndata_def]
QED

Theorem asm_selfdestruct_clears_old_return_data:
  !s.
    ?t.
      asm_selfdestruct
        (s with <|as_stack := [0w]; as_returndata := [1w]|>) = AsmHalt t /\
      t.as_returndata = []
Proof
  simp[asm_selfdestruct_def]
QED
