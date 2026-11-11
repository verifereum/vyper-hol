(* Functional synchronization of an INVOKE entry with its caller decode. *)
Theory bodyIntCallInvokeEntry
Ancestors
  fragGasFocus venomExecSemantics venomState

Theorem gas_invoke_entry_decode:
  gas_invoke_entry (ctx,func) s callee entered /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (label,ops) /\
  eval_operands ops s = SOME argv ==>
  ~s.vs_halted /\ inst.inst_opcode = INVOKE /\
  lookup_function label ctx.ctx_functions = SOME callee /\
  ?setup first phi_state.
    setup_callee callee argv s = SOME setup /\
    lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
    eval_phis setup first.bb_instructions = OK phi_state /\
    ~phi_state.vs_halted /\
    entered = phi_state with vs_inst_idx :=
      phi_prefix_length first.bb_instructions
Proof
  rw[gas_invoke_entry_def] >> gvs[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
