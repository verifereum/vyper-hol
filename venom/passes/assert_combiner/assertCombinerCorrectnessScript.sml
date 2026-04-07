Theory assertCombinerCorrectness
Ancestors
  assertCombinerProofs venomWf

Theorem ac_transform_function_correct:
  !fuel ctx fn s.
    let fn' = ac_transform_function fn in
    let dfg = dfg_build_function fn in
    wf_ssa fn /\
    wf_function fn /\
    fn_inst_wf fn /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
       ac_is_safe_between inst \/ inst.inst_opcode = ASSERT \/
       is_terminator inst.inst_opcode) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN ac_fresh_vars_fn fn) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM x inst.inst_outputs ==> x NOTIN ac_fresh_vars_fn fn) /\
    ac_inv fn dfg s /\
    (* no_redefine: all instruction outputs are undefined in initial state *)
    (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
       MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s)) /\
    (* Combined invariant preservation for fn blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn.fn_blocks /\
       ac_inv fn dfg s0 /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0)) /\
       s0.vs_inst_idx = 0 /\
       exec_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       ac_inv fn dfg s0' /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0'))) /\
    (* Combined invariant preservation for fn' blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn'.fn_blocks /\
       ac_inv fn dfg s0 /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0)) /\
       s0.vs_inst_idx = 0 /\
       exec_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       ac_inv fn dfg s0' /\
       (!bb' inst x. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions /\
          MEM x inst.inst_outputs ==> ~IS_SOME (lookup_var x s0'))) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv (ac_fresh_vars_fn fn))
               (execution_equiv UNIV)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)
Proof
  ACCEPT_TAC ac_transform_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem ac_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (ac_transform_function fn)
Proof
  cheat
QED

Theorem ac_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (ac_transform_function fn)
Proof
  cheat
QED
