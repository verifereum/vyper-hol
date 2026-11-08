Theory singleUseExpansionCorrectness
Ancestors
  singleUseExpansionProofs singleUseExpansionSupplySim venomWf irSupply

(* Semantic correctness: running a function after SUE expansion gives an
   equivalent result (up to fresh variable names) to the original. *)
Theorem sue_expand_function_correct:
  !fuel ctx fn s.
    fn_inst_wf fn /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
       ~is_alloca_op inst.inst_opcode /\ sue_operands_wf inst) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (sue_expand_function fn) s)
Proof
  ACCEPT_TAC sue_expand_function_correct_proof
QED

(* ===== Obligations ===== *)

(* After SUE expansion, every non-exempt variable is used at most once. *)
Theorem sue_establishes_single_use:
  !fn.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    (!inst. MEM inst (fn_insts fn) /\
         (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) ==>
       ?n. HD inst.inst_operands = Lit n) ==>
    single_use_form (sue_expand_function fn)
Proof
  ACCEPT_TAC sue_establishes_single_use_form
QED

(* The dispatched supply pass allocates fresh outputs outside the input. *)
Theorem sue_preserves_ssa_form:
  ∀s fn fn' s'.
    ssa_form fn ∧ ir_supply_covers_fn s fn ∧
    sue_expand_function_supply s fn = (fn',s') ⇒
    ssa_form fn'
Proof
  metis_tac[sue_supply_replay, sue_expand_function_supply_ssa_form]
QED

(* Replay supplies the instruction-id invariant without an extra premise. *)
Theorem sue_preserves_wf_function:
  ∀s fn fn' s'.
    wf_function fn ∧ ir_supply_covers_fn s fn ∧
    sue_expand_function_supply s fn = (fn',s') ⇒
    wf_function fn'
Proof
  metis_tac[sue_supply_replay, sue_expand_function_supply_wf_function]
QED
