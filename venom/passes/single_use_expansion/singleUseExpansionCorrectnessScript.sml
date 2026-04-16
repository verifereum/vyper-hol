Theory singleUseExpansionCorrectness
Ancestors
  singleUseExpansionProofs venomWf

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
    (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = LOG ==>
       ?n. HD inst.inst_operands = Lit n) ==>
    single_use_form (sue_expand_function fn)
Proof
  ACCEPT_TAC sue_establishes_single_use_form
QED

(* BLOCKER: sue_expand_ops creates ASSIGN instructions with
   inst_id := inst.inst_id * 1000 + op_idx. These IDs can collide with
   existing instruction IDs for arbitrary inputs (e.g., if some original
   ID equals id * 1000 + idx). Similarly, fresh output variables
   (sue_fresh_var id op_idx = "sue_<id>_<idx>") may collide with
   existing output variable names.
   Fix: either add preconditions (e.g., all IDs < 1000) or use a
   globally-unique ID generation scheme. *)
Theorem sue_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (sue_expand_function fn)
Proof
  cheat
QED

Theorem sue_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (sue_expand_function fn)
Proof
  cheat
QED
