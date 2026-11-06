Theory bodyPtrPopEntryFeasibility
Ancestors bodyPtrPopCalleeCandidate bodyPtrPopGlobalLegality supportedProgram
  compileVyper vyperCompiler vyperValue

(* One bounded supported-module diagnostic. The named fixture permits sharing
   unit lowering while comparing complete Pop suffixes, not just guard windows.
   The word-array Pop is supported; an indexed read supplies address arithmetic. *)
Definition pop_feasible_word_def:
  pop_feasible_word = BaseT (UintT 256)
End
Definition pop_feasible_array_def:
  pop_feasible_array = ArrayT pop_feasible_word (Dynamic 2)
End
Definition pop_feasible_tops_def:
  pop_feasible_tops =
    [VariableDecl Private Storage "b" pop_feasible_array (SOME 0);
     FunctionDecl External Nonpayable F F "__default__" [] [] NoneT
       [Expr (Subscript pop_feasible_word
         (TopLevelName pop_feasible_array (NONE,"b"))
         (Literal pop_feasible_word (IntL 0)));
        Expr (Pop pop_feasible_word (TopLevelNameTarget (NONE,"b")))]]
End

Theorem pop_feasible_supported:
  supported_program pop_feasible_tops
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_feasible_lowering_exists:
  IS_SOME (lower_vyper_runtime_unit pop_feasible_tops pop_global_policy)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Definition pop_feasible_unit_def:
  pop_feasible_unit =
    THE (lower_vyper_runtime_unit pop_feasible_tops pop_global_policy)
End

(* Full nine-instruction nested storage suffix, with arbitrary SSA names and
   instruction IDs. Prefix positions are enumerated only in this finite unit. *)
Theorem pop_feasible_nested_suffix_absent:
  EVERY (\fn. EVERY (\bb.
    !h a b c d e f g j0 j1 j2 j3 j4 j5 j6 j7 j8 esz.
    ~MEM
      [mk_inst j0 SLOAD [Var h] [a];
       mk_inst j1 ISZERO [Var a] [b];
       mk_inst j2 ISZERO [Var b] [c];
       mk_inst j3 ASSERT [Var c] [];
       mk_inst j4 SUB [Var a; Lit 1w] [d];
       mk_inst j5 SSTORE [Var h; Var d] [];
       mk_inst j6 ADD [Var h; Lit 1w] [e];
       mk_inst j7 MUL [Var d; Lit esz] [f];
       mk_inst j8 ADD [Var e; Var f] [g]]
      (MAP (\n. TAKE 9 (DROP n bb.bb_instructions))
        (COUNT_LIST (LENGTH bb.bb_instructions)))) fn.fn_blocks)
    pop_feasible_unit.cu_context.ctx_functions
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_feasible_unit_lowered:
  lower_vyper_runtime_unit pop_feasible_tops pop_global_policy =
    SOME pop_feasible_unit
Proof
  mp_tac pop_feasible_lowering_exists >>
  Cases_on `lower_vyper_runtime_unit pop_feasible_tops pop_global_policy` >>
  simp[pop_feasible_unit_def]
QED

Theorem pop_feasible_entry_lookup:
  ?fn. venomInst$lookup_function "__entry"
    pop_feasible_unit.cu_context.ctx_functions = SOME fn
Proof
  qexists_tac `THE (venomInst$lookup_function "__entry"
    pop_feasible_unit.cu_context.ctx_functions)` >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

(* Entry-premise ledger:
   - supported_program and actual runtime-unit lowering hold for this module;
     __entry is a function of that very lowered context.
   - Every block of every function has been checked at every finite instruction
     position for the complete nested storage Pop suffix, including its store
     and returned-address arithmetic; IDs and SSA names are arbitrary.
   - This is finite absence, not universal compiler exclusion. A top-level Pop
     with literal header is deliberately present and is NOT excluded.
   - No stmt_state_rel, ghost_inv, expr_body_pre, gas_admissible or universal
     index judgment is asserted for a nested Pop. Function membership alone
     supplies none of these premises. No counterexample follows.
   Existing global and callee fixtures were audited before selecting this unit:
   pop_global_supported/unit_lowered use an assignment-only internal body with
   no INVOKE; pop_callee_supported/lowering_exists have a real call but separate
   INVOKE from SSTORE across functions (pop_callee_no_containment). Neither has
   the supported word-array Pop plus indexed read collision tested here. *)
