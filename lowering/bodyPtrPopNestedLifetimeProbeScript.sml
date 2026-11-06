Theory bodyPtrPopNestedLifetimeProbe
Ancestors
  bodyPtrPopRegionStore bodyPtrPopSavedRegion bodyPtrPopStorageExecProbe
  fragGasSeqPtr exprLowering vyperValue vfmState words ptrDiscipline
  venomInst venomState venomExecSemantics vyperCompiler

(* Concrete compiler/layout diagnostic, not a body-frame witness. The root
   is DynArray[DynArray[uint256,2],1]: root header 0, saved child header 1,
   live payload 2, unused payload 3. Pop shortens root to zero. This nested
   element type is outside the current source support whitelist. Definitions
   below only name the executable compiler fragment and its test states. *)
Definition pop_lifetime_code_def:
  pop_lifetime_code =
    (SND (compile_dynarray_pop (Lit 0w) 1 3 F NONE LocStorage
      (initial_compile_state "entry"))).cs_current_insts
End

Definition pop_lifetime_start_def:
  pop_lifetime_start = sstore 0w 1w (sstore 1w 1w
    (sstore 2w 7w (init_venom_state "entry")))
End

Definition pop_lifetime_taint_def:
  pop_lifetime_taint = entry_taint with t_stor := {(3w,0)}
End

Theorem pop_lifetime_layout:
  type_slot_size (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) = 3 /\
  type_slot_size
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 1)) = 4
Proof
  EVAL_TAC
QED

Theorem pop_lifetime_run:
  ?s. run_inst_seq pop_lifetime_code pop_lifetime_start = OK s /\
      eval_operand (Var "%6") s = SOME 1w /\
      sload 0w s = 0w /\ sload 1w s = 1w /\ sload 2w s = 7w
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC
QED

Theorem pop_lifetime_initial_observer:
  pop_region_taint_ok
    (pop_lifetime_start.vs_accounts
      pop_lifetime_start.vs_call_ctx.cc_address).storage
    1 (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
    pop_lifetime_taint.t_stor
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem pop_lifetime_checked:
  ?G tn. inst_seq_ptr D 0 (mk_venom_context [] NONE)
    (mk_raw_function "%lifetime"
      [<| bb_label := "entry"; bb_instructions := pop_lifetime_code |>])
    [] FEMPTY pop_lifetime_taint pop_lifetime_code pop_lifetime_start G tn /\
    tn.t_stor = {(3w,0)}
Proof
  EVAL_TAC >> simp[pred_setTheory.SUBSET_DEF] >> rpt conj_tac >> gen_tac >>
  Cases_on `op` >> simp[] >> EVAL_TAC >>
  Cases_on `s = "%4"` >> Cases_on `s = "%5"` >> simp[]
QED

Theorem pop_lifetime_final_observer:
  run_inst_seq pop_lifetime_code pop_lifetime_start = OK s ==>
  pop_region_taint_ok
    (s.vs_accounts s.vs_call_ctx.cc_address).storage
    1 (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) {(3w,0)} /\
  lookup_storage 1w (s.vs_accounts s.vs_call_ctx.cc_address).storage = 1w /\
  dead_bytes (s.vs_accounts s.vs_call_ctx.cc_address).storage 0
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 1)) 1 0
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss] >> EVAL_TAC
QED

(* Complete instruction accounting is in pop_lifetime_checked: reads and
   arithmetic do not change t_stor; the compiled SSTORE clears the root key
   and leaves the saved child's unused-payload taint at (3,0). The run and
   final observer separately check unchanged raw child header (length 1)
   while root length becomes zero and that child is globally dead.
   This local fixture establishes layout, actual compiler suffix execution,
   per-instruction pointer checks, raw header preservation and local taint.
   It does NOT establish supported_program/body_inv, expr_body_pre for a
   source caller, lookup_function/stmt_state_rel in a lowered context, an
   index body_expr_ptr_ok, or full source gas_outcome_ptr. In particular the
   source element-array Pop is excluded by pop_supported_dynamic_element.
   Therefore it is neither a full-frame counterexample nor a proof of the
   universal SubscriptTarget transport. INVOKE/typed writes remain open. *)
