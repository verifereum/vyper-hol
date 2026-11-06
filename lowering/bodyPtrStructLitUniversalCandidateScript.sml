(* Fixed narrow-declared/wide-annotated feasibility candidate.  These names
   keep the callable syntax opaque during symbolic frame reasoning. *)
Theory bodyPtrStructLitUniversalCandidate
Ancestors bodyPtrStructLitRepresentationProbe bodyPtrPreds exprLowering
  vyperAST bodyPtrDefs exprSimProps loweringPosts valueEncoding
  compileVyper supportedProgram bodyPtrStructLitWidenedCandidate vyperContext

Definition structlit_universal_call_def:
  structlit_universal_call =
    Call (TupleT [BaseT (BytesT (Dynamic 33)); BaseT (BytesT (Dynamic 1))])
      (IntCall (NONE,"structlit_universal")) [] NONE
End

Definition structlit_universal_value_def:
  structlit_universal_value =
    Builtin (TupleT [BaseT (BytesT (Dynamic 1)); BaseT (BytesT (Dynamic 1))])
      (MakeArray NONE (Fixed 2))
      [Literal (BaseT (BytesT (Dynamic 1))) (BytesL []);
       Literal (BaseT (BytesT (Dynamic 1))) (BytesL [])]
End

(* Even empty tuple elements require the full tuple footprint, unlike a
   top-level BytesV.  Thus the actual 128-byte declared allocation cannot
   satisfy the 160-byte annotated ptr_mem_ok, irrespective of memory/taint.
   This is not yet a legal child-frame obstruction: reaching this exact
   resource binding through INVOKE still needs a call/return theorem. *)
Theorem structlit_universal_capacity_obstruction:
  !cx s G tn x b.
    eval_operand (Var x) s = SOME (n2w b) /\ b < dimword (:256) /\
    FLOOKUP G x = SOME (b,128) ==>
    ~ptr_val_ok cx (expr_type structlit_universal_call)
      (ArrayV (TupleV [BytesV []; BytesV []])) (Var x) G tn s
Proof
  rpt gen_tac >> strip_tac >>
  simp[structlit_universal_call_def, expr_type_def, ptr_val_ok_def,
       ptr_mem_ok_def, structlit_probe_tuple_evaluations] >>
  EVAL_TAC >> simp[]
QED

(* No StructLit in this program: support of an enclosing effectful StructLit
   is not being assumed.  Only the callable needed by the child is fixed. *)
Definition structlit_universal_program_def:
  structlit_universal_program =
    [FunctionDecl Internal Pure F F "structlit_universal" [] []
      (structlit_identity_type 1) [Return (SOME structlit_universal_value)]]
End

Definition structlit_universal_env_def:
  structlit_universal_env =
    build_compile_env structlit_universal_program Internal Pure
      "structlit_universal" [] (structlit_identity_type 1)
      [Return (SOME structlit_universal_value)] F
End

Theorem structlit_universal_program_supported:
  supported_program structlit_universal_program
Proof
  EVAL_TAC
QED

Theorem structlit_universal_return_info:
  structlit_universal_env.ce_func_info "structlit_universal" = (0,128,[]) /\
  structlit_universal_env.ce_func_return_type "structlit_universal" =
    structlit_identity_type 1
Proof
  EVAL_TAC
QED

Definition structlit_universal_compiled_def:
  structlit_universal_compiled =
    lower_value compile_expr structlit_universal_env
      (expr_type structlit_universal_call) structlit_universal_call
      (initial_compile_state "caller")
End

Theorem structlit_universal_call_instructions:
  (SND structlit_universal_compiled).cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 128w] ["%0"];
     mk_inst 1 INVOKE
       [Label "internal 0 structlit_universal()_runtime"; Var "%0"] []]
Proof
  EVAL_TAC
QED

Definition structlit_universal_context_def:
  structlit_universal_context =
    empty_evaluation_context with sources :=
      [(empty_evaluation_context.txn.target,
        [(NONE,structlit_universal_program)])]
End

Theorem structlit_universal_callable:
  get_module_code structlit_universal_context NONE =
    SOME structlit_universal_program /\
  lookup_callable_function F "structlit_universal" structlit_universal_program =
    SOME (Pure,F,[],[],structlit_identity_type 1,
      [Return (SOME structlit_universal_value)])
Proof
  EVAL_TAC
QED

(* Universal-premise checkpoint (not a candidate refutation): unfolding
   body_expr_ptr_ok and expr_sim_ptr leaves gas_outcome_ptr for this call
   under arbitrary body_inv/expr_body_pre, code embedding, state relation,
   gas_admissible and ghost_inv.  The concrete compiler certificate above
   fixes neither that embedding nor the dynamic INVOKE execution.

   A rejection proof still needs a legal such frame, successful source call,
   and a call/return execution characterization preserving the exact
   return operand binding SOME (b,128) from fresh ALLOCA through INVOKE.
   A positive proof instead needs the annotated 160-byte coverage, which
   the capacity obstruction rules out whenever that exact binding survives.
   No general counted pointer call/return characterization with these
   premises is supplied by the existing local return transport lemmas.
   Proving it requires entering the callable simulation/body machinery;
   no such induction is undertaken here.  In particular this file asserts
   neither body_expr_ptr_ok nor its negation for this fixed context. *)
