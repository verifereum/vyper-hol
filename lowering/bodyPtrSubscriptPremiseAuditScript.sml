(* Bounded nested-mapping vacuity probe. No new semantic definitions. *)
Theory bodyPtrSubscriptPremiseAudit
Ancestors
  exprSimHypsDefs supportedExprTraverse allocLimits vyperAST

(* The outer precondition still traverses a mapping-valued base. *)
Theorem subscript_pre_excludes_key_evm_run:
  expr_body_pre cenv cx env (Subscript ty operand key) es ==>
  ~expr_has_evm_run key
Proof
  simp[expr_body_pre_def, expr_has_evm_run_thm] >> metis_tac[]
QED

(* Proposed key: a delegate raw call, whose EVM execution could otherwise
   change arbitrary storage. It is excluded even inside a nested mapping
   base; no frame-realizability or unsafe target-run claim is made. *)
Theorem nested_mapping_delegate_key_excluded:
  ~expr_body_pre cenv cx env
    (Subscript ty
      (Subscript NoneT (TopLevelName NoneT nsid)
        (Call kt (RawCallTarget (flags with rcf_is_delegate := T)) args dflt))
      idx) es
Proof
  simp[expr_body_pre_def, expr_has_evm_run_thm,
       expr_evm_run_root_def]
QED

(* Premise audit:
   - type_place_expr admits arbitrary WELL-TYPED keys, not arbitrary syntax
     (bodyPtrSubscriptBaseAudit.mapping_key_place_typing). Mapping-valued
     operand vacuity therefore does not remove the inner typing check.
   - byte_widths_expr and alloc_limits_expr explicitly recurse through both
     operands of every Subscript (definitions lines 87 and 77 respectively).
   - int_calls_expr traverses nested operands; call_evaluation_safe and EVERY
     supported calls in expr_body_pre therefore still constrain inner keys.
   - supported_expr_exists traverses both operands, so ABI decode occurrence
     requirements still reach inner keys. Dynamic ABI compatibility is global.
   - expr_sim_inv and body_inv are not vacuous outer-frame assumptions. No
     concrete frame satisfying them was constructed in this bounded audit.
   - delegate raw-call key above: excluded by the checked theorem BEFORE
     source success, source gas admissibility, or target pointer checks arise.
   - base body_expr_ptr_ok vacuity alone does not supply a failing operation;
     index body judgment alone does not supply such an operation either.
   Outcome: this explicit candidate is excluded, overall route inconclusive.
   No concrete operation violating pointer safety while satisfying all outer
   clauses was found. No counterexample to the frozen theorem is claimed.
   Return for strategy review, not broader search or suffix integration.
*)
