(*
 * Expression Lowering Properties
 *
 * TOP-LEVEL:
 *   run_inst_seq             — run instruction sequence on Venom state
 *   emitted_insts            — extract new instructions from compile state
 *   compile_expr_correct     — main expression lowering correctness
 *   compile_literal_vv_correct  — word literal case
 *   compile_name_correct     — variable lookup case
 *   compile_binop_correct    — binary operation case
 *
 * Helper:
 *   vars_only_change         — compile_expr only adds SSA vars, no mem/storage side effects
 *
 * Mirrors correctness of: exprLoweringScript.sml (compile_expr)
 * Source semantics: vyperInterpreterScript.sml (eval_expr)
 * Target semantics: venomExecSemanticsScript.sml (step_inst_base)
 *)

Theory exprLoweringProps
Ancestors
  exprLowering emitHelper compileEnv
  venomExecSemantics venomState
  vyperInterpreter vyperContext
  vyperState vyperValueOperation
  valueEncoding valueEncodingProofs

(* ===== Instruction Sequence Execution ===== *)

(* Run a list of instructions sequentially via step_inst_base.
   Returns OK if all succeed, or the first non-OK result. *)
Definition run_inst_seq_def:
  run_inst_seq [] ss = OK ss ∧
  run_inst_seq (i::is) ss =
    case step_inst_base i ss of
      OK ss' => run_inst_seq is ss'
    | other => other
End

(* ===== Compile State Helpers ===== *)

(* Instructions emitted between two compile states (within same block) *)
Definition emitted_insts_def:
  emitted_insts (st:compile_state) (st':compile_state) =
    DROP (LENGTH st.cs_current_insts) st'.cs_current_insts
End

(* No new blocks were created *)
Definition same_blocks_def:
  same_blocks (st:compile_state) (st':compile_state) ⇔
    st'.cs_blocks = st.cs_blocks ∧
    st'.cs_current_bb = st.cs_current_bb
End

(* ===== Main Correctness Theorem ===== *)

(* For a "simple" (single-block) expression:
   - The emitted instructions run successfully on the Venom state
   - The returned operand evaluates to the encoded Vyper value
   - State relation is preserved

   NOTE: This covers Literal, Name, BinOp, Compare, UnaryOp, Env vars.
   IfExp (multi-block) needs a separate theorem using run_block. *)
(* Supported expressions: single-block compilation forms.
   Phase 1 handles: Literal, Name, Env vars, Not, Neg, BinOp.
   IfExp is multi-block (separate theorem needed).
   Other forms are not yet implemented in compile_expr. *)
Definition supported_expr_def:
  supported_expr (Literal _ _) = T ∧
  supported_expr (Name _ _) = T ∧
  supported_expr (Builtin _ (Env _) _) = T ∧
  supported_expr (Builtin _ Not (e::_)) = supported_expr e ∧
  supported_expr (Builtin _ Neg (e::_)) = supported_expr e ∧
  supported_expr (Builtin _ (Bop _) (e1::e2::_)) =
    (supported_expr e1 ∧ supported_expr e2) ∧
  supported_expr _ = F
End

Theorem compile_expr_correct:
  ∀ cenv cx ty e es ss st op st' v es'.
    state_rel cenv cx es ss ∧
    fresh_vars_wrt st ss ∧
    supported_expr e ∧
    eval_expr cx e es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty e st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      state_rel cenv cx es' ss' ∧
      same_blocks st st' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      ¬ss'.vs_halted ∧
      EVERY (λi. ¬is_terminator i.inst_opcode ∧ i.inst_opcode ≠ INVOKE)
        (emitted_insts st st') ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)
Proof
  cheat
QED

(* ===== Infrastructure Lemmas ===== *)

(* Helper: if xs = ys ++ zs then DROP (LENGTH ys) xs = zs *)
Theorem DROP_PREFIX:
  ∀ ys zs. DROP (LENGTH ys) (ys ++ zs) = zs
Proof
  Induct >> simp[]
QED

(* run_inst_seq concatenation: OK prefix *)
Theorem run_inst_seq_append:
  ∀ is1 is2 ss ss'.
    run_inst_seq is1 ss = OK ss' ⇒
    run_inst_seq (is1 ++ is2) ss = run_inst_seq is2 ss'
Proof
  Induct_on `is1` >> rw[run_inst_seq_def, comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `step_inst_base h ss` >> gvs[]
QED

(* run_inst_seq concatenation: non-OK prefix *)
Theorem run_inst_seq_append_err:
  ∀ is1 is2 ss.
    (∀s. run_inst_seq is1 ss ≠ OK s) ⇒
    run_inst_seq (is1 ++ is2) ss = run_inst_seq is1 ss
Proof
  Induct_on `is1` >> rw[run_inst_seq_def, comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `step_inst_base h ss` >> gvs[]
QED

(* emit_op extends instructions: appends exactly one instruction *)
Theorem emit_op_extends:
  ∀ opc ops st v st'.
    emit_op opc ops st = (v, st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def]
  >> simp[emitted_insts_def, same_blocks_def,
          rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_LENGTH_NIL, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* emit_void extends instructions: appends exactly one instruction *)
Theorem emit_void_extends:
  ∀ opc ops st st'.
    emit_void opc ops st = ((), st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[emitted_insts_def, same_blocks_def,
          rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_LENGTH_NIL, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* emitted_insts composition through intermediate state *)
Theorem emitted_insts_append:
  ∀ st st1 st2.
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2
    ⇒
    emitted_insts st st2 =
      emitted_insts st st1 ++ emitted_insts st1 st2
Proof
  rw[emitted_insts_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> pop_assum (fn th => SUBST_ALL_TAC th)
  >> pop_assum (fn th =>
       `LENGTH st.cs_current_insts ≤ LENGTH st1.cs_current_insts` by
         (SUBST1_TAC th >> simp[]) >>
       assume_tac th)
  >> simp[rich_listTheory.DROP_APPEND1, DROP_PREFIX]
QED

(* ===== Per-Expression Lemmas ===== *)

(* --- Literal --- *)
(* Covers word-type literals only. Bytestring/string literals allocate buffers. *)
Theorem compile_literal_vv_correct:
  ∀ cenv cx ty l es ss st vv st'.
    state_rel cenv cx es ss ∧
    compile_literal_vv ty l st = (vv, st') ∧
    (* Word literals only — dynamic bytes/strings allocate buffers *)
    (* Word literals only — exclude bytestring/string types that allocate buffers *)
    (∀ bs. l = BytesL bs ⇒ ∃ m. ty = BaseT (BytesT (Fixed m))) ∧
    (∀ s. l ≠ StringL s)
    ⇒
    emitted_insts st st' = [] ∧
    same_blocks st st'
Proof
  (* TODO: update proof for lower_value wrapper *)
  cheat
QED

(* --- Name (local variable load) --- *)
(* Phase 1: v must be a primitive (word-sized) value,
   and offset must fit in a word (offset < dimword(:256)).
   Uses typed_val_to_w256 (not val_to_w256) to avoid BytesV address heuristic.
   The type_value tv from the scope correctly distinguishes address from bytesN. *)
Theorem compile_name_correct:
  ∀ cenv cx ty id es ss st op st' v tv es' offset size.
    state_rel cenv cx es ss ∧
    eval_expr cx (Name _ id) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Name _ id) st = (op, st') ∧
    FLOOKUP cenv.ce_vars id = SOME (MemLoc offset size) ∧
    offset < dimword (:256) ∧
    (* Type-value from scope for correct encoding.
       tv must be a base type_value (word-sized, not array/struct/tuple). *)
    lookup_scopes (string_to_num id) es.scopes = SOME (tv, v) ∧
    (∃ bt. tv = BaseTV bt ∧ is_word_type (BaseT bt))
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (typed_val_to_w256 tv v) ∧
      es' = es ∧
      same_blocks st st'
Proof
  cheat
QED

(* --- BinOp (safe arithmetic) --- *)
(* For compile_binop: the emitted instructions compute the correct
   result and any overflow checks correctly abort on invalid inputs *)
Theorem compile_binop_correct:
  ∀ cenv cx ty bop e1 e2 es ss st v es'.
    state_rel cenv cx es ss ∧
    eval_expr cx (Builtin _ (Bop bop) [e1; e2]) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Builtin _ (Bop bop) [e1; e2]) st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- Not (boolean negation) --- *)
(* The ISZERO instruction correctly computes boolean NOT.
   Sub-expression correctness is handled by the main induction. *)
Theorem iszero_bool_correct:
  ∀ op b ss inst_id out_var.
    eval_operand op ss = SOME (val_to_w256 (BoolV b)) ⇒
    step_inst_base (mk_inst inst_id ISZERO [op] [out_var]) ss =
      OK (update_var out_var (val_to_w256 (BoolV (¬b))) ss)
Proof
  Cases_on `b`
  >> simp[step_inst_base_def, exec_pure1_def, eval_operand_def,
          val_to_w256_def, update_var_def, venomInstTheory.mk_inst_def,
          venomExecSemanticsTheory.bool_to_word_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* ASSERT instruction: non-zero → OK (no-op), zero → Abort *)
Theorem assert_true_correct:
  ∀ op v ss inst_id.
    eval_operand op ss = SOME v ∧ v ≠ 0w ⇒
    step_inst_base (mk_inst inst_id ASSERT [op] []) ss = OK ss
Proof
  simp[step_inst_base_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

Theorem assert_false_correct:
  ∀ op ss inst_id.
    eval_operand op ss = SOME 0w ⇒
    step_inst_base (mk_inst inst_id ASSERT [op] []) ss =
      Abort Revert_abort (revert_state (set_returndata [] ss))
Proof
  simp[step_inst_base_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* emit_void ASSERT: emits one ASSERT instruction *)
Theorem emit_void_assert_inst:
  ∀ op st.
    emit_void ASSERT [op] st =
      ((), st with <| cs_next_id := st.cs_next_id + 1;
                       cs_current_insts := st.cs_current_insts ++
                         [mk_inst st.cs_next_id ASSERT [op] []] |>)
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       emit_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* --- Not (boolean negation) --- compositional proof *)
(* Given sub-expression compiles correctly, compile_expr Not is correct. *)
Theorem compile_not_correct:
  ∀ cenv cx e es ss st op st' v es' b.
    state_rel cenv cx es ss ∧
    (* Vyper evaluates Not *)
    eval_expr cx (Builtin _ Not [e]) es = (INL (Value v), es') ∧
    v = BoolV (¬b) ∧
    (* compile_expr structure *)
    lower_value compile_expr cenv (BaseT BoolT) (Builtin _ Not [e]) st = (op, st') ∧
    (* Sub-expression correctness (IH) *)
    (let (sub_op, st1) = lower_value compile_expr cenv (BaseT BoolT) e st in
      st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
      ∃ ss_sub.
        run_inst_seq (emitted_insts st st1) ss = OK ss_sub ∧
        eval_operand sub_op ss_sub = SOME (val_to_w256 (BoolV b)) ∧
        state_rel cenv cx es' ss_sub)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- Neg (unary negation with overflow check) --- *)
Theorem compile_neg_correct:
  ∀ cenv cx ty e es ss st v es'.
    state_rel cenv cx es ss ∧
    eval_expr cx (Builtin _ Neg [e]) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Builtin _ Neg [e]) st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- Environment variables (CALLER, TIMESTAMP, etc.) --- *)
(* Helper: for simple env vars (single opcode, no args),
   the emitted instruction is a single read0 that matches the Vyper value *)
Theorem compile_env_var_correct:
  ∀ cenv cx ty item es ss st v es'.
    state_rel cenv cx es ss ∧
    eval_expr cx (Builtin _ (Env item) []) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Builtin _ (Env item) []) st = (op, st') ∧
    item ≠ PrevHash
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      es' = es ∧
      same_blocks st st'
Proof
  cheat
QED

(* ===== Structural Properties ===== *)

(* compile_expr preserves external-facing state components.
   Memory MAY be modified (keccak256, struct literals, mapping access, etc.
   all emit MSTORE/ALLOCA). Only call/tx/block context and accounts are
   guaranteed unchanged. *)
Theorem compile_expr_preserves_contexts:
  ∀ cenv ty e st op st' ss ss'.
    lower_value compile_expr cenv ty e st = (op, st') ∧
    same_blocks st st' ∧
    run_inst_seq (emitted_insts st st') ss = OK ss'
    ⇒
    ss'.vs_call_ctx = ss.vs_call_ctx ∧
    ss'.vs_tx_ctx = ss.vs_tx_ctx ∧
    ss'.vs_block_ctx = ss.vs_block_ctx ∧
    ss'.vs_accounts = ss.vs_accounts
Proof
  cheat
QED

(* Emitted instructions extend the current block.
   This is a prefix property of the compile monad:
   every operation only appends to cs_current_insts. *)
Theorem compile_expr_extends_insts:
  ∀ cenv ty e st op st'.
    lower_value compile_expr cenv ty e st = (op, st') ∧
    same_blocks st st'
    ⇒
    st'.cs_current_insts =
      st.cs_current_insts ++ emitted_insts st st'
Proof
  cheat
QED
