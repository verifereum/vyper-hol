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
  vyperAST

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

(* well_annotated: annotation types in the AST agree with operand types
   where the evaluator uses them for bounds checking.
   - BoolV Not: evaluator ignores annotation, compiler dispatches on expr_type
   - IntV Not: evaluator uses type_to_int_bound ann for bounds
   - Neg: evaluator uses type_to_int_bound ann for bounds
   - BinOp: evaluator uses type_to_int_bound ann for arithmetic bounds;
     for comparisons type_to_int_bound ann = NONE (vacuously true). *)
Definition well_annotated_def:
  well_annotated (Literal ann l) = T ∧
  well_annotated (Name ann id) = T ∧
  well_annotated (Builtin ann (Env item) args) = T ∧
  well_annotated (Builtin ann Not (e::rest)) =
    ((expr_type e ≠ BaseT BoolT ⇒
      type_to_int_bound ann = type_to_int_bound (expr_type e)) ∧
     well_annotated e) ∧
  well_annotated (Builtin ann Neg (e::rest)) =
    (type_to_int_bound ann = type_to_int_bound (expr_type e) ∧
     well_annotated e) ∧
  well_annotated (Builtin ann (Bop bop) (e1::e2::rest)) =
    ((∀u. type_to_int_bound ann = SOME u ⇒
          type_to_int_bound (expr_type e1) = SOME u) ∧
     well_annotated e1 ∧ well_annotated e2) ∧
  well_annotated _ = T
End

Theorem compile_expr_correct:
  ∀ cenv cx ty e es ss st op st' v es'.
    state_rel cenv cx es ss ∧
    fresh_vars_wrt st ss ∧
    supported_expr e ∧
    well_annotated e ∧
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

(* Chain run_inst_seq across two instruction-emitting steps.
   Also produces the accumulated cs_current_insts fact for further chaining.
   Replaces the manual emitted_insts_append + run_inst_seq_append pattern. *)
Theorem run_inst_seq_chain:
  ∀ st st1 st' ss ss1.
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st'.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st' ∧
    run_inst_seq (emitted_insts st st1) ss = OK ss1
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      run_inst_seq (emitted_insts st1 st') ss1 ∧
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rw[]
  >- (`emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
        by (irule emitted_insts_append >> gvs[]) >>
      gvs[] >> irule run_inst_seq_append >> gvs[])
  >> `emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
       by (irule emitted_insts_append >> gvs[]) >>
     gvs[]
QED

(* Error version of run_inst_seq_chain: if prefix errors, total also errors.
   Also produces the accumulated cs_current_insts fact. *)
Theorem run_inst_seq_chain_err:
  ∀ st st1 st' ss.
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st'.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st' ∧
    (∀s. run_inst_seq (emitted_insts st st1) ss ≠ OK s)
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      run_inst_seq (emitted_insts st st1) ss ∧
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rw[]
  >- (`emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
        by (irule emitted_insts_append >> gvs[]) >>
      gvs[] >> irule run_inst_seq_append_err >> gvs[])
  >> `emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
       by (irule emitted_insts_append >> gvs[]) >>
     gvs[]
QED

(* ===== Utility Lemmas (local, avoid emitHelperProps dependency) ===== *)

(* eval_operand for a Var just written by update_var *)
Theorem eval_operand_update_var_local:
  !x w ss. eval_operand (Var x) (update_var x w ss) = SOME w
Proof
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* eval_operand for a Lit is always SOME *)
Theorem eval_operand_lit_local:
  !w ss. eval_operand (Lit w) ss = SOME w
Proof
  simp[eval_operand_def]
QED

(* state_rel is preserved by update_var (only changes vs_vars) *)
Theorem state_rel_update_var_local:
  !cenv cx es ss name w.
    state_rel cenv cx es ss ==> state_rel cenv cx es (update_var name w ss)
Proof
  rw[state_rel_def, update_var_def, vars_rel_def, storage_rel_def,
     transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
     contract_storage_def, contract_transient_def]
QED

(* step_inst_base for MLOAD: reads 32 bytes from memory *)
Theorem step_MLOAD_local:
  !op1 out id ss v.
    eval_operand op1 ss = SOME v ==>
    step_inst_base (mk_inst id MLOAD [op1] [out]) ss =
      OK (update_var out (mload (w2n v) ss) ss)
Proof
  rw[step_inst_base_def, venomInstTheory.mk_inst_def,
     comp_return_def, comp_bind_def, comp_ignore_bind_def,
     mload_def, update_var_def, LET_THM, exec_read1_def]
QED

(* eval_operand preserved by update_var on a different variable *)
Theorem eval_operand_update_other_local:
  !op ss name w v.
    eval_operand op ss = SOME v /\
    (!x. op = Var x ==> x <> name) ==>
    eval_operand op (update_var name w ss) = SOME v
Proof
  Cases_on `op` >>
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
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
  rpt gen_tac >> strip_tac >>
  Cases_on `l`
  >- (Cases_on `b` >>
      gvs[compile_literal_vv_def, comp_return_def,
          emitted_insts_def, same_blocks_def, listTheory.DROP_LENGTH_NIL])
  >- gvs[]
  >- (res_tac >>
      gvs[compile_literal_vv_def, comp_return_def,
          emitted_insts_def, same_blocks_def, listTheory.DROP_LENGTH_NIL])
  >- gvs[compile_literal_vv_def, comp_return_def,
         emitted_insts_def, same_blocks_def, listTheory.DROP_LENGTH_NIL]
  >> gvs[compile_literal_vv_def, comp_return_def,
         emitted_insts_def, same_blocks_def, listTheory.DROP_LENGTH_NIL]
QED

(* --- Name (local variable load) --- *)
(* Phase 1: v must be a primitive (word-sized) value,
   and offset must fit in a word (offset < dimword(:256)).
   Uses typed_val_to_w256 (not val_to_w256) to avoid BytesV address heuristic.
   The type_value tv from the scope correctly distinguishes address from bytesN. *)
(* NOTE: original statement was FALSE for v = NoneV.
   val_in_memory (BaseTV (UintT n)) NoneV offset mem = T (vacuously true)
   but mload offset ss is unconstrained, while typed_val_to_w256 NoneV = 0w.
   Fix: added v ≠ NoneV. *)
Theorem compile_name_correct:
  ∀ cenv cx ty ann id es ss st op st' v es' offset size entry.
    state_rel cenv cx es ss ∧
    eval_expr cx (Name ann id) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Name ann id) st = (op, st') ∧
    FLOOKUP cenv.ce_vars id = SOME (MemLoc offset size) ∧
    offset < dimword (:256) ∧
    lookup_scopes (string_to_num id) es.scopes = SOME entry ∧
    entry.value = v ∧
    v ≠ NoneV ∧
    (∃ bt. entry.type = BaseTV bt ∧ is_word_type (BaseT bt))
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (typed_val_to_w256 entry.type v) ∧
      es' = es ∧
      same_blocks st st'
Proof
  cheat
QED

(* --- BinOp (safe arithmetic) --- *)
(* For compile_binop: the emitted instructions compute the correct
   result and any overflow checks correctly abort on invalid inputs *)
(* NOTE: original statement was FALSE when annotation type has different
   bounds than expr_type e1. Evaluator uses type_to_int_bound ann for
   bounds checking, compiler uses type_bounds(expr_type e1).
   Fix: added type consistency + fresh_vars_wrt + named annotation. *)
Theorem compile_binop_correct:
  ∀ cenv cx ty ann bop e1 e2 es ss st op st' v es'.
    state_rel cenv cx es ss ∧
    fresh_vars_wrt st ss ∧
    (∀u. type_to_int_bound ann = SOME u ⇒
         type_to_int_bound (expr_type e1) = SOME u) ∧
    eval_expr cx (Builtin ann (Bop bop) [e1; e2]) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1; e2]) st = (op, st')
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

(* compile_expr ignores the ty parameter for all supported_expr forms.
   This is because compile_expr uses expr_type e internally, not the passed ty.
   Generalizes the former compile_expr_ty_indep_Not. *)
Theorem compile_expr_ty_indep:
  ∀ e cenv ty1 ty2 st.
    supported_expr e ⇒
    compile_expr cenv ty1 e st = compile_expr cenv ty2 e st
Proof
  Induct_on `e` >> simp[supported_expr_def] >>
  rpt strip_tac >>
  once_rewrite_tac [cj 1 compile_expr_def] >> simp[] >>
  Cases_on `b` >> gvs[supported_expr_def] >>
  once_rewrite_tac [cj 2 compile_expr_def] >> simp[]
QED

Theorem lower_value_ty_indep:
  ∀ e cenv ty1 ty2 st.
    supported_expr e ⇒
    lower_value compile_expr cenv ty1 e st =
    lower_value compile_expr cenv ty2 e st
Proof
  rpt strip_tac >>
  simp[lower_value_def, comp_bind_def, pairTheory.UNCURRY] >>
  `compile_expr cenv ty1 e st = compile_expr cenv ty2 e st`
    by metis_tac[compile_expr_ty_indep] >>
  simp[]
QED

(* --- Not (boolean negation) --- compositional proof *)
(* Given sub-expression compiles correctly, compile_expr Not is correct. *)
(* NOTE: original statement was FALSE without expr_type constraint.
   When expr_type e ≠ BaseT BoolT, compiler emits NOT (bitwise complement)
   instead of ISZERO. Counterexample: NOT 1w = 0xFFF..FEw ≠ 0w.
   Fix: added hypothesis "expr_type e = BaseT BoolT". *)
Theorem compile_not_correct:
  ∀ cenv cx ann e es ss st op st' v es' b.
    state_rel cenv cx es ss ∧
    eval_expr cx (Builtin ann Not [e]) es = (INL (Value v), es') ∧
    v = BoolV (¬b) ∧
    expr_type e = BaseT BoolT ∧
    lower_value compile_expr cenv (BaseT BoolT) (Builtin ann Not [e]) st = (op, st') ∧
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

(* NOTE: original statement was FALSE when annotation type has different
   bounds than expr_type e. Compiler uses type_bounds(expr_type e) but
   evaluator uses type_to_int_bound(annotation type).
   Fix: named annotation, added type_to_int_bound constraint. *)
Theorem compile_neg_correct:
  ∀ cenv cx ty ann e es ss st op st' v es'.
    state_rel cenv cx es ss ∧
    eval_expr cx (Builtin ann Neg [e]) es = (INL (Value v), es') ∧
    type_to_int_bound ann = type_to_int_bound (expr_type e) ∧
    lower_value compile_expr cenv ty (Builtin ann Neg [e]) st = (op, st')
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
  ∀ cenv cx ty ann item es ss st op st' v es'.
    state_rel cenv cx es ss ∧
    eval_expr cx (Builtin ann (Env item) []) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Builtin ann (Env item) []) st = (op, st') ∧
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

(* ===== Prefix / same_blocks Infrastructure ===== *)

(* isPREFIX ↔ append-DROP identity *)
Theorem prefix_drop_equiv:
  !xs (l:'a list). isPREFIX xs l <=> (l = xs ++ DROP (LENGTH xs) l)
Proof
  rw[rich_listTheory.IS_PREFIX_APPEND, EQ_IMP_THM]
  >- simp[rich_listTheory.DROP_LENGTH_APPEND]
  >> qexists_tac `DROP (LENGTH xs) l` >> simp[]
QED

(* same_blocks: reflexive, symmetric, transitive *)
Theorem same_blocks_refl:
  same_blocks st st
Proof
  simp[same_blocks_def]
QED

Theorem same_blocks_trans:
  same_blocks st st1 /\ same_blocks st1 st2 ==> same_blocks st st2
Proof
  simp[same_blocks_def]
QED

(* emit_op / emit_void / emit_inst: prefix + same_blocks *)
Theorem emit_op_prefix:
  !opc ops st v st'.
    emit_op opc ops st = (v, st') ==>
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem emit_op_same_blocks:
  !opc ops st v st'.
    emit_op opc ops st = (v, st') ==> same_blocks st st'
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def] >>
  simp[same_blocks_def]
QED

Theorem emit_void_prefix:
  !opc ops st v st'.
    emit_void opc ops st = (v, st') ==>
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem emit_void_same_blocks:
  !opc ops st v st'.
    emit_void opc ops st = (v, st') ==> same_blocks st st'
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def] >>
  simp[same_blocks_def]
QED

(* compile_ptr_load: all cases are emit_op *)
Theorem compile_ptr_load_prefix:
  !is_ctor loc op st v st'.
    compile_ptr_load is_ctor loc op st = (v, st') ==>
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  Cases_on `loc` >>
  simp[contextTheory.compile_ptr_load_def] >>
  rw[] >> imp_res_tac emit_op_prefix
QED

Theorem compile_ptr_load_same_blocks:
  !is_ctor loc op st v st'.
    compile_ptr_load is_ctor loc op st = (v, st') ==>
    same_blocks st st'
Proof
  Cases_on `loc` >>
  simp[contextTheory.compile_ptr_load_def] >>
  rw[] >> imp_res_tac emit_op_same_blocks
QED

(* new_block: always breaks same_blocks *)
Theorem new_block_breaks_same_blocks:
  ~same_blocks st (SND (new_block label st))
Proof
  simp[new_block_def, same_blocks_def, LET_THM]
QED

(* run_inst_seq nil *)
Theorem run_inst_seq_nil:
  run_inst_seq [] ss = OK ss
Proof
  simp[run_inst_seq_def]
QED

(* emitted_insts reflexive *)
Theorem emitted_insts_refl:
  emitted_insts st st = []
Proof
  simp[emitted_insts_def]
QED

(* ===== isPREFIX Composition Toolkit ===== *)

(* Monad composition preserves isPREFIX on cs_current_insts *)
Theorem comp_bind_isPREFIX:
  !(mf : compile_state -> 'a # compile_state)
   (mg : 'a -> compile_state -> 'b # compile_state) s0 bval s2.
    comp_bind mf mg s0 = (bval, s2) /\
    (!sa av sb. mf sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts) /\
    (!av sa bv sb. mg av sa = (bv, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts)
    ==>
    isPREFIX s0.cs_current_insts s2.cs_current_insts
Proof
  rw[comp_bind_def, pairTheory.UNCURRY] >>
  `?av s1. mf s0 = (av, s1)` by metis_tac[pairTheory.PAIR] >>
  gvs[] >>
  irule rich_listTheory.IS_PREFIX_TRANS >>
  qexists_tac `s1.cs_current_insts` >>
  metis_tac[]
QED

Theorem comp_ignore_bind_isPREFIX:
  !(mf : compile_state -> 'a # compile_state)
   (mg : compile_state -> 'b # compile_state) s0 bval s2.
    comp_ignore_bind mf mg s0 = (bval, s2) /\
    (!sa av sb. mf sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts) /\
    (!sa bv sb. mg sa = (bv, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts)
    ==>
    isPREFIX s0.cs_current_insts s2.cs_current_insts
Proof
  rw[comp_ignore_bind_def, comp_bind_def, pairTheory.UNCURRY] >>
  `?av s1. mf s0 = (av, s1)` by metis_tac[pairTheory.PAIR] >>
  gvs[] >>
  irule rich_listTheory.IS_PREFIX_TRANS >>
  qexists_tac `s1.cs_current_insts` >>
  metis_tac[]
QED

(* Primitive isPREFIX lemmas *)
Theorem comp_return_isPREFIX[local]:
  !x sa av sb. comp_return x sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[comp_return_def]
QED

Theorem emit_isPREFIX[local]:
  !inst sa av sb. emit inst sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[emit_def] >> simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem fresh_var_ci_eq[local]:
  !sa av sb. fresh_var sa = (av, sb) ==> sa.cs_current_insts = sb.cs_current_insts
Proof
  rw[fresh_var_def] >> simp[]
QED

Theorem fresh_id_ci_eq[local]:
  !sa av sb. fresh_id sa = (av, sb) ==> sa.cs_current_insts = sb.cs_current_insts
Proof
  rw[fresh_id_def] >> simp[]
QED

Theorem fresh_label_ci_eq[local]:
  !pfx sa av sb. fresh_label pfx sa = (av, sb) ==> sa.cs_current_insts = sb.cs_current_insts
Proof
  rw[fresh_label_def] >> simp[]
QED

Theorem emit_op_isPREFIX[local]:
  !opc ops sa av sb. emit_op opc ops sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def, pairTheory.UNCURRY] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem emit_void_isPREFIX[local]:
  !opc ops sa av sb. emit_void opc ops sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def, pairTheory.UNCURRY] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem emit_inst_isPREFIX[local]:
  !opc ops outs sa av sb. emit_inst opc ops outs sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def, pairTheory.UNCURRY] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

(* new_block changes cs_blocks (needed for vacuous cases) *)
Theorem new_block_changes_blocks[local]:
  !label st. (SND (new_block label st)).cs_blocks <> st.cs_blocks
Proof
  rw[new_block_def, LET_THM]
QED

(* ===== ci_mono: Compile monad monotonicity ===== *)

(* ci_mono st st' holds when the compile state transition from st to st'
   either (1) appends to cs_current_insts without changing cs_blocks, or
   (2) cs_blocks grew (meaning new_block was called, which resets ci).
   This is the key invariant for all compile monad operations. *)
Definition ci_mono_def:
  ci_mono (st:compile_state) (st':compile_state) ⇔
    (isPREFIX st.cs_current_insts st'.cs_current_insts ∧
     st'.cs_blocks = st.cs_blocks) ∨
    LENGTH st'.cs_blocks > LENGTH st.cs_blocks
End

Theorem ci_mono_refl[local]:
  ci_mono st st
Proof
  simp[ci_mono_def]
QED

Theorem ci_mono_trans[local]:
  ci_mono a b ∧ ci_mono b c ⇒ ci_mono a c
Proof
  simp[ci_mono_def] >> rpt strip_tac >> gvs[] >>
  irule rich_listTheory.IS_PREFIX_TRANS >>
  qexists `b.cs_current_insts` >> simp[]
QED

(* ci_mono composes through monad_bind (= comp_bind) *)
Theorem ci_mono_bind[local]:
  ∀ (mf : compile_state -> 'a # compile_state)
    (mg : 'a -> compile_state -> 'b # compile_state) s0.
    (∀ sa. ci_mono sa (SND (mf sa))) ∧
    (∀ av sa. ci_mono sa (SND (mg av sa)))
    ⇒
    ci_mono s0 (SND (comp_bind mf mg s0))
Proof
  rw[comp_bind_def, pairTheory.UNCURRY] >>
  Cases_on `mf s0` >> gvs[] >>
  irule ci_mono_trans >>
  qexists `r` >> conj_tac
  >- (first_x_assum (qspec_then `s0` mp_tac) >> simp[])
  >> first_x_assum (qspecl_then [`q`, `r`] mp_tac) >> simp[]
QED

(* ci_mono composes through comp_ignore_bind *)
Theorem ci_mono_ignore_bind[local]:
  ∀ (mf : compile_state -> 'a # compile_state)
    (mg : compile_state -> 'b # compile_state) s0.
    (∀ sa. ci_mono sa (SND (mf sa))) ∧
    (∀ sa. ci_mono sa (SND (mg sa)))
    ⇒
    ci_mono s0 (SND (comp_ignore_bind mf mg s0))
Proof
  rw[comp_ignore_bind_def, comp_bind_def, pairTheory.UNCURRY] >>
  Cases_on `mf s0` >> gvs[] >>
  irule ci_mono_trans >>
  qexists `r` >> conj_tac
  >- (qpat_x_assum `!sa. ci_mono sa (SND (mf sa))` (qspec_then `s0` mp_tac) >> simp[])
  >> qpat_x_assum `!sa. ci_mono sa (SND (mg sa))` (qspec_then `r` mp_tac) >> simp[]
QED

(* ci_mono + same_blocks → isPREFIX *)
Theorem ci_mono_same_blocks_isPREFIX[local]:
  ci_mono st st' ∧ same_blocks st st' ⇒
  isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rw[ci_mono_def, same_blocks_def] >> gvs[]
QED

(* ci_mono for primitives *)
Theorem ci_mono_comp_return[local]:
  ∀ x sa. ci_mono sa (SND (comp_return x sa))
Proof
  simp[comp_return_def, ci_mono_def]
QED

Theorem ci_mono_emit[local]:
  ∀ inst sa. ci_mono sa (SND (emit inst sa))
Proof
  simp[emit_def, ci_mono_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem ci_mono_fresh_var[local]:
  ∀ sa. ci_mono sa (SND (fresh_var sa))
Proof
  simp[fresh_var_def, ci_mono_def]
QED

Theorem ci_mono_fresh_id[local]:
  ∀ sa. ci_mono sa (SND (fresh_id sa))
Proof
  simp[fresh_id_def, ci_mono_def]
QED

Theorem ci_mono_fresh_label[local]:
  ∀ pfx sa. ci_mono sa (SND (fresh_label pfx sa))
Proof
  simp[fresh_label_def, ci_mono_def]
QED

Theorem ci_mono_new_block[local]:
  ∀ label sa. ci_mono sa (SND (new_block label sa))
Proof
  simp[new_block_def, LET_THM, ci_mono_def]
QED

Theorem ci_mono_emit_op[local]:
  ∀ opc ops sa. ci_mono sa (SND (emit_op opc ops sa))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def,
       venomInstTheory.mk_inst_def, pairTheory.UNCURRY,
       ci_mono_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem ci_mono_emit_void[local]:
  ∀ opc ops sa. ci_mono sa (SND (emit_void opc ops sa))
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def,
       venomInstTheory.mk_inst_def, pairTheory.UNCURRY,
       ci_mono_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem ci_mono_emit_inst[local]:
  ∀ opc ops outs sa. ci_mono sa (SND (emit_inst opc ops outs sa))
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def,
       venomInstTheory.mk_inst_def, pairTheory.UNCURRY,
       ci_mono_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

(* ci_mono for compile_ptr_load (used by unwrap_value) *)
Theorem ci_mono_compile_ptr_load[local]:
  ∀ is_ctor loc op sa. ci_mono sa (SND (compile_ptr_load is_ctor loc op sa))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[contextTheory.compile_ptr_load_def] >>
  rw[] >> simp[ci_mono_emit_op]
QED

(* ===== blocks_len toolkit for ci_mono proofs ===== *)

(* LENGTH cs_blocks is preserved by all primitives except new_block *)
Theorem blocks_len_bind[local]:
  ∀ (m : compile_state -> 'a # compile_state)
    (g : 'a -> compile_state -> 'b # compile_state) sa.
    LENGTH (SND (monad_bind m g sa)).cs_blocks =
    LENGTH (SND (g (FST (m sa)) (SND (m sa)))).cs_blocks
Proof
  rw[comp_bind_def, LET_THM, pairTheory.UNCURRY]
QED

Theorem blocks_pres_emit_op[local]:
  ∀ opc ops sa.
    LENGTH (SND (emit_op opc ops sa)).cs_blocks = LENGTH sa.cs_blocks
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, LET_THM,
     pairTheory.UNCURRY, fresh_id_def, fresh_var_def, emit_def,
     venomInstTheory.mk_inst_def, comp_return_def]
QED

Theorem blocks_pres_emit_void[local]:
  ∀ opc ops sa.
    LENGTH (SND (emit_void opc ops sa)).cs_blocks = LENGTH sa.cs_blocks
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, LET_THM,
     pairTheory.UNCURRY, fresh_id_def, emit_def,
     venomInstTheory.mk_inst_def, comp_return_def]
QED

Theorem blocks_pres_emit_inst[local]:
  ∀ opc ops outs sa.
    LENGTH (SND (emit_inst opc ops outs sa)).cs_blocks = LENGTH sa.cs_blocks
Proof
  rw[emit_inst_def, comp_bind_def, comp_ignore_bind_def, LET_THM,
     pairTheory.UNCURRY, fresh_id_def, emit_def,
     venomInstTheory.mk_inst_def, comp_return_def]
QED

Theorem blocks_pres_compile_ptr_load[local]:
  ∀ ic loc op sa.
    LENGTH (SND (compile_ptr_load ic loc op sa)).cs_blocks =
    LENGTH sa.cs_blocks
Proof
  rpt gen_tac >> Cases_on `loc` >>
  rw[contextTheory.compile_ptr_load_def] >>
  rw[blocks_pres_emit_op]
QED

Theorem blocks_pres_compile_ptr_store[local]:
  ∀ ic loc op v sa.
    LENGTH (SND (compile_ptr_store ic loc op v sa)).cs_blocks =
    LENGTH sa.cs_blocks
Proof
  rpt gen_tac >> Cases_on `loc` >>
  rw[contextTheory.compile_ptr_store_def] >>
  rw[blocks_pres_emit_void]
QED

(* compile_word_copy_loop grows blocks by exactly 3 *)
val blocks_len_rws = [blocks_len_bind,
  SIMP_RULE bool_ss [] (Q.SPECL [`i`,`sa`] (INST_TYPE [alpha |-> ``:unit``] blocks_pres_emit_op)),
  blocks_pres_emit_op, blocks_pres_emit_void, blocks_pres_emit_inst,
  blocks_pres_compile_ptr_load, blocks_pres_compile_ptr_store,
  SIMP_RULE bool_ss [LET_THM] fresh_var_def,
  SIMP_RULE bool_ss [LET_THM] fresh_id_def,
  SIMP_RULE bool_ss [LET_THM] fresh_label_def,
  SIMP_RULE bool_ss [] emit_def,
  SIMP_RULE bool_ss [LET_THM] new_block_def,
  comp_return_def];

Theorem blocks_grow_compile_word_copy_loop[local]:
  ∀ src dst wc ll sl ic sa.
    LENGTH sa.cs_blocks + 3 =
    LENGTH (SND (compile_word_copy_loop src dst wc ll sl ic sa)).cs_blocks
Proof
  rw[contextTheory.compile_word_copy_loop_def, LET_THM] >>
  simp (blocks_len_rws @ [comp_bind_def, pairTheory.UNCURRY,
        comp_ignore_bind_def]) >>
  rw[] >> simp blocks_len_rws
QED

(* ci_mono for compile_word_copy_loop *)
Theorem ci_mono_compile_word_copy_loop[local]:
  ∀ src dst wc ll sl ic sa.
    ci_mono sa (SND (compile_word_copy_loop src dst wc ll sl ic sa))
Proof
  rw[ci_mono_def] >> disj2_tac >>
  `LENGTH sa.cs_blocks + 3 =
   LENGTH (SND (compile_word_copy_loop src dst wc ll sl ic sa)).cs_blocks`
    by rw[blocks_grow_compile_word_copy_loop] >>
  simp[]
QED

(* ci_mono for compile_alloc_buffer *)
Theorem ci_mono_compile_alloc_buffer[local]:
  ∀ size sa. ci_mono sa (SND (compile_alloc_buffer size sa))
Proof
  rw[contextTheory.compile_alloc_buffer_def,
     comp_bind_def, comp_return_def, LET_THM, pairTheory.UNCURRY] >>
  simp[ci_mono_emit_op]
QED

(* ci_mono for storage/transient/code_to_memory *)
Theorem ci_mono_compile_storage_to_memory[local]:
  ∀ slot buf wc sa.
    ci_mono sa (SND (compile_storage_to_memory slot buf wc sa))
Proof
  rw[contextTheory.compile_storage_to_memory_def,
     ci_mono_compile_word_copy_loop]
QED

Theorem ci_mono_compile_transient_to_memory[local]:
  ∀ slot buf wc sa.
    ci_mono sa (SND (compile_transient_to_memory slot buf wc sa))
Proof
  rw[contextTheory.compile_transient_to_memory_def,
     ci_mono_compile_word_copy_loop]
QED

Theorem ci_mono_compile_code_to_memory[local]:
  ∀ off dst wc sa.
    ci_mono sa (SND (compile_code_to_memory off dst wc sa))
Proof
  rw[contextTheory.compile_code_to_memory_def] >>
  rw[ci_mono_def]
  >- simp[comp_return_def]
  >> disj2_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, pairTheory.UNCURRY, LET_THM,
       comp_return_def] >>
  `LENGTH sa.cs_blocks + 3 =
   LENGTH (SND (compile_word_copy_loop off dst wc LocCode LocMemory F sa)).cs_blocks`
    by rw[blocks_grow_compile_word_copy_loop] >>
  simp[]
QED

(* ci_mono for compile_ensure_in_memory:
   Storage/Transient → blocks grow via compile_word_copy_loop (always)
   Code → blocks grow when word_count > 0, isPREFIX when word_count = 0
   Calldata → blocks preserved, isPREFIX via emit chain
   Memory → trivial via comp_return *)

(* Shared tactic abbreviation for blocks-grew cases *)
val blocks_grew_tac =
  simp[ci_mono_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, pairTheory.UNCURRY] >> disj2_tac;

val blocks_grew_rws =
  [contextTheory.compile_alloc_buffer_def,
   comp_bind_def, comp_ignore_bind_def, comp_return_def,
   pairTheory.UNCURRY, LET_THM,
   GSYM blocks_grow_compile_word_copy_loop,
   blocks_pres_emit_op];

(* Shared tactic for isPREFIX cases *)
val isPREFIX_prim_rws =
  [contextTheory.compile_alloc_buffer_def,
   emit_op_def, emit_void_def, comp_bind_def,
   comp_ignore_bind_def, comp_return_def,
   fresh_id_def, fresh_var_def, emit_def,
   venomInstTheory.mk_inst_def, pairTheory.UNCURRY, LET_THM];

Theorem ci_mono_compile_ensure_in_memory[local]:
  ∀ ptr_op loc mem_bytes word_count is_ctor sa.
    ci_mono sa
      (SND (compile_ensure_in_memory ptr_op loc mem_bytes word_count is_ctor sa))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[contextTheory.compile_ensure_in_memory_def, LET_THM]
  (* LocMemory *)
  >- simp[comp_return_def, ci_mono_def]
  (* LocStorage: blocks grow *)
  >- (blocks_grew_tac >>
      simp (contextTheory.compile_storage_to_memory_def :: blocks_grew_rws))
  (* LocTransient: blocks grow *)
  >- (blocks_grew_tac >>
      simp (contextTheory.compile_transient_to_memory_def :: blocks_grew_rws))
  (* LocCode: case split on word_count *)
  >- (simp[ci_mono_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, pairTheory.UNCURRY] >>
      Cases_on `word_count = 0`
      >- (disj1_tac >>
          simp (contextTheory.compile_code_to_memory_def :: isPREFIX_prim_rws) >>
          rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
          simp[rich_listTheory.IS_PREFIX_APPEND3])
      >> disj2_tac >>
      simp (contextTheory.compile_code_to_memory_def :: blocks_grew_rws))
  (* LocCalldata: pure emit chain — isPREFIX *)
  >> simp[ci_mono_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, pairTheory.UNCURRY] >>
  disj1_tac >>
  simp isPREFIX_prim_rws >>
  rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

(* ci_mono for unwrap_value *)
Theorem ci_mono_unwrap_value[local]:
  ∀ cenv vv sa. ci_mono sa (SND (unwrap_value cenv vv sa))
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[unwrap_value_def]
  (* StackValue: comp_return *)
  >- simp[comp_return_def, ci_mono_def]
  (* LocatedValue: split on is_word_type *)
  >> rw[]
  (* word type: compile_ptr_load *)
  >- simp[ci_mono_compile_ptr_load]
  (* non-word type: case on ptr_location *)
  >> Cases_on `p.ptr_location` >>
  simp[LET_THM]
  >- simp[comp_return_def, ci_mono_def]
  >> simp[ci_mono_compile_ensure_in_memory]
QED

(* ===== compile_expr ci_mono by induction ===== *)

Theorem compile_expr_ci_mono[local]:
  (∀ cenv ty e st. ci_mono st (SND (compile_expr cenv ty e st))) ∧
  (∀ cenv ret_ty ty bi args st.
    ci_mono st (SND (compile_builtin_dispatch cenv ret_ty ty bi args st))) ∧
  (∀ cenv vv_ty ty tb ret_ty args st.
    ci_mono st (SND (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args st)))
Proof
  cheat
QED

(* Derive: lower_value compile_expr preserves ci_mono *)
Theorem ci_mono_lower_value_compile_expr[local]:
  ∀ cenv ty e st.
    ci_mono st (SND (lower_value compile_expr cenv ty e st))
Proof
  rw[lower_value_def] >>
  irule ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> simp[ci_mono_unwrap_value])
  >> simp[cj 1 compile_expr_ci_mono]
QED

(* ===== run_inst_seq preserves venom_state fields ===== *)

(* Generic: if every instruction in a list preserves some projection,
   then run_inst_seq preserves it *)
Theorem run_inst_seq_preserves_field:
  !(proj : venom_state -> 'a) is ss ss'.
    run_inst_seq is ss = OK ss' /\
    (!i ss1 ss2. MEM i is /\ step_inst_base i ss1 = OK ss2 ==> proj ss2 = proj ss1)
    ==>
    proj ss' = proj ss
Proof
  gen_tac >> Induct_on `is`
  >- simp[run_inst_seq_def]
  >> rpt gen_tac >> strip_tac >>
  gvs[run_inst_seq_def] >>
  Cases_on `step_inst_base h ss` >> gvs[] >>
  `proj v = proj ss` by
    (first_x_assum (qspecl_then [`h`, `ss`, `v`] mp_tac) >> simp[]) >>
  `proj ss' = proj v` by
    (first_x_assum (qspecl_then [`v`, `ss'`] mp_tac) >> simp[] >>
     disch_then irule >>
     rpt strip_tac >>
     first_x_assum (qspecl_then [`i`, `ss1`, `ss2`] mp_tac) >> simp[]) >>
  simp[]
QED

(* ===== Structural Properties ===== *)

(* compile_expr preserves external-facing state components.
   Memory MAY be modified (keccak256, struct literals, mapping access, etc.
   all emit MSTORE/ALLOCA). Only call/tx/block context and accounts are
   guaranteed unchanged. *)
(* NOTE: original statement was FALSE: vs_accounts is modified by CALL/SEND
   which compile_expr can emit for non-supported expressions.
   Fix: restrict to supported_expr + drop vs_accounts.
   For supported_expr, all emitted opcodes are pure/MLOAD — they preserve contexts. *)
Theorem compile_expr_preserves_contexts:
  ∀ cenv ty e st op st' ss ss'.
    lower_value compile_expr cenv ty e st = (op, st') ∧
    supported_expr e ∧
    same_blocks st st' ∧
    run_inst_seq (emitted_insts st st') ss = OK ss'
    ⇒
    ss'.vs_call_ctx = ss.vs_call_ctx ∧
    ss'.vs_tx_ctx = ss.vs_tx_ctx ∧
    ss'.vs_block_ctx = ss.vs_block_ctx
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
  rpt strip_tac >>
  `ci_mono st st'` by (
    `ci_mono st (SND (lower_value compile_expr cenv ty e st))`
      by simp[ci_mono_lower_value_compile_expr] >>
    Cases_on `lower_value compile_expr cenv ty e st` >> gvs[]) >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts`
    by (irule ci_mono_same_blocks_isPREFIX >> simp[]) >>
  gvs[GSYM prefix_drop_equiv, emitted_insts_def]
QED
