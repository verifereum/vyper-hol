(*
 * Emission Helper Properties
 *
 * Reusable lemmas for proving correctness of compiled instruction sequences.
 * Every lowering proof (ABI, arithmetic, expr, stmt) uses these building blocks.
 *
 * TOP-LEVEL:
 *   exec_pure1_ok / exec_pure2_ok   — generic pure opcode execution
 *   exec_read1_ok / exec_write2_ok  — memory/storage read/write execution
 *   assert_ok / assert_revert       — ASSERT instruction outcomes
 *   eval_operand_update_var         — variable lookup after update
 *   eval_operand_update_other       — unrelated variable preserves lookup
 *   eval_operand_lit                — literal always evaluates
 *   run_inst_seq_cons_ok            — step through instruction list
 *   run_inst_seq_snoc_ok_or_abort   — common pattern: pure prefix + assert
 *   emitted_insts_emit_op           — what emit_op produces
 *   emitted_insts_emit_void         — what emit_void produces
 *   emitted_insts_chain             — composing emitted_insts through do-blocks
 *
 * Helper:
 *   fresh_var_name    — characterize fresh_var output
 *   fresh_id_val      — characterize fresh_id output
 *)

Theory emitHelperProps
Ancestors
  exprLoweringProps emitHelper compileEnv
  venomExecSemantics venomState venomInst
Libs
  intLib

(* ===== Pure Opcode Execution ===== *)

(* exec_pure1: 1-operand pure instruction succeeds when operand is defined *)
Theorem exec_pure1_ok:
  ∀ f op1 v1 id opc out ss v.
    eval_operand op1 ss = SOME v1 ∧ v = f v1 ⇒
    exec_pure1 f (mk_inst id opc [op1] [out]) ss =
      OK (update_var out v ss)
Proof
  simp[exec_pure1_def, mk_inst_def]
QED

(* exec_pure2: 2-operand pure instruction succeeds when both operands defined *)
Theorem exec_pure2_ok:
  ∀ f op1 op2 v1 v2 id opc out ss v.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ∧ v = f v1 v2 ⇒
    exec_pure2 f (mk_inst id opc [op1; op2] [out]) ss =
      OK (update_var out v ss)
Proof
  simp[exec_pure2_def, mk_inst_def]
QED

Theorem mk_inst_opcode[simp]:
  (mk_inst id op ops outs).inst_opcode = op
Proof
  rw[mk_inst_def]
QED

Theorem mk_inst_operands[simp]:
  (mk_inst id op ops outs).inst_operands = ops
Proof
  rw[mk_inst_def]
QED

Theorem mk_inst_outputs[simp]:
  (mk_inst id op ops outs).inst_outputs = outs
Proof
  rw[mk_inst_def]
QED

(* ===== Specific Pure Opcodes ===== *)
(* These combine step_inst_base dispatch with exec_pure{1,2}_ok *)

Theorem step_SIGNEXTEND:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id SIGNEXTEND [op1; op2] [out]) ss =
      OK (update_var out (sign_extend v1 v2) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem step_EQ:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id EQ [op1; op2] [out]) ss =
      OK (update_var out (bool_to_word (v1 = v2)) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem step_SHR:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id SHR [op1; op2] [out]) ss =
      OK (update_var out (word_lsr v2 (w2n v1)) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem step_SHL:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id SHL [op1; op2] [out]) ss =
      OK (update_var out (word_lsl v2 (w2n v1)) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem step_ISZERO:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    step_inst_base (mk_inst id ISZERO [op1] [out]) ss =
      OK (update_var out (bool_to_word (v1 = 0w)) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure1_ok >> rw[]
QED

Theorem step_ADD:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id ADD [op1; op2] [out]) ss =
      OK (update_var out (v1 + v2) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem step_MUL:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id MUL [op1; op2] [out]) ss =
      OK (update_var out (v1 * v2) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem step_GT:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id GT [op1; op2] [out]) ss =
      OK (update_var out (bool_to_word (w2n v1 > w2n v2)) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem step_LT:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id LT [op1; op2] [out]) ss =
      OK (update_var out (bool_to_word (w2n v1 < w2n v2)) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem step_AND:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id AND [op1; op2] [out]) ss =
      OK (update_var out (word_and v1 v2) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

(* ===== Memory Opcodes ===== *)

Theorem step_MLOAD:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    step_inst_base (mk_inst id MLOAD [op1] [out]) ss =
      OK (update_var out (mload (w2n v1) ss) ss)
Proof
  rw[step_inst_base_def, exec_read1_def]
QED

Theorem step_MSTORE:
  ∀ op1 op2 v1 v2 id ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id MSTORE [op1; op2] []) ss =
      OK (mstore (w2n v1) v2 ss)
Proof
  rw[step_inst_base_def, exec_write2_def]
QED

(* ===== ASSERT ===== *)

(* ASSERT with non-zero condition: OK, state unchanged *)
Theorem assert_ok:
  ∀ op1 v id ss.
    eval_operand op1 ss = SOME v ∧ v ≠ 0w ⇒
    step_inst_base (mk_inst id ASSERT [op1] []) ss = OK ss
Proof
  rw[step_inst_base_def]
QED

(* ASSERT with zero condition: Abort Revert *)
Theorem assert_revert:
  ∀ op1 id ss rs.
    eval_operand op1 ss = SOME 0w ∧ rs = revert_state (set_returndata [] ss) ⇒
    step_inst_base (mk_inst id ASSERT [op1] []) ss = Abort Revert_abort rs
Proof
  rw[step_inst_base_def]
QED

(* ASSERT either succeeds or reverts (disjunctive form) *)
Theorem assert_ok_or_revert:
  ∀ op1 v id ss rs.
    eval_operand op1 ss = SOME v ∧ rs = revert_state (set_returndata [] ss) ⇒
    step_inst_base (mk_inst id ASSERT [op1] []) ss = OK ss ∨
    step_inst_base (mk_inst id ASSERT [op1] []) ss = Abort Revert_abort rs
Proof
  rw[step_inst_base_def]
QED

(* ===== eval_operand after update_var ===== *)

Theorem update_var_labels[simp]:
  (update_var v w ss).vs_labels = ss.vs_labels
Proof
  rw[update_var_def]
QED

Theorem mstore_labels[simp]:
  (mstore a v s).vs_labels = s.vs_labels
Proof
  rw[mstore_def]
QED

Theorem lookup_var_update_var:
  lookup_var v2 (update_var v1 w ss) =
  if v2 = v1 then SOME w else lookup_var v2 ss
Proof
  rw[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lookup_var_mstore[simp]:
  lookup_var v (mstore a b s) = lookup_var v s
Proof
  rw[lookup_var_def, mstore_def]
QED

(* Lookup the variable just written *)
Theorem eval_operand_update_var:
  ∀ v w ss.
    eval_operand (Var v) (update_var v w ss) = SOME w
Proof
  rw[eval_operand_def, lookup_var_update_var]
QED

(* Lookup a different variable: unaffected *)
Theorem eval_operand_update_other:
  ∀ v v' w ss.
    v ≠ v' ⇒
    eval_operand (Var v) (update_var v' w ss) = eval_operand (Var v) ss
Proof
  rw[eval_operand_def, lookup_var_update_var]
QED

(* Literal is always defined, unaffected by state changes *)
Theorem eval_operand_lit:
  ∀ w ss. eval_operand (Lit w) ss = SOME w
Proof
  simp[eval_operand_def]
QED

(* Literal unaffected by update_var *)
Theorem eval_operand_lit_update:
  ∀ w v w' ss. eval_operand (Lit w) (update_var v w' ss) = SOME w
Proof
  simp[eval_operand_def]
QED

(* eval_operand preserved through update_var when operand doesn't mention v *)
Theorem eval_operand_update_var_mstore:
  ∀ op v w ss val.
    eval_operand op ss = SOME val ∧
    (∀ x. op = Var x ⇒ x ≠ v) ⇒
    eval_operand op (update_var v w ss) = SOME val
Proof
  Cases \\ rw[eval_operand_def, lookup_var_update_var]
QED

(* eval_operand preserved through mstore (memory write doesn't affect vars) *)
Theorem eval_operand_mstore:
  ∀ op addr val ss v.
    eval_operand op ss = SOME v ⇒
    eval_operand op (mstore addr val ss) = SOME v
Proof
  Cases \\ rw[eval_operand_def]
QED

(* ===== run_inst_seq building blocks ===== *)

(* Single instruction: OK case *)
Theorem run_inst_seq_sing_ok:
  ∀ i ss ss'.
    step_inst_base i ss = OK ss' ⇒
    run_inst_seq [i] ss = OK ss'
Proof
  simp[run_inst_seq_def]
QED

(* Single instruction: Abort case *)
Theorem run_inst_seq_sing_abort:
  ∀ i ss a ss'.
    step_inst_base i ss = Abort a ss' ⇒
    run_inst_seq [i] ss = Abort a ss'
Proof
  simp[run_inst_seq_def]
QED

(* Cons: if head succeeds, recurse on tail *)
Theorem run_inst_seq_cons_ok:
  ∀ i is ss ss'.
    step_inst_base i ss = OK ss' ⇒
    run_inst_seq (i::is) ss = run_inst_seq is ss'
Proof
  simp[run_inst_seq_def]
QED

(* Cons: if head aborts, whole sequence aborts *)
Theorem run_inst_seq_cons_abort:
  ∀ i is ss a ss'.
    step_inst_base i ss = Abort a ss' ⇒
    run_inst_seq (i::is) ss = Abort a ss'
Proof
  simp[run_inst_seq_def]
QED

(* ===== Common patterns: pure ops + assert ===== *)

(* Pattern: two pure ops then ASSERT — either OK or Revert.
   Covers: int_clamp, bytes_clamp, bool_clamp. *)
Theorem run_pure2_assert_ok_or_revert:
  ∀ i1 i2 i3 ss ss1 ss2.
    step_inst_base i1 ss = OK ss1 ∧
    step_inst_base i2 ss1 = OK ss2 ∧
    (step_inst_base i3 ss2 = OK ss2 ∨
     ∃ ss3. step_inst_base i3 ss2 = Abort Revert_abort ss3)
    ⇒
    ∃ ss'.
      run_inst_seq [i1; i2; i3] ss = OK ss' ∨
      run_inst_seq [i1; i2; i3] ss = Abort Revert_abort ss'
Proof
  rw[run_inst_seq_def] >> gvs[]
QED

(* Pattern: three pure ops then ASSERT *)
Theorem run_pure3_assert_ok_or_revert:
  ∀ i1 i2 i3 i4 ss ss1 ss2 ss3.
    step_inst_base i1 ss = OK ss1 ∧
    step_inst_base i2 ss1 = OK ss2 ∧
    step_inst_base i3 ss2 = OK ss3 ∧
    (step_inst_base i4 ss3 = OK ss3 ∨
     ∃ ss4. step_inst_base i4 ss3 = Abort Revert_abort ss4)
    ⇒
    ∃ ss'.
      run_inst_seq [i1; i2; i3; i4] ss = OK ss' ∨
      run_inst_seq [i1; i2; i3; i4] ss = Abort Revert_abort ss'
Proof
  rw[run_inst_seq_def] >> gvs[]
QED

(* Pattern: pure prefix succeeds, then rest *)
Theorem run_inst_seq_prefix_ok = run_inst_seq_append

(* ===== Compile monad: emitted_insts characterization ===== *)

(* emit_op emits exactly one instruction and returns Var of the fresh output *)
Theorem emitted_insts_emit_op:
  ∀ opc ops st v st'.
    emit_op opc ops st = (v, st') ⇒
    emitted_insts st st' =
      [mk_inst st.cs_next_id opc ops
               [STRING #"%" (toString st.cs_next_var)]] ∧
    v = Var (STRING #"%" (toString st.cs_next_var)) ∧
    st'.cs_next_id = st.cs_next_id + 1 ∧
    st'.cs_next_var = st.cs_next_var + 1 ∧
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id opc ops
               [STRING #"%" (toString st.cs_next_var)]]
Proof
  rw[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
     comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* emit_void emits exactly one instruction with no outputs *)
Theorem emitted_insts_emit_void:
  ∀ opc ops st st'.
    emit_void opc ops st = ((), st') ⇒
    emitted_insts st st' =
      [mk_inst st.cs_next_id opc ops []] ∧
    st'.cs_next_id = st.cs_next_id + 1 ∧
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id opc ops []]
Proof
  rw[emit_void_def, comp_bind_def, fresh_id_def, emit_def, emitted_insts_def]
  \\ gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* Chaining: emitted_insts through sequential emit_op calls *)
Theorem emitted_insts_seq2 = emitted_insts_append;

(* ===== Fresh variable invariant ===== *)

(* Compiler's fresh variable counter is ahead of all %-named vars in the
   venom state. Ensures emit_op/emit_void produce names that don't alias
   any existing operand. *)
Definition fresh_vars_wrt_def:
  fresh_vars_wrt (st:compile_state) (ss:venom_state) ⇔
    ∀ n. n ≥ st.cs_next_var ⇒
      STRING #"%" (toString n) ∉ FDOM ss.vs_vars
End

(* fresh_vars_wrt preserved by update_var of a name below the counter *)
Theorem fresh_vars_wrt_update_var:
  ∀ st ss name n w.
    fresh_vars_wrt st ss ∧
    name = STRING #"%" (toString n) ∧
    n < st.cs_next_var ⇒
    fresh_vars_wrt st (update_var name w ss)
Proof
  rw[fresh_vars_wrt_def, update_var_def]
QED

(* fresh_vars_wrt preserved when counter advances past the written var *)
Theorem fresh_vars_wrt_advance:
  ∀ st st' ss name n w.
    fresh_vars_wrt st ss ∧
    name = STRING #"%" (toString n) ∧
    n = st.cs_next_var ∧
    st'.cs_next_var > st.cs_next_var ⇒
    fresh_vars_wrt st' (update_var name w ss)
Proof
  rw[fresh_vars_wrt_def, update_var_def]
QED

(* fresh_vars_wrt preserved by mstore (memory doesn't affect vs_vars) *)
Theorem fresh_vars_wrt_mstore:
  ∀ st ss addr val.
    fresh_vars_wrt st ss ⇒
    fresh_vars_wrt st (mstore addr val ss)
Proof
  rw[fresh_vars_wrt_def, mstore_def]
QED

(* fresh_vars_wrt: an operand that evaluates in ss doesn't alias fresh vars *)
Theorem fresh_vars_wrt_eval_operand:
  ∀ st ss op v x n.
    fresh_vars_wrt st ss ∧
    eval_operand op ss = SOME v ∧
    n ≥ st.cs_next_var ∧
    op = Var x ⇒
    x ≠ STRING #"%" (toString n)
Proof
  rw[fresh_vars_wrt_def, eval_operand_def] >>
  strip_tac >> gvs[eval_operand_def, lookup_var_def] >>
  first_x_assum drule >>
  gvs[finite_mapTheory.TO_FLOOKUP]
QED

(* eval_operand preserved through update_var when the written name
   doesn't alias op. Hypotheses ensure non-aliasing via freshness. *)
Theorem eval_operand_update_fresh:
  ∀ op v w name n ss st.
    eval_operand op ss = SOME v ∧
    fresh_vars_wrt st ss ∧
    name = STRING #"%" (toString n) ∧
    n ≥ st.cs_next_var ⇒
    eval_operand op (update_var name w ss) = SOME v
Proof
  Cases >> rw[eval_operand_def, lookup_var_update_var] >>
  drule fresh_vars_wrt_eval_operand >>
  simp[eval_operand_def] >>
  disch_then drule >> rw[]
QED

(* ===== Fresh variable name properties ===== *)

Theorem not_tilde_num_to_dec_string[simp]:
  num_to_dec_string n <> #"~"::s
Proof
  strip_tac
  \\ `EVERY isDigit (#"~"::s)`
  by metis_tac[ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string]
  \\ gvs[stringTheory.isDigit_def]
QED

(* Fresh variables from different counter values are distinct *)
Theorem fresh_var_distinct:
  ∀ m n. m ≠ n ⇒
    STRING #"%" (toString m) ≠ STRING #"%" (toString n)
Proof
  rw[integer_wordTheory.toString_def, integerTheory.Num_EQ] >>
  strip_tac >> gvs[] >> intLib.COOPER_TAC
QED

(* A fresh variable name is not equal to any earlier fresh variable *)
Theorem fresh_var_neq:
  ∀ base offset. offset > 0 ⇒
    STRING #"%" (toString base) ≠
    STRING #"%" (toString (base + offset))
Proof
  rw[]
QED

(* ===== Compound: emit_op then eval_operand on result ===== *)

(* After emit_op, the returned operand evaluates to f(args) in the updated state.
   This is the key composition lemma: emit_op + step + eval_operand. *)
Theorem emit_op_result_eval:
  ∀ opc ops st v st' f ss ss' vals.
    emit_op opc ops st = (v, st') ∧
    (* All input operands evaluate *)
    MAP (λop. eval_operand op ss) ops = MAP SOME vals ∧
    (* The emitted instruction steps to ss' *)
    run_inst_seq (emitted_insts st st') ss = OK ss' ⇒
    eval_operand v ss' = lookup_var (STRING #"%" (toString st.cs_next_var)) ss'
Proof
  rw[emit_op_def, comp_bind_def, fresh_id_def, fresh_var_def,
     comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def] >>
  rw[eval_operand_def]
QED
