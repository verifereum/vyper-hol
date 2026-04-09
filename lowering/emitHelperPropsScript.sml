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
  instIdxIndep vfmState
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
    st'.cs_next_var = st.cs_next_var ∧
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id opc ops []]
Proof
  rw[emit_void_def, comp_bind_def, fresh_id_def, emit_def, emitted_insts_def]
  \\ gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* Chaining: emitted_insts through sequential emit_op calls *)
Theorem emitted_insts_seq2 = emitted_insts_append;

(* ===== Fresh variable invariant ===== *)
(* fresh_vars_wrt is defined in compileEnvScript.sml *)

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

(* ===== Compile monad: emit_inst, fresh_label, new_block properties ===== *)

(* emit_inst: appends one instruction, preserves block structure *)
Theorem emit_inst_extends:
  ∀ opc ops outs st st'.
    emit_inst opc ops outs st = ((), st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id opc ops outs] ∧
    st'.cs_current_bb = st.cs_current_bb ∧
    st'.cs_blocks = st.cs_blocks ∧
    st'.cs_next_id = st.cs_next_id + 1 ∧
    st'.cs_next_var = st.cs_next_var ∧
    st'.cs_next_label = st.cs_next_label
Proof
  rw[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >> rw[]
QED

(* fresh_label: only changes cs_next_label *)
Theorem fresh_label_props:
  ∀ prefix st lbl st'.
    fresh_label prefix st = (lbl, st') ⇒
    st'.cs_current_bb = st.cs_current_bb ∧
    st'.cs_blocks = st.cs_blocks ∧
    st'.cs_current_insts = st.cs_current_insts ∧
    st'.cs_next_var = st.cs_next_var ∧
    st'.cs_next_id = st.cs_next_id ∧
    st'.cs_next_label = st.cs_next_label + 1
Proof
  rw[fresh_label_def, comp_bind_def, comp_return_def] >> rw[]
QED

(* new_block: finalizes current block, starts new one *)
Theorem new_block_props:
  ∀ label st old_lbl st'.
    new_block label st = (old_lbl, st') ⇒
    old_lbl = st.cs_current_bb ∧
    st'.cs_current_bb = label ∧
    st'.cs_current_insts = [] ∧
    st'.cs_blocks =
      <| bb_label := st.cs_current_bb;
         bb_instructions := st.cs_current_insts |> :: st.cs_blocks ∧
    st'.cs_next_var = st.cs_next_var ∧
    st'.cs_next_id = st.cs_next_id ∧
    st'.cs_next_label = st.cs_next_label
Proof
  rw[new_block_def] >> rw[]
QED

(* ===== Layer 1: Connecting run_inst_seq to exec_block ===== *)

(* Running non-terminator, non-INVOKE instructions within a block:
   If instructions at indices [idx .. idx + LENGTH insts) match `insts`,
   and run_inst_seq succeeds, then exec_block from idx reaches
   idx + LENGTH insts with the same state.

   This lets us "fast forward" through a prefix of a block's instructions
   using run_inst_seq, then reason about the terminator separately. *)
Theorem exec_block_inst_seq_prefix:
  ∀ insts fuel ctx bb idx ss ss'.
    run_inst_seq insts ss = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀ k. k < LENGTH insts ⇒
          get_instruction bb (idx + k) = SOME (EL k insts))
    ⇒
    exec_block fuel ctx bb (ss with vs_inst_idx := idx) =
      exec_block fuel ctx bb (ss' with vs_inst_idx := idx + LENGTH insts)
Proof
  Induct_on `insts` >>
  rw[run_inst_seq_def] >>
  Cases_on `step_inst_base h ss` >> gvs[] >>
  simp[Once exec_block_def] >>
  CASE_TAC >- (first_x_assum(qspec_then`0`mp_tac) >> rw[]) >>
  first_assum(qspec_then`0`mp_tac) >>
  impl_tac >- rw[] >> simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
  simp[Once step_inst_def] >>
  drule step_inst_inst_idx_indep >>
  simp[] >> disch_then kall_tac >>
  simp[exec_result_map_def] >>
  first_x_assum drule >>
  `idx + SUC (LENGTH insts) = SUC idx + LENGTH insts` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  disch_then irule >>
  rw[] >>
  first_x_assum(qspec_then`SUC k`mp_tac) >>
  rw[] >> gvs[arithmeticTheory.ADD1]
QED

(* Full single-block execution ending with JMP:
   Non-terminator instructions followed by a JMP. *)
Theorem exec_block_inst_seq_jmp:
  ∀ insts fuel ctx bb idx ss ss' target_lbl jmp_id.
    run_inst_seq insts ss = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀ k. k < LENGTH insts ⇒
          get_instruction bb (idx + k) = SOME (EL k insts)) ∧
    get_instruction bb (idx + LENGTH insts) =
      SOME (mk_inst jmp_id JMP [Label target_lbl] []) ∧
    ¬ss'.vs_halted
    ⇒
    exec_block fuel ctx bb (ss with vs_inst_idx := idx) =
      OK (jump_to target_lbl ss')
Proof
  rw[] >>
  drule_all exec_block_inst_seq_prefix >> simp[] >>
  disch_then kall_tac >>
  simp[Once exec_block_def] >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_def, is_terminator_def, jump_to_def]
QED

(* Full single-block execution ending with JNZ *)
Theorem exec_block_inst_seq_jnz:
  ∀ insts fuel ctx bb idx ss ss' cond_op cond_v
    lbl_nz lbl_z jnz_id.
    run_inst_seq insts ss = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀ k. k < LENGTH insts ⇒
          get_instruction bb (idx + k) = SOME (EL k insts)) ∧
    get_instruction bb (idx + LENGTH insts) =
      SOME (mk_inst jnz_id JNZ [cond_op; Label lbl_nz; Label lbl_z] []) ∧
    eval_operand cond_op ss' = SOME cond_v ∧
    ¬ss'.vs_halted
    ⇒
    exec_block fuel ctx bb (ss with vs_inst_idx := idx) =
      OK (jump_to (if cond_v ≠ 0w then lbl_nz else lbl_z) ss')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exec_block_inst_seq_prefix >> simp[] >>
  disch_then kall_tac >>
  simp[Once exec_block_def] >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_def, is_terminator_def, jump_to_def] >>
  simp[eval_op_inst_idx] >> rw[]
QED

(* ===== Combined emit_op + step + frame lemmas ===== *)

(* These package up emitted_insts + run_inst_seq + step + freshness/frame
   for common opcodes. Each one says: running the emitted instruction
   succeeds, the result operand has the right value, and all frame
   conditions (operands, memory, freshness) are preserved. *)

(* emit_op for a pure 2-operand opcode *)
(* Generic: emit_op for pure 2-operand opcode *)
Theorem emit_op_pure2_correct:
  ∀ opc f op1 op2 v1 v2 st v st' ss.
    emit_op opc [op1; op2] st = (v, st') ∧
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ∧
    fresh_vars_wrt st ss ∧
    step_inst_base (mk_inst st.cs_next_id opc [op1; op2]
                     [STRING #"%" (toString st.cs_next_var)]) ss =
      OK (update_var (STRING #"%" (toString st.cs_next_var)) (f v1 v2) ss)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand v ss' = SOME (f v1 v2) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ⇒ EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory = LENGTH ss.vs_memory
Proof
  rw[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def] >>
  simp[eval_operand_update_var] >>
  drule emit_op_extends >>
  simp[same_blocks_def] >>
  strip_tac >> gvs[] >>
  conj_tac
  >- (
    irule fresh_vars_wrt_advance
    >> simp[] >>
    goal_assum $ drule_at Any >> gvs[] ) >>
  conj_tac >- (
    rw[]
    \\ irule eval_operand_update_fresh
    >> rw[]
    >> goal_assum $ drule_at Any >> gvs[] ) >>
  rw[update_var_def]
QED

Theorem emit_op_ADD_correct:
  ∀ op1 op2 v1 v2 st v st' ss.
    emit_op ADD [op1; op2] st = (v, st') ∧
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand v ss' = SOME (v1 + v2) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ⇒ EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory = LENGTH ss.vs_memory
Proof
  rw[] >> irule emit_op_pure2_correct >> gvs[] >>
  goal_assum $ drule_at (Pat`emit_op`) >> gvs[] >>
  irule step_ADD >> rw[]
QED

Theorem emit_op_MUL_correct:
  ∀ op1 op2 v1 v2 st v st' ss.
    emit_op MUL [op1; op2] st = (v, st') ∧
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand v ss' = SOME (v1 * v2) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ⇒ EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory = LENGTH ss.vs_memory
Proof
  rw[] >> irule emit_op_pure2_correct >> gvs[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> gvs[] >>
  irule step_MUL >> rw[]
QED

Theorem emit_op_MLOAD_correct:
  ∀ op1 v1 st v st' ss.
    emit_op MLOAD [op1] st = (v, st') ∧
    eval_operand op1 ss = SOME v1 ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand v ss' = SOME (mload (w2n v1) ss) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      (∀ a. a < LENGTH ss.vs_memory ⇒ EL a ss'.vs_memory = EL a ss.vs_memory) ∧
      LENGTH ss'.vs_memory = LENGTH ss.vs_memory
Proof
  rw[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def] >>
  drule step_MLOAD >> simp[] >> disch_then kall_tac >>
  simp[eval_operand_update_var] >>
  drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule fresh_vars_wrt_advance >> simp[] >>
      goal_assum $ drule_at Any >> gvs[]) >>
  conj_tac
  >- (rw[] >> irule eval_operand_update_fresh >> rw[] >>
      goal_assum $ drule_at Any >> gvs[]) >>
  rw[update_var_def]
QED

Theorem fresh_vars_wrt_emit_void:
  fresh_vars_wrt st1 ss /\
  emit_void op args st1 = (uu,st2) ==>
  fresh_vars_wrt st2 ss
Proof
  rw[emit_void_def, comp_bind_def, fresh_id_def, comp_return_def, emit_def] >>
  gvs[fresh_vars_wrt_def]
QED

Theorem emit_void_MSTORE_correct:
  ∀ op1 op2 v1 v2 st st' ss.
    emit_void MSTORE [op1; op2] st = ((), st') ∧
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = mstore (w2n v1) v2 ss ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  `step_inst_base (mk_inst st.cs_next_id MSTORE [op1; op2] []) ss =
     OK (mstore (w2n v1) v2 ss)` by simp[step_MSTORE] >>
  simp[run_inst_seq_def] >>
  drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  simp[fresh_vars_wrt_mstore, eval_operand_mstore] >>
  irule fresh_vars_wrt_mstore >> gvs[] >>
  irule fresh_vars_wrt_emit_void >>
  goal_assum drule >> gvs[]
QED

Theorem emit_void_MCOPY_correct:
  ∀ op_dst op_src op_sz dst_v src_v sz_v st st' ss.
    emit_void MCOPY [op_dst; op_src; op_sz] st = ((), st') ∧
    eval_operand op_dst ss = SOME dst_v ∧
    eval_operand op_src ss = SOME src_v ∧
    eval_operand op_sz ss = SOME sz_v ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = mcopy (w2n dst_v) (w2n src_v) (w2n sz_v) ss ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  `step_inst_base (mk_inst st.cs_next_id MCOPY [op_dst; op_src; op_sz] []) ss =
     OK (mcopy (w2n dst_v) (w2n src_v) (w2n sz_v) ss)`
    by simp[step_inst_base_def] >>
  simp[run_inst_seq_def] >>
  drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  conj_tac >- (
    gvs[fresh_vars_wrt_def, mcopy_def, write_memory_with_expansion_def,
        emit_void_def, comp_bind_def, fresh_id_def, emit_def]) >>
  rw[] >> Cases_on `op` >>
  gvs[eval_operand_def, mcopy_def, write_memory_with_expansion_def,
       lookup_var_def, LET_THM]
QED


(* ===== Storage Opcodes ===== *)

Theorem step_SLOAD:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    step_inst_base (mk_inst id SLOAD [op1] [out]) ss =
      OK (update_var out (sload v1 ss) ss)
Proof
  rw[step_inst_base_def, exec_read1_def]
QED

Theorem step_SSTORE:
  ∀ op1 op2 v1 v2 id ss.
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id SSTORE [op1; op2] []) ss =
      OK (sstore v1 v2 ss)
Proof
  rw[step_inst_base_def, exec_write2_def]
QED

Theorem step_ASSERT_ok:
  ∀ op1 v id ss.
    eval_operand op1 ss = SOME v ∧ v ≠ 0w ⇒
    step_inst_base (mk_inst id ASSERT [op1] []) ss = OK ss
Proof
  rw[step_inst_base_def, mk_inst_def] >> gvs[]
QED

Theorem step_ASSERT_revert:
  ∀ op1 id ss.
    eval_operand op1 ss = SOME 0w ⇒
    step_inst_base (mk_inst id ASSERT [op1] []) ss =
      Abort Revert_abort (revert_state (set_returndata [] ss))
Proof
  rw[step_inst_base_def, mk_inst_def]
QED

(* ===== sload / sstore / update_var independence ===== *)

(* sload reads vs_accounts; update_var writes vs_vars → independent *)
Theorem sload_update_var[simp]:
  ∀ k v w s. sload k (update_var v w s) = sload k s
Proof
  rw[sload_def, contract_storage_def, update_var_def]
QED

(* sstore writes vs_accounts; vs_memory is unaffected *)
Theorem sstore_vs_memory[simp]:
  ∀ k v s. (sstore k v s).vs_memory = s.vs_memory
Proof
  rw[sstore_def, LET_THM]
QED

(* sstore writes vs_accounts; vs_vars is unaffected *)
Theorem sstore_vs_vars[simp]:
  ∀ k v s. (sstore k v s).vs_vars = s.vs_vars
Proof
  rw[sstore_def, LET_THM]
QED

(* sstore writes vs_accounts; vs_call_ctx is unaffected *)
Theorem sstore_vs_call_ctx[simp]:
  ∀ k v s. (sstore k v s).vs_call_ctx = s.vs_call_ctx
Proof
  rw[sstore_def, LET_THM]
QED

(* sstore writes vs_accounts; vs_labels is unaffected *)
Theorem sstore_vs_labels[simp]:
  ∀ k v s. (sstore k v s).vs_labels = s.vs_labels
Proof
  rw[sstore_def, LET_THM]
QED

(* eval_operand only reads vs_vars → preserved by sstore *)
Theorem eval_operand_sstore[simp]:
  ∀ op k v s. eval_operand op (sstore k v s) = eval_operand op s
Proof
  Cases >> rw[eval_operand_def, lookup_var_def]
QED

(* fresh_vars_wrt only examines vs_vars → preserved by sstore *)
Theorem fresh_vars_wrt_sstore[simp]:
  ∀ st k v s. fresh_vars_wrt st (sstore k v s) = fresh_vars_wrt st s
Proof
  rw[fresh_vars_wrt_def]
QED

(* sload after sstore at same key returns new value *)
Theorem sload_sstore_same:
  ∀ k v s. sload k (sstore k v s) = v
Proof
  rw[sload_def, sstore_def, contract_storage_def, LET_THM,
     lookup_account_def, lookup_storage_def, update_storage_def,
     combinTheory.UPDATE_APPLY]
QED

(* sload after sstore at different key: unchanged *)
Theorem sload_sstore_diff:
  ∀ k k' v s. k ≠ k' ⇒ sload k (sstore k' v s) = sload k s
Proof
  rw[sload_def, sstore_def, contract_storage_def, LET_THM,
     lookup_account_def, lookup_storage_def, update_storage_def,
     combinTheory.UPDATE_APPLY, combinTheory.APPLY_UPDATE_THM]
QED

(* ===== Generic emit_op for read1 opcodes ===== *)

(* This covers MLOAD, SLOAD, TLOAD, CALLDATALOAD, etc.
   Any opcode where step_inst_base = exec_read1 f for some f.
   Result: update_var out (f v1 ss) ss — only vs_vars changes. *)
Theorem emit_op_read1_correct:
  ∀ opc f op1 v1 st v st' ss.
    emit_op opc [op1] st = (v, st') ∧
    eval_operand op1 ss = SOME v1 ∧
    fresh_vars_wrt st ss ∧
    step_inst_base (mk_inst st.cs_next_id opc [op1]
                     [STRING #"%" (toString st.cs_next_var)]) ss =
      OK (update_var (STRING #"%" (toString st.cs_next_var)) (f v1 ss) ss)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand v ss' = SOME (f v1 ss) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_accounts = ss.vs_accounts ∧
      ss'.vs_labels = ss.vs_labels
Proof
  rw[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def] >>
  simp[eval_operand_update_var] >>
  drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule fresh_vars_wrt_advance >> simp[] >>
      goal_assum $ drule_at Any >> gvs[]) >>
  conj_tac
  >- (rw[] >> irule eval_operand_update_fresh >> rw[] >>
      goal_assum $ drule_at Any >> gvs[]) >>
  rw[update_var_def]
QED

Theorem emit_op_SLOAD_correct:
  ∀ op1 v1 st v st' ss.
    emit_op SLOAD [op1] st = (v, st') ∧
    eval_operand op1 ss = SOME v1 ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand v ss' = SOME (sload v1 ss) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_accounts = ss.vs_accounts ∧
      ss'.vs_labels = ss.vs_labels
Proof
  rw[] >> irule emit_op_read1_correct >> gvs[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> gvs[] >>
  irule step_SLOAD >> rw[]
QED

(* ===== Generic emit_void for write2 opcodes ===== *)

Theorem emit_void_SSTORE_correct:
  ∀ op1 op2 v1 v2 st st' ss.
    emit_void SSTORE [op1; op2] st = ((), st') ∧
    eval_operand op1 ss = SOME v1 ∧
    eval_operand op2 ss = SOME v2 ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = sstore v1 v2 ss ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      ss'.vs_memory = ss.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  `step_inst_base (mk_inst st.cs_next_id SSTORE [op1; op2] []) ss =
     OK (sstore v1 v2 ss)` by simp[step_SSTORE] >>
  simp[run_inst_seq_def] >>
  drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  simp[] >>
  irule fresh_vars_wrt_emit_void >>
  goal_assum drule >> gvs[]
QED

(* ASSERT: emit_void_ASSERT_ok — ASSERT succeeds when condition nonzero *)
Theorem emit_void_ASSERT_ok:
  ∀ op1 v st st' ss.
    emit_void ASSERT [op1] st = ((), st') ∧
    eval_operand op1 ss = SOME v ∧
    v ≠ 0w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = ss ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, assert_ok] >>
  drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  irule fresh_vars_wrt_emit_void >>
  goal_assum drule >> gvs[]
QED

(* ASSERT: emit_void_ASSERT_revert — ASSERT reverts when condition = 0w *)
Theorem emit_void_ASSERT_revert:
  ∀ op1 st st' ss.
    emit_void ASSERT [op1] st = ((), st') ∧
    eval_operand op1 ss = SOME 0w
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      Abort Revert_abort (revert_state (set_returndata [] ss))
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def] >>
  `step_inst_base (mk_inst st.cs_next_id ASSERT [op1] []) ss =
     Abort Revert_abort (revert_state (set_returndata [] ss))`
    by simp[assert_revert] >>
  simp[]
QED

(* ===== Compound emit chain helpers ===== *)

(* Chaining: emitted_insts through monad bind *)
Theorem emitted_insts_bind:
  ∀ f g st st1 st2 a.
    f st = (a, st1) ∧
    g a st1 = st2 ∧
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1
    ⇒
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1
Proof
  rw[]
QED

(* ===== Multi-step run_inst_seq composition ===== *)

(* 4 steps all OK *)
Theorem run_inst_seq_4:
  ∀ i1 i2 i3 i4 ss s1 s2 s3 s4.
    step_inst_base i1 ss = OK s1 ∧
    step_inst_base i2 s1 = OK s2 ∧
    step_inst_base i3 s2 = OK s3 ∧
    step_inst_base i4 s3 = OK s4 ⇒
    run_inst_seq [i1;i2;i3;i4] ss = OK s4
Proof
  rw[run_inst_seq_def]
QED

(* 5 steps all OK *)
Theorem run_inst_seq_5:
  ∀ i1 i2 i3 i4 i5 ss s1 s2 s3 s4 s5.
    step_inst_base i1 ss = OK s1 ∧
    step_inst_base i2 s1 = OK s2 ∧
    step_inst_base i3 s2 = OK s3 ∧
    step_inst_base i4 s3 = OK s4 ∧
    step_inst_base i5 s4 = OK s5 ⇒
    run_inst_seq [i1;i2;i3;i4;i5] ss = OK s5
Proof
  rw[run_inst_seq_def]
QED

(* 3 OK steps then abort at step 4, with trailing instructions *)
Theorem run_inst_seq_ok3_abort:
  ∀ i1 i2 i3 i4 rest ss s1 s2 s3 a s4.
    step_inst_base i1 ss = OK s1 ∧
    step_inst_base i2 s1 = OK s2 ∧
    step_inst_base i3 s2 = OK s3 ∧
    step_inst_base i4 s3 = Abort a s4 ⇒
    run_inst_seq ([i1;i2;i3;i4] ++ rest) ss = Abort a s4
Proof
  rw[run_inst_seq_def]
QED

(* same_blocks is transitive *)
Theorem same_blocks_trans:
  ∀ st1 st2 st3.
    same_blocks st1 st2 ∧ same_blocks st2 st3 ⇒ same_blocks st1 st3
Proof
  rw[same_blocks_def]
QED


(* ===== Instruction sequence composition ===== *)

(* Two-step composition: if two sequential emit phases each succeed,
   the combined emitted instructions also succeed. *)
(* Two-step composition: if two sequential emit phases each succeed,
   the combined emitted instructions also succeed.
   The cs_current_insts preconditions come from emit_op_extends/emit_void_extends. *)
Theorem run_emitted_compose2:
  ∀ st st1 st2 ss ss1 ss2.
    run_inst_seq (emitted_insts st st1) ss = OK ss1 ∧
    run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2 ∧
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2
    ⇒
    run_inst_seq (emitted_insts st st2) ss = OK ss2
Proof
  rpt strip_tac >>
  drule_all emitted_insts_append >> strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq (emitted_insts st st1) _ = _`
    (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts st1 st2` mp_tac) >> simp[]
QED

(* cs_current_insts extends transitively (for building compose3 preconditions) *)
Theorem emit_extends_trans:
  ∀ st st1 st2.
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2
    ⇒
    st2.cs_current_insts = st.cs_current_insts ++ emitted_insts st st2
Proof
  rpt strip_tac >>
  drule_all emitted_insts_append >> strip_tac >> gvs[]
QED

(* Three-step composition *)
Theorem run_emitted_compose3:
  ∀ st st1 st2 st3 ss ss1 ss2 ss3.
    run_inst_seq (emitted_insts st st1) ss = OK ss1 ∧
    run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2 ∧
    run_inst_seq (emitted_insts st2 st3) ss2 = OK ss3 ∧
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2 ∧
    st3.cs_current_insts = st2.cs_current_insts ++ emitted_insts st2 st3
    ⇒
    run_inst_seq (emitted_insts st st3) ss = OK ss3
Proof
  rpt strip_tac >>
  `run_inst_seq (emitted_insts st st2) ss = OK ss2` by (
    irule run_emitted_compose2 >>
    goal_assum (drule_at (Pat `run_inst_seq _ ss1 = OK _`)) >>
    goal_assum (drule_at (Pat `run_inst_seq _ ss = OK _`)) >>
    simp[]) >>
  `st2.cs_current_insts = st.cs_current_insts ++ emitted_insts st st2` by (
    irule emit_extends_trans >>
    goal_assum (drule_at (Pat `st1.cs_current_insts = _`)) >> simp[]) >>
  irule run_emitted_compose2 >>
  goal_assum (drule_at (Pat `run_inst_seq _ ss2 = OK _`)) >>
  goal_assum (drule_at (Pat `run_inst_seq _ ss = OK _`)) >>
  simp[]
QED
