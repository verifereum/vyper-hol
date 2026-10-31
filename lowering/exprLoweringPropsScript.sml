(*
 * Expression Lowering Properties
 *
 * TOP-LEVEL:
 *   run_inst_seq             — run instruction sequence on Venom state
 *   emitted_insts            — extract new instructions from compile state
 *   stmt_state_rel           — state_rel with the Venom-side allocation
 *                              facts a fragment keeps, and alloca_room
 *   alloca_room, pending_alloca_size — the frontier plus the sizes of the
 *                              ALLOCAs not yet run stays below 2 ** 256
 *   compile_expr_correct     — main expression lowering correctness
 *   compile_literal_vv_correct  — word literal case
 *   compile_name_correct     — variable lookup case
 *   compile_binop_correct    — binary operation case
 *   compile_expr_grows, compile_binop_grows — compile_expr, lower_value
 *                              and compile_binop only append (cs_extends)
 *                              and grow the counters
 *   compile_expr_ci_mono     — the same as ci_mono
 *
 * Helper:
 *   ci_mono_refl, ci_mono_bind, ci_mono_ignore_bind, ci_mono_comp_return,
 *   ci_mono_compile_* (copy_memory, word_copy_loop, store_bytestring,
 *   keccak256_key, mapping_subscript, array_subscript, bytelike_literal),
 *   ci_mono_typed_memory_family — ci_mono of the monad and of the helpers
 *                              compile_expr calls, for stmtLoweringMono
 *   state_rel_jump_to, state_rel_push_scope, state_rel_pop_scope,
 *   state_rel_frame, stmt_state_rel_jump_to, stmt_state_rel_inst_idx,
 *   stmt_state_rel_push_scope, stmt_state_rel_pop_scope,
 *   stmt_state_rel_update_var, stmt_state_rel_allocas_frame — frames for
 *                              the state relations
 *   local_ptrs_rel_cenv_cong, state_rel_cenv_cong,
 *   stmt_state_rel_cenv_cong — the relations at another compile
 *                              environment that agrees on what they read
 *   local_ptrs_reserved_next_var, local_ptrs_reserved_fresh,
 *   local_ptrs_reserved_not_live — local_ptrs_reserved survives a later
 *                              cs_next_var, and fresh variables and the
 *                              pointers of locals out of scope are not
 *                              live local pointers
 *
 * Mirrors correctness of: exprLoweringScript.sml (compile_expr)
 * Source semantics: vyperInterpreterScript.sml (eval_expr)
 * Target semantics: venomExecSemanticsScript.sml (step_inst_base)
 *)

Theory exprLoweringProps
Ancestors
  exprLowering emitHelper compileEnv accountsRelProps builtinSystem
  venomExecSemantics venomState venomInst venomInstProps
  vyperInterpreter vyperContext
  vyperState vyperValueOperation
  valueEncoding valueEncodingProofs localPtrsProps venomMemDefs
  vyperAST vyperTyping
Libs
  pairLib BasicProvers monadsyntax

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
   Handles: Literal, Name, Env vars, Not, Neg, BinOp.
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

(* The sizes func's frame can still allocate: those of its ALLOCAs whose ids
   have no allocation yet.  Every ALLOCA the lowering emits has a literal
   size; any other counts as the whole address space. *)
Definition pending_alloca_size_def:
  pending_alloca_size (func:ir_function) (ss:venom_state) =
    SUM (MAP (\inst. case inst.inst_operands of
                       [Lit n] => w2n n
                     | _ => dimword (:256))
             (FILTER (\inst. inst.inst_opcode = ALLOCA /\
                             inst.inst_id NOTIN FDOM ss.vs_allocas)
                (fn_insts func)))
End

(* Room in func's frame: the frontier plus every allocation func can still
   make stays below 2 ** 256, so no ALLOCA of func hands out a wrapped
   pointer.  A fresh ALLOCA of func moves its size from the pending sizes to
   the frontier; a step that leaves the allocations alone keeps it, and so
   does an INVOKE, which gives the caller its frontier back
   (merge_callee_state). *)
Definition alloca_room_def:
  alloca_room func (ss:venom_state) <=>
    ss.vs_alloca_next + pending_alloca_size func ss < dimword (:256)
End

(* state_rel in func, the function running, with the Venom-side facts a
   statement fragment needs and keeps:
   - alloca_inv: the recorded allocations are disjoint and below the
     frontier;
   - an allocation recorded for an ALLOCA of func has the size it asks for.
     A re-executed ALLOCA (a loop body, a branch) returns the recorded base
     without checking its size, so with alloca_inv this is what makes its
     region miss every other live local;
   - alloca_room: func's allocations still to come fit below 2 ** 256, so
     the frontier stays below 2 ** 256 and a declaration's ALLOCA hands out
     its base unwrapped, after other declarations and inside bodies. *)
Definition stmt_state_rel_def:
  stmt_state_rel func cenv cx vs ss ⇔
    state_rel func cenv cx vs ss ∧ alloca_inv ss ∧ alloca_room func ss ∧
    ∀inst n base sz.
      MEM inst (fn_insts func) ∧ inst.inst_opcode = ALLOCA ∧
      inst.inst_operands = [Lit n] ∧
      FLOOKUP ss.vs_allocas inst.inst_id = SOME (base, sz) ⇒
      sz = w2n n
End

Theorem alloca_room_fields:
  !func ss ss'.
    alloca_room func ss /\
    ss'.vs_allocas = ss.vs_allocas /\ ss'.vs_alloca_next = ss.vs_alloca_next ==>
    alloca_room func ss'
Proof
  rw[alloca_room_def, pending_alloca_size_def] >> gvs[]
QED

(* state_rel re-established by a step that keeps the allocations gives
   stmt_state_rel back. *)
Theorem stmt_state_rel_allocas_frame:
  !func cenv cx es s es' s'.
    stmt_state_rel func cenv cx es s /\ state_rel func cenv cx es' s' /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next ==>
    stmt_state_rel func cenv cx es' s'
Proof
  rw[stmt_state_rel_def]
  >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[])
  >- (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  gvs[] >> res_tac
QED

Theorem alloca_room_next_lt:
  !func ss. alloca_room func ss ==> ss.vs_alloca_next < dimword (:256)
Proof
  rw[alloca_room_def] >> decide_tac
QED

Theorem SUM_MAP_FILTER_mono[local]:
  !(f:'a -> num) P P' l.
    (!y. P' y ==> P y) ==>
    SUM (MAP f (FILTER P' l)) <= SUM (MAP f (FILTER P l))
Proof
  rpt gen_tac >> strip_tac >> Induct_on `l` >> rw[] >> gvs[] >> res_tac
QED

Theorem SUM_MAP_FILTER_drop[local]:
  !(f:'a -> num) P P' x l.
    MEM x l /\ P x /\ ~P' x /\ (!y. P' y ==> P y) ==>
    SUM (MAP f (FILTER P' l)) + f x <= SUM (MAP f (FILTER P l))
Proof
  rpt gen_tac >> strip_tac >> rpt (pop_assum mp_tac) >>
  Induct_on `l` >> rw[] >> gvs[] >> metis_tac[SUM_MAP_FILTER_mono]
QED

(* A fresh ALLOCA of func fits below 2 ** 256 and keeps the room. *)
Theorem alloca_room_fresh:
  !func ss inst n.
    alloca_room func ss /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit n] /\
    inst.inst_id NOTIN FDOM ss.vs_allocas ==>
    ss.vs_alloca_next + w2n n < dimword (:256) /\
    alloca_room func
      (ss with <| vs_allocas :=
                    ss.vs_allocas |+ (inst.inst_id, (ss.vs_alloca_next, w2n n));
                  vs_alloca_next := ss.vs_alloca_next + w2n n |>)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then
    [`\i:instruction. case i.inst_operands of
                        [Lit n] => w2n n | _ => dimword (:256)`,
     `\i. i.inst_opcode = ALLOCA /\ i.inst_id NOTIN FDOM ss.vs_allocas`,
     `\i. i.inst_opcode = ALLOCA /\
          i.inst_id NOTIN (inst.inst_id INSERT FDOM ss.vs_allocas)`,
     `inst`, `fn_insts func`] mp_tac SUM_MAP_FILTER_drop >>
  impl_tac >- simp[] >>
  fs[alloca_room_def, pending_alloca_size_def]
QED

(* The expression lemmas relate states with stmt_state_rel func, where func
   is the function the code runs in, under the code premises of the
   statement lemmas (stmtLoweringProps), with fn_has_code, which is defined
   above this theory, replaced by its single-block consequence: the emitted
   instructions are func's.  An ALLOCA of the expression (a buffer) then
   misses every live local, and a Name reads a pointer local, not a MemLoc
   variable, which state_rel does not relate. *)
Theorem compile_expr_correct:
  ∀ func cenv cx ty e es ss st op st' v es'.
    stmt_state_rel func cenv cx es ss ∧
    supported_expr e ∧
    well_annotated e ∧
    (do result <- eval_expr cx e; read_result cx result od) es =
      (INL v, es') ∧
    lower_value compile_expr cenv ty e st = (op, st') ∧
    (∀i. MEM i (emitted_insts st st') ⇒ MEM i (fn_insts func)) ∧
    fn_inst_ids_distinct func ∧ local_ptrs_reserved cenv st
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      stmt_state_rel func cenv cx es' ss' ∧
      same_blocks st st' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      ¬ss'.vs_halted ∧
      EVERY (λi. ¬is_terminator i.inst_opcode ∧ i.inst_opcode ≠ INVOKE)
        (emitted_insts st st') ∧
      (∀x w. not_fresh_at st x ∧ lookup_var x ss = SOME w ⇒
             lookup_var x ss' = SOME w) ∧
      (∀x. op = Var x ⇒ not_fresh_at st' x)
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

(* emit_op emits exactly one instruction and returns Var of the fresh output *)
Theorem emitted_insts_emit_op_local:
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

(* update_var keeps state_rel unless it overwrites a live local's pointer:
   the other conjuncts do not read vs_vars. *)
Theorem state_rel_update_var_local:
  ∀ func cenv cx es ss name w.
    state_rel func cenv cx es ss ∧ not_local_ptr cenv es.scopes name ⇒
    state_rel func cenv cx es (update_var name w ss)
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes (update_var name w ss)` by
    (irule local_ptrs_rel_update_var >> fs[state_rel_def]) >>
  fs[state_rel_def, update_var_def, storage_rel_def,
     transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
     contract_storage_def, contract_transient_def]
QED

Theorem state_rel_jump_to:
  !func cenv cx es s lbl.
    state_rel func cenv cx es (jump_to lbl s) <=> state_rel func cenv cx es s
Proof
  simp[state_rel_def, local_ptrs_rel_def, local_region_def, local_backed_def,
       lookup_var_def, storage_rel_def, transient_rel_def, immutables_rel_def,
       logs_rel_def, call_ctx_rel_def, contract_storage_def,
       contract_transient_def, jump_to_def]
QED

Theorem state_rel_push_scope:
  !func cenv cx es s.
    state_rel func cenv cx (es with scopes := FEMPTY :: es.scopes) s <=>
    state_rel func cenv cx es s
Proof
  simp[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
       logs_rel_def, local_ptrs_rel_push_scope]
QED

Theorem state_rel_pop_scope:
  !func cenv cx es s sc rest.
    state_rel func cenv cx es s /\ es.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    state_rel func cenv cx (es with scopes := rest) s
Proof
  rpt strip_tac >>
  fs[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
     logs_rel_def] >>
  irule local_ptrs_rel_pop_scope >> qexists_tac `sc` >> gvs[]
QED

(* state_rel reads the Venom state only through the locals' memory and
   the fields below. *)
Theorem state_rel_frame:
  !func cenv cx es es' s s'.
    state_rel func cenv cx es s /\ local_ptrs_rel func cenv es'.scopes s' /\
    es' = es with scopes := es'.scopes /\
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\ s'.vs_logs = s.vs_logs /\
    s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_data_section = s.vs_data_section ==>
    state_rel func cenv cx es' s'
Proof
  rpt strip_tac >>
  qpat_x_assum `es' = _` SUBST1_TAC >>
  fs[state_rel_def, storage_rel_def, transient_rel_def, accounts_rel_def,
     immutables_rel_def, logs_rel_def, call_ctx_rel_def, contract_storage_def,
     contract_transient_def]
QED

Theorem stmt_state_rel_jump_to:
  !func cenv cx es s lbl.
    stmt_state_rel func cenv cx es (jump_to lbl s) <=>
    stmt_state_rel func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_jump_to, jump_to_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def]
QED

Theorem stmt_state_rel_inst_idx:
  !func cenv cx es s n.
    stmt_state_rel func cenv cx es (s with vs_inst_idx := n) <=>
    stmt_state_rel func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def]
QED

Theorem stmt_state_rel_push_scope:
  !func cenv cx es s.
    stmt_state_rel func cenv cx (es with scopes := FEMPTY :: es.scopes) s <=>
    stmt_state_rel func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_push_scope]
QED

Theorem stmt_state_rel_pop_scope:
  !func cenv cx es s sc rest.
    stmt_state_rel func cenv cx es s /\ es.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
    stmt_state_rel func cenv cx (es with scopes := rest) s
Proof
  rw[stmt_state_rel_def] >> metis_tac[state_rel_pop_scope]
QED

Theorem local_ptrs_rel_cenv_cong:
  !func cenv cenv' scopes ss.
    local_ptrs_rel func cenv' scopes ss /\
    (!n e. lookup_scopes n scopes = SOME e ==>
           FLOOKUP cenv.ce_vars n = FLOOKUP cenv'.ce_vars n) ==>
    local_ptrs_rel func cenv scopes ss
Proof
  rw[local_ptrs_rel_def, local_region_def] >> metis_tac[]
QED

(* state_rel reads cenv through the locals in scope and its other
   (storage, transient, immutable) bindings. *)
Theorem state_rel_cenv_cong:
  !func cenv cenv' cx vs ss.
    state_rel func cenv' cx vs ss /\
    (!n e. lookup_scopes n vs.scopes = SOME e ==>
           FLOOKUP cenv.ce_vars n = FLOOKUP cenv'.ce_vars n) /\
    (!n l. FLOOKUP cenv.ce_vars n = SOME l /\ (!p sz. l <> PtrVar p sz) ==>
           FLOOKUP cenv'.ce_vars n = SOME l) /\
    (!n l. FLOOKUP cenv'.ce_vars n = SOME l /\ (!p sz. l <> PtrVar p sz) ==>
           FLOOKUP cenv.ce_vars n = SOME l) /\
    cenv'.ce_module = cenv.ce_module /\ cenv'.ce_is_ctor = cenv.ce_is_ctor ==>
    state_rel func cenv cx vs ss
Proof
  rw[state_rel_def]
  >- metis_tac[local_ptrs_rel_cenv_cong]
  >- (simp[storage_vars_rel_def] >> conj_tac >> rpt strip_tac
      >- (`FLOOKUP cenv'.ce_vars (module_var_key (cenv.ce_module,name)) =
           SOME (StorageLoc slot)` by
            (qpat_x_assum `!n l. FLOOKUP cenv.ce_vars n = SOME l /\ _ ==> _`
               irule >> simp[]) >>
          qpat_x_assum `storage_vars_rel cenv' cx` mp_tac >>
          simp[storage_vars_rel_def] >> metis_tac[]) >>
      qpat_x_assum `!n l. FLOOKUP cenv'.ce_vars n = SOME l /\ _ ==> _` irule >>
      simp[] >> qpat_x_assum `storage_vars_rel cenv' cx` mp_tac >>
      simp[storage_vars_rel_def] >> metis_tac[])
  >- (simp[transient_vars_rel_def] >> conj_tac >> rpt strip_tac
      >- (`FLOOKUP cenv'.ce_vars (module_var_key (cenv.ce_module,name)) =
           SOME (TransientLoc slot)` by
            (qpat_x_assum `!n l. FLOOKUP cenv.ce_vars n = SOME l /\ _ ==> _`
               irule >> simp[]) >>
          qpat_x_assum `transient_vars_rel cenv' cx` mp_tac >>
          simp[transient_vars_rel_def] >> metis_tac[]) >>
      qpat_x_assum `!n l. FLOOKUP cenv'.ce_vars n = SOME l /\ _ ==> _` irule >>
      simp[] >> qpat_x_assum `transient_vars_rel cenv' cx` mp_tac >>
      simp[transient_vars_rel_def] >> metis_tac[])
  >- (fs[immutables_rel_def, LET_THM] >> Cases_on `cenv.ce_is_ctor` >>
      gvs[] >> rpt strip_tac >>
      `FLOOKUP cenv'.ce_vars (module_var_key (cenv.ce_module,name)) =
       SOME (ImmutableLoc byte_offset)` by (first_x_assum irule >> simp[]) >>
      metis_tac[]) >>
  fs[logs_rel_def, listTheory.LIST_REL_EL_EQN, log_entry_equiv_def]
QED

(* stmt_state_rel reads the compile environment through the locals in
   scope and its other bindings. *)
Theorem stmt_state_rel_cenv_cong:
  !func cenv cenv' cx es ss.
    stmt_state_rel func cenv' cx es ss /\
    (!n e. lookup_scopes n es.scopes = SOME e ==>
           FLOOKUP cenv.ce_vars n = FLOOKUP cenv'.ce_vars n) /\
    (!n l. FLOOKUP cenv.ce_vars n = SOME l /\ (!p sz. l <> PtrVar p sz) ==>
           FLOOKUP cenv'.ce_vars n = SOME l) /\
    (!n l. FLOOKUP cenv'.ce_vars n = SOME l /\ (!p sz. l <> PtrVar p sz) ==>
           FLOOKUP cenv.ce_vars n = SOME l) /\
    cenv'.ce_module = cenv.ce_module /\ cenv'.ce_is_ctor = cenv.ce_is_ctor ==>
    stmt_state_rel func cenv cx es ss
Proof
  rw[stmt_state_rel_def] >- (irule state_rel_cenv_cong >> metis_tac[]) >>
  res_tac
QED

(* Assigning a variable that is no live local's pointer. *)
Theorem stmt_state_rel_update_var:
  !func cenv cx es s x w.
    stmt_state_rel func cenv cx es s /\ not_local_ptr cenv es.scopes x ==>
    stmt_state_rel func cenv cx es (update_var x w s)
Proof
  rpt strip_tac >> fs[stmt_state_rel_def] >> rpt conj_tac
  >- (irule state_rel_update_var_local >> simp[])
  >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[update_var_def])
  >- (irule alloca_room_fields >> qexists_tac `s` >> simp[update_var_def]) >>
  simp[update_var_def] >> metis_tac[]
QED

Theorem local_ptrs_reserved_next_var:
  !cenv st st'.
    local_ptrs_reserved cenv st /\ st.cs_next_var <= st'.cs_next_var ==>
    local_ptrs_reserved cenv st'
Proof
  rw[local_ptrs_reserved_def, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* A variable the compiler hands out from st on is no local's pointer. *)
Theorem local_ptrs_reserved_fresh:
  !cenv st scopes n.
    local_ptrs_reserved cenv st /\ st.cs_next_var <= n ==>
    not_local_ptr cenv scopes (STRING #"%" (toString n))
Proof
  rw[local_ptrs_reserved_def, not_local_ptr_def, not_fresh_at_def] >>
  strip_tac >> metis_tac[]
QED

(* A local's pointer is no other local's, so it is no live local's pointer
   while the local itself is not live. *)
Theorem local_ptrs_reserved_not_live:
  !cenv st scopes id p sz.
    local_ptrs_reserved cenv st /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_scopes id scopes = NONE ==>
    not_local_ptr cenv scopes p
Proof
  rw[local_ptrs_reserved_def, not_local_ptr_def] >> strip_tac >>
  `name = id` by metis_tac[] >> gvs[]
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
  ∀ func cenv cx ty l es ss st vv st'.
    state_rel func cenv cx es ss ∧
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

(* A well-typed word value held in memory is the word at its base. *)
Theorem word_val_in_memory_mem_word_at[local]:
  ∀bt v off mem.
    val_in_memory (BaseTV bt) v off mem ∧ value_has_type (BaseTV bt) v ∧
    is_word_type (BaseT bt) ⇒
    mem_word_at off mem = typed_val_to_w256 (BaseTV bt) v
Proof
  rpt strip_tac >> Cases_on `v` >> Cases_on `bt` >>
  gvs[value_has_type_def, is_word_type_def]
  >~ [`BytesT bd`]
  >- (Cases_on `bd` >>
      gvs[value_has_type_def, is_word_type_def,
          valueEncodingPropsTheory.val_in_memory_fixed_bytes])
  >~ [`BaseTV AddressT`]
  >- gvs[valueEncodingPropsTheory.val_in_memory_address] >>
  gvs[val_in_memory_def, typed_val_to_w256_def]
QED

(* --- Name (local variable load) --- *)
(* v must be a primitive (word-sized) value.  The local is held through its
   pointer variable (PtrVar), which is what state_rel relates.
   Uses typed_val_to_w256 (not val_to_w256) to avoid BytesV address heuristic.
   The type_value tv from the scope correctly distinguishes address from bytesN. *)
(* NOTE: original statement was FALSE for v = NoneV and for
   type/value mismatches like entry.type=BaseTV BoolT with v=BytesV [1w]
   (ruled out by value_has_type). val_in_memory (BaseTV (UintT n)) NoneV
   offset mem = T (vacuously true) but mload offset ss is unconstrained,
   while typed_val_to_w256 NoneV = 0w.
   Fix: added v ≠ NoneV and value_has_type entry.type v.
   It was also false for a non-word annotation ann: compile_name_vv tags the
   pointer with ann, and unwrap_value loads only if is_word_type ann, else it
   returns the pointer; eval_expr ignores ann.  Fix: added is_word_type ann. *)
Theorem compile_name_correct:
  ∀ func cenv cx ty ann id es ss st op st' v es' p size entry.
    state_rel func cenv cx es ss ∧
    (do result <- eval_expr cx (Name ann id); read_result cx result od) es =
      (INL v, es') ∧
    lower_value compile_expr cenv ty (Name ann id) st = (op, st') ∧
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) size) ∧
    lookup_scopes id es.scopes = SOME entry ∧
    entry.value = v ∧
    v ≠ NoneV ∧
    value_has_type entry.type v ∧
    (∃ bt. entry.type = BaseTV bt ∧ is_word_type (BaseT bt)) ∧
    is_word_type ann
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (typed_val_to_w256 entry.type v) ∧
      es' = es ∧
      same_blocks st st'
Proof
  rpt gen_tac >> strip_tac >>
  `es' = es` by
    (qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, ignore_bind_def] >>
     metis_tac[read_result_state]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, compile_expr_def, expr_type_def, compile_name_vv_def,
       unwrap_value_def, contextTheory.mk_ptr_def,
       contextTheory.compile_ptr_load_def, comp_bind_def,
       comp_return_def] >>
  strip_tac >>
  drule emit_op_extends >> drule emitted_insts_emit_op_local >>
  rpt strip_tac >> gvs[] >>
  `∃w. lookup_var p ss = SOME w ∧
       val_in_memory (BaseTV bt) entry.value (w2n w) ss.vs_memory` by
    (fs[state_rel_def, local_ptrs_rel_def] >> first_x_assum drule_all >>
     strip_tac >> qexists_tac `w` >> gvs[]) >>
  `eval_operand (Var p) ss = SOME w` by simp[eval_operand_def] >>
  drule step_MLOAD_local >> strip_tac >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  `mload (w2n w) ss = mem_word_at (w2n w) ss.vs_memory` by
    simp[mload_def, mem_word_at_def] >>
  simp[] >> irule word_val_in_memory_mem_word_at >> simp[]
QED

(* --- BinOp (safe arithmetic) --- *)
(* For compile_binop: the emitted instructions compute the correct
   result and any overflow checks correctly abort on invalid inputs *)
(* NOTE: original statement was FALSE when annotation type has different
   bounds than expr_type e1. Evaluator uses type_to_int_bound ann for
   bounds checking, compiler uses type_bounds(expr_type e1).
   Fix: added type consistency + fresh_vars_wrt + named annotation.
   fresh_vars_wrt is now dropped (see stmt_state_rel): local_ptrs_reserved
   keeps the temporaries off the locals' pointers. *)
Theorem compile_binop_correct:
  ∀ func cenv cx ty ann bop e1 e2 es ss st op st' v es'.
    stmt_state_rel func cenv cx es ss ∧
    (∀u. type_to_int_bound ann = SOME u ⇒
         type_to_int_bound (expr_type e1) = SOME u) ∧
    (do result <- eval_expr cx (Builtin ann (Bop bop) [e1; e2]);
        read_result cx result od) es =
      (INL v, es') ∧
    lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1; e2]) st = (op, st') ∧
    (∀i. MEM i (emitted_insts st st') ⇒ MEM i (fn_insts func)) ∧
    fn_inst_ids_distinct func ∧ local_ptrs_reserved cenv st
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      stmt_state_rel func cenv cx es' ss'
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
  Cases_on `b` >> rpt strip_tac >>
  `(mk_inst inst_id ISZERO [op] [out_var]).inst_opcode = ISZERO`
    by simp[venomInstTheory.mk_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pop_assum (fn th => PURE_REWRITE_TAC[th]) >>
  simp[exec_pure1_def, venomInstTheory.mk_inst_def, val_to_w256_def,
       venomExecSemanticsTheory.bool_to_word_def]
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
  rpt strip_tac >>
  simp[venomInstTheory.mk_inst_def] >>
  simp[Once step_inst_base_def] >>
  simp[comp_return_def, comp_bind_def, comp_ignore_bind_def]
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

(* NOTE: original statement was FALSE when annotation type has different
   bounds than expr_type e. Compiler uses type_bounds(expr_type e) but
   evaluator uses type_to_int_bound(annotation type). Additionally, Neg
   is only defined for signed integers — unsigned annotation (e.g.
   UintT 256 with IntV 0) gave a spurious counterexample.
   Fix: named annotation, added type_to_int_bound constraint, and
   restricted ann to signed IntT. *)
Theorem compile_neg_correct:
  ∀ func cenv cx ty ann e es ss st op st' v es' n.
    stmt_state_rel func cenv cx es ss ∧
    (do result <- eval_expr cx (Builtin ann Neg [e]); read_result cx result od) es =
      (INL v, es') ∧
    ann = BaseT (IntT n) ∧
    type_to_int_bound ann = type_to_int_bound (expr_type e) ∧
    lower_value compile_expr cenv ty (Builtin ann Neg [e]) st = (op, st') ∧
    (∀i. MEM i (emitted_insts st st') ⇒ MEM i (fn_insts func)) ∧
    fn_inst_ids_distinct func ∧ local_ptrs_reserved cenv st
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      stmt_state_rel func cenv cx es' ss'
Proof
  cheat
QED

(* --- Environment variables (CALLER, TIMESTAMP, etc.) --- *)

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

Theorem same_blocks_sym:
  same_blocks st st1 ==> same_blocks st1 st
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
   only appends code (cs_extends) and hands out variables and instruction
   ids from st's counters on.  This is the key invariant for all compile
   monad operations. *)
Definition ci_mono_def:
  ci_mono (st:compile_state) (st':compile_state) ⇔
    cs_extends st st' ∧ st.cs_next_var ≤ st'.cs_next_var ∧
    st.cs_next_id ≤ st'.cs_next_id
End

Theorem ci_mono_refl:
  ci_mono st st
Proof
  simp[ci_mono_def, cs_extends_refl]
QED

Theorem ci_mono_trans[local]:
  ci_mono a b ∧ ci_mono b c ⇒ ci_mono a c
Proof
  simp[ci_mono_def] >> rpt strip_tac >> gvs[] >>
  irule cs_extends_trans >> qexists `b` >> simp[]
QED

(* ci_mono composes through monad_bind (= comp_bind) *)
Theorem ci_mono_bind:
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
Theorem ci_mono_ignore_bind:
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
  rw[ci_mono_def, same_blocks_def, cs_extends_def] >>
  gvs[listTheory.APPEND_EQ_SELF]
QED

(* ci_mono for primitives *)
Theorem ci_mono_comp_return:
  ∀ x sa. ci_mono sa (SND (comp_return x sa))
Proof
  simp[comp_return_def, ci_mono_refl]
QED

Theorem ci_mono_emit[local]:
  ∀ inst sa. ci_mono sa (SND (emit inst sa))
Proof
  rpt gen_tac >> Cases_on `emit inst sa` >> drule cs_extends_emit >>
  gvs[ci_mono_def, emit_def]
QED

Theorem ci_mono_fresh_var:
  ∀ sa. ci_mono sa (SND (fresh_var sa))
Proof
  gen_tac >> Cases_on `fresh_var sa` >> drule cs_extends_fresh_var >>
  gvs[ci_mono_def, fresh_var_def]
QED

Theorem ci_mono_fresh_id[local]:
  ∀ sa. ci_mono sa (SND (fresh_id sa))
Proof
  gen_tac >> Cases_on `fresh_id sa` >> drule cs_extends_fresh_id >>
  gvs[ci_mono_def, fresh_id_def]
QED

Theorem ci_mono_fresh_label:
  ∀ pfx sa. ci_mono sa (SND (fresh_label pfx sa))
Proof
  rpt gen_tac >> Cases_on `fresh_label pfx sa` >>
  drule cs_extends_fresh_label >> gvs[ci_mono_def, fresh_label_def]
QED

Theorem ci_mono_new_block:
  ∀ label sa. ci_mono sa (SND (new_block label sa))
Proof
  rpt gen_tac >> Cases_on `new_block label sa` >>
  drule cs_extends_new_block >> gvs[ci_mono_def, new_block_def]
QED

(* Sequence ci_mono through binds, lets and conditionals, down to the
   operations named in rws. *)
fun ci_mono_chain_tac rws =
  rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind, IF_CASES_TAC] >>
       rpt conj_tac >> rpt gen_tac >> PURE_REWRITE_TAC[LET_THM] >> BETA_TAC) >>
  simp (ci_mono_comp_return :: rws);

val ci_mono_prim_rws =
  [ci_mono_emit, ci_mono_fresh_var, ci_mono_fresh_id, ci_mono_fresh_label,
   ci_mono_new_block];

Theorem ci_mono_emit_op:
  ∀ opc ops sa. ci_mono sa (SND (emit_op opc ops sa))
Proof
  rw[emit_op_def] >> ci_mono_chain_tac ci_mono_prim_rws
QED

Theorem ci_mono_emit_void:
  ∀ opc ops sa. ci_mono sa (SND (emit_void opc ops sa))
Proof
  rw[emit_void_def] >> ci_mono_chain_tac ci_mono_prim_rws
QED

Theorem ci_mono_emit_inst:
  ∀ opc ops outs sa. ci_mono sa (SND (emit_inst opc ops outs sa))
Proof
  rw[emit_inst_def] >> ci_mono_chain_tac ci_mono_prim_rws
QED

(* ci_mono for compile_ptr_load (used by unwrap_value) *)
Theorem ci_mono_compile_ptr_load[local]:
  ∀ is_ctor loc op sa. ci_mono sa (SND (compile_ptr_load is_ctor loc op sa))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[contextTheory.compile_ptr_load_def] >>
  rw[] >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_ptr_store[local]:
  ∀ is_ctor loc op v sa.
    ci_mono sa (SND (compile_ptr_store is_ctor loc op v sa))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[contextTheory.compile_ptr_store_def] >>
  rw[] >> simp[ci_mono_emit_void]
QED

val ci_mono_emit_rws =
  ci_mono_prim_rws @
  [ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
   ci_mono_compile_ptr_load, ci_mono_compile_ptr_store];

(* ci_mono for compile_word_copy_loop *)
Theorem ci_mono_compile_word_copy_loop:
  ∀ src dst wc ll sl ic sa.
    ci_mono sa (SND (compile_word_copy_loop src dst wc ll sl ic sa))
Proof
  rw[contextTheory.compile_word_copy_loop_def, LET_THM] >>
  ci_mono_chain_tac ci_mono_emit_rws
QED

(* ci_mono for compile_alloc_buffer *)
Theorem ci_mono_compile_alloc_buffer:
  ∀ size sa. ci_mono sa (SND (compile_alloc_buffer size sa))
Proof
  rw[contextTheory.compile_alloc_buffer_def] >>
  ci_mono_chain_tac ci_mono_emit_rws
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
  ci_mono_chain_tac [ci_mono_compile_word_copy_loop]
QED

val ci_mono_copy_rws =
  ci_mono_emit_rws @
  [ci_mono_compile_alloc_buffer, ci_mono_compile_storage_to_memory,
   ci_mono_compile_transient_to_memory, ci_mono_compile_code_to_memory];

Theorem ci_mono_compile_ensure_in_memory[local]:
  ∀ ptr_op loc mem_bytes word_count is_ctor sa.
    ci_mono sa
      (SND (compile_ensure_in_memory ptr_op loc mem_bytes word_count is_ctor sa))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[contextTheory.compile_ensure_in_memory_def] >>
  ci_mono_chain_tac ci_mono_copy_rws
QED

(* ci_mono for unwrap_value *)
Theorem ci_mono_unwrap_value:
  ∀ cenv vv sa. ci_mono sa (SND (unwrap_value cenv vv sa))
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[unwrap_value_def]
  (* StackValue: comp_return *)
  >- simp[comp_return_def, ci_mono_refl]
  (* LocatedValue: split on is_word_type *)
  >> rw[]
  (* word type: compile_ptr_load *)
  >- simp[ci_mono_compile_ptr_load]
  (* non-word type: case on ptr_location *)
  >> Cases_on `p.ptr_location` >>
  simp[LET_THM]
  >- simp[comp_return_def, ci_mono_refl]
  >> simp[ci_mono_compile_ensure_in_memory]
QED

Theorem ci_mono_lower_value_cfn:
  ∀ cfn cenv ty e sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (lower_value cfn cenv ty e sa))
Proof
  rpt strip_tac >> simp[lower_value_def] >> irule ci_mono_bind >> simp[ci_mono_unwrap_value]
QED

Theorem ci_mono_compile_dynarray_pop[local]:
  ∀ base_op ws es load_opc store_opc sa.
    ci_mono sa (SND (compile_dynarray_pop base_op ws es load_opc store_opc sa))
Proof
  simp[compile_dynarray_pop_def, LET_THM] >>
  rpt (CHANGED_TAC (rpt gen_tac >>
    (TRY (irule ci_mono_bind >> conj_tac) >>
     TRY (irule ci_mono_ignore_bind >> conj_tac) >>
     simp[ci_mono_emit_op, ci_mono_emit_void])))
QED

(* ===== compile_expr ci_mono by induction ===== *)

(*
 * ci_mono for compile_expr: every call only appends code and hands out
 * variables and instruction ids from its input state's counters on.
 * Proved by unfolding definitions and composing ci_mono lemmas.
 *)

Theorem ci_mono_compile_store_bytestring:
  ∀ val_op dst_op sa.
    ci_mono sa (SND (compile_store_bytestring val_op dst_op sa))
Proof
  simp[contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def, LET_THM] >>
  rpt (CHANGED_TAC (rpt gen_tac >>
    (TRY (irule ci_mono_bind >> conj_tac) >>
     TRY (irule ci_mono_ignore_bind >> conj_tac) >>
     simp[ci_mono_emit_op, ci_mono_emit_void])))
QED

Theorem ci_mono_compile_copy_memory:
  ∀ dst src sz sa. ci_mono sa (SND (compile_copy_memory dst src sz sa))
Proof
  rpt gen_tac >> Cases_on `sz` >>
  rewrite_tac[contextTheory.compile_copy_memory_def] >>
  simp[ci_mono_comp_return, ci_mono_emit_void]
QED

Theorem ci_mono_compile_copy_memory_dynamic[local]:
  ∀ dst src len_op sa. ci_mono sa (SND (compile_copy_memory_dynamic dst src len_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[contextTheory.compile_copy_memory_dynamic_def] >>
  simp[ci_mono_emit_void]
QED

Theorem ci_mono_compile_with_byte_offset[local]:
  ∀ base offset sa. ci_mono sa (SND (compile_with_byte_offset base offset sa))
Proof
  rw[contextTheory.compile_with_byte_offset_def] >>
  simp[ci_mono_comp_return, ci_mono_emit_op]
QED

Theorem ci_mono_typed_memory_family:
  (∀cenv dst dst_ty src src_ty sa.
    ci_mono sa (SND (compile_store_memory_typed cenv dst dst_ty src src_ty sa))) ∧
  (∀cenv dst src dst_tys src_tys dst_off src_off sa.
    ci_mono sa (SND (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off sa))) ∧
  (∀cenv dst dst_ty src src_ty count sa.
    ci_mono sa (SND (compile_copy_sarray_typed cenv dst dst_ty src src_ty count sa))) ∧
  (∀cenv dst dst_ty cap src src_ty sa.
    ci_mono sa (SND (compile_copy_dynarray_typed cenv dst dst_ty cap src src_ty sa))) ∧
  (∀cenv dst src dst_fields src_fields dst_off src_off sa.
    ci_mono sa (SND (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off sa)))
Proof
  ho_match_mp_tac contextTheory.compile_store_memory_typed_ind
  >> rpt conj_tac
  >- suspend "dispatch"
  >- suspend "fields_nil"
  >- suspend "fields_mismatch"
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- suspend "struct_nil"
  >> suspend "struct_cons"
QED

Resume ci_mono_typed_memory_family[dispatch]:
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dst_ty`
  >- (simp[Once contextTheory.compile_store_memory_typed_def] >>
      irule ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
  Cases_on `is_bytestring_type dst_ty ∧ is_bytestring_type src_ty`
  >- simp[Once contextTheory.compile_store_memory_typed_def,
           ci_mono_compile_store_bytestring] >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (Cases_on `dst_ty` >> Cases_on `src_ty` >>
      TRY (rename1 `compile_store_memory_typed cenv dst (ArrayT dt db) src (ArrayT st sb)` >>
           Cases_on `db` >> Cases_on `sb`) >> gvs[] >>
      simp[Once contextTheory.compile_store_memory_typed_def, LET_THM,
           ci_mono_compile_copy_memory] >> metis_tac[]) >>
  simp[Once contextTheory.compile_store_memory_typed_def, ci_mono_emit_void]
QED
Resume ci_mono_typed_memory_family[fields_nil]:
  simp[Once contextTheory.compile_store_memory_typed_def, ci_mono_comp_return]
QED
Resume ci_mono_typed_memory_family[fields_mismatch]:
  simp[Once contextTheory.compile_store_memory_typed_def, ci_mono_comp_return]
QED
Resume ci_mono_typed_memory_family[fields_cons]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once contextTheory.compile_store_memory_typed_def, LET_THM] >>
  gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_with_byte_offset] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_with_byte_offset] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> simp[]
QED
Resume ci_mono_typed_memory_family[sarray]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty ∧
            ¬is_abi_dynamic cenv.ce_struct_fields dst_ty` >> gvs[] >>
  simp[Once contextTheory.compile_store_memory_typed_def, LET_THM,
       ci_mono_compile_copy_memory] >>
  IF_CASES_TAC >- metis_tac[] >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_fresh_label, ci_mono_fresh_var,
         ci_mono_emit_inst, ci_mono_new_block, ci_mono_emit_op,
         ci_mono_comp_return]) ORELSE gen_tac) >>
  simp[ci_mono_comp_return]
QED
Resume ci_mono_typed_memory_family[dynarray]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty ∧ dst_ty = src_ty` >> gvs[] >>
  simp[Once contextTheory.compile_store_memory_typed_def, LET_THM] >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_fresh_label, ci_mono_fresh_var,
         ci_mono_emit_inst, ci_mono_new_block, ci_mono_emit_op, ci_mono_emit_void,
         ci_mono_compile_copy_memory_dynamic, ci_mono_comp_return]) ORELSE gen_tac) >>
  simp[ci_mono_compile_copy_memory_dynamic, ci_mono_comp_return] >>
  IF_CASES_TAC >- metis_tac[] >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_fresh_label, ci_mono_fresh_var,
         ci_mono_emit_inst, ci_mono_new_block, ci_mono_emit_op,
         ci_mono_compile_copy_memory_dynamic, ci_mono_comp_return]) ORELSE gen_tac) >>
  simp[ci_mono_comp_return]
QED
Resume ci_mono_typed_memory_family[struct_nil]:
  simp[Once contextTheory.compile_store_memory_typed_def, ci_mono_comp_return]
QED
Resume ci_mono_typed_memory_family[struct_cons]:
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP src_fields name` >>
  TRY (rename1 `SOME p` >> PairCases_on `p`) >> gvs[] >>
  (simp[Once contextTheory.compile_store_memory_typed_def, LET_THM] >>
   gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
   >- simp[ci_mono_compile_with_byte_offset] >>
   rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
   >- simp[ci_mono_compile_with_byte_offset] >>
   rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> simp[])
QED
Finalise ci_mono_typed_memory_family

Theorem ci_mono_compile_store_memory:
  ∀cenv src dst dst_ty src_ty sa.
    ci_mono sa (SND (compile_store_memory cenv src dst dst_ty src_ty sa))
Proof
  rpt gen_tac >>
  simp[contextTheory.compile_store_memory_def] >>
  rpt IF_CASES_TAC >>
  simp[ci_mono_emit_void, ci_mono_compile_store_bytestring,
       ci_mono_typed_memory_family, ci_mono_compile_copy_memory]
QED

Theorem ci_mono_compile_struct_lit_cfn:
  ∀ cfn cenv ty fields buf_op cur_offset sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_struct_lit cfn cenv ty fields buf_op cur_offset sa))
Proof
  Induct_on `fields` >> simp[compile_struct_lit_def, ci_mono_comp_return] >>
  rpt gen_tac >> Cases_on `h` >> strip_tac >>
  simp[Once compile_struct_lit_def, LET_THM] >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_unwrap_value,
                         ci_mono_compile_store_memory]) ORELSE gen_tac) >>
  first_x_assum irule >> simp[]
QED

Theorem ci_mono_compile_concat_cfn:
  ∀ cfn cenv es data_ptr infos offset_op sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_concat cfn cenv es data_ptr infos offset_op sa))
Proof
  recInduct compile_concat_ind >> rpt strip_tac >> gvs[compile_concat_def, ci_mono_comp_return] >>
Cases_on `is_bs` >> gvs[] >>
irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void] >>
TRY (irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_ignore_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_lower_value_cfn >> simp[])
QED

Theorem ci_mono_compile_make_array_elems_cfn[local]:
  ∀ cfn cenv es elem_ty elem_size has_lw buf_op cur_idx sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_make_array_elems cfn cenv es elem_ty elem_size has_lw buf_op cur_idx sa))
Proof
  Induct_on `es` >> simp[compile_make_array_elems_def, ci_mono_comp_return] >>
  rpt gen_tac >> strip_tac >>
  simp[Once compile_make_array_elems_def, LET_THM] >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_unwrap_value,
                         ci_mono_compile_store_memory]) ORELSE gen_tac) >>
  first_x_assum irule >> simp[]
QED

Theorem ci_mono_compile_make_array_cfn:
  ∀ cfn cenv es elem_ty elem_size has_lw buf_op sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_make_array cfn cenv es elem_ty elem_size has_lw buf_op sa))
Proof
  rpt strip_tac >> simp[compile_make_array_def] >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (Cases_on `has_lw` >> simp[ci_mono_emit_void, ci_mono_comp_return]) >>
  simp[ci_mono_compile_make_array_elems_cfn]
QED

Theorem ci_mono_compile_zero_words:
  ∀base n sa. ci_mono sa (SND (compile_zero_words base n sa))
Proof
  Induct_on `n` >> simp[builtinSimpleTheory.compile_zero_words_def,
                         ci_mono_comp_return] >> rpt gen_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac ci_mono_bind >>
  simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem ci_mono_compile_builtin_empty_complex[local]:
  ∀size lw sa. ci_mono sa (SND (compile_builtin_empty_complex size lw sa))
Proof
  rpt gen_tac >>
  simp[builtinSimpleTheory.compile_builtin_empty_complex_def, LET_THM] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_alloc_buffer] >>
  rpt gen_tac >> simp[comp_bind_def, comp_return_def] >>
  Cases_on `lw` >> simp[] >>
  (ho_match_mp_tac ci_mono_ignore_bind >>
   simp[ci_mono_emit_void, ci_mono_compile_zero_words, ci_mono_comp_return])
QED

(* Reusable tactic for ci_mono composition through monadic expressions *)
val ci_mono_base_thms =
  [ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
   ci_mono_fresh_var, ci_mono_fresh_id, ci_mono_fresh_label,
   ci_mono_new_block, ci_mono_comp_return, ci_mono_emit,
   ci_mono_compile_ptr_load, ci_mono_unwrap_value,
   ci_mono_compile_ensure_in_memory, ci_mono_compile_alloc_buffer,
   ci_mono_compile_word_copy_loop, ci_mono_compile_storage_to_memory,
   ci_mono_compile_transient_to_memory, ci_mono_compile_code_to_memory,
   ci_mono_compile_dynarray_pop,
   ci_mono_compile_store_bytestring, ci_mono_compile_store_memory,
   ci_mono_compile_builtin_empty_complex,
   ci_mono_refl];

Theorem ci_mono_compile_multi_exprs[local]:
  ∀ cfn cenv es sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_multi_exprs cfn cenv es sa))
Proof
  Induct_on `es` >> rpt strip_tac
  >- simp[compile_multi_exprs_def, ci_mono_comp_return]
  >> simp[Once compile_multi_exprs_def, LET_THM]
  >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> ho_match_mp_tac ci_mono_lower_value_cfn >> metis_tac[])
  >> rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> first_x_assum ho_match_mp_tac >> metis_tac[])
  >> rpt strip_tac >> simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_keccak256_key:
  ∀ key_op is_bytes32 sa.
    ci_mono sa (SND (compile_keccak256_key key_op is_bytes32 sa))
Proof
  rpt gen_tac >> simp[compile_keccak256_key_def, LET_THM] >> IF_CASES_TAC >> rpt gen_tac >> rpt (irule ci_mono_ignore_bind ORELSE irule ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_compile_alloc_buffer, ci_mono_comp_return] >> rpt gen_tac >> rpt (irule ci_mono_ignore_bind ORELSE irule ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_compile_alloc_buffer, ci_mono_comp_return]
QED

Theorem ci_mono_compile_mapping_subscript:
  ∀ base_slot key_op sa.
    ci_mono sa (SND (compile_mapping_subscript base_slot key_op sa))
Proof
  simp[compile_mapping_subscript_def, LET_THM] >>
  rpt (CHANGED_TAC (rpt gen_tac >>
    (TRY (irule ci_mono_bind >> conj_tac) >>
     TRY (irule ci_mono_ignore_bind >> conj_tac) >>
     simp[ci_mono_emit_op, ci_mono_emit_void,
          ci_mono_compile_alloc_buffer, ci_mono_comp_return])))
QED

Theorem ci_mono_compile_tuple_subscript[local]:
  ∀ base_op offset sa.
    ci_mono sa (SND (compile_tuple_subscript base_op offset sa))
Proof
  rpt gen_tac >> Cases_on `offset` >> simp[compile_tuple_subscript_def, ci_mono_emit_op, ci_mono_comp_return]
QED

Theorem ci_mono_compile_array_subscript:
  ∀ base_op idx_op is_dyn sc ws es is_signed load_opc sa.
    ci_mono sa (SND (compile_array_subscript base_op idx_op is_dyn sc ws es is_signed load_opc sa))
Proof
  rpt gen_tac >>
  simp[compile_array_subscript_def, LET_THM] >>
  rpt (CHANGED_TAC (rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind) >>
    rpt strip_tac >>
    simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
         ci_mono_compile_alloc_buffer, ci_mono_refl] >>
    TRY (IF_CASES_TAC >>
         simp[ci_mono_emit_op, ci_mono_comp_return, LET_THM])))
QED

Theorem ci_mono_compile_subscript_cfn[local]:
  ∀ cfn cenv ret_ty ty base_e idx_e sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_subscript cfn cenv ret_ty ty base_e idx_e sa))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_subscript_def] >> BETA_TAC >>
  irule ci_mono_bind >> conj_tac
  >- (rpt gen_tac >> simp[LET_THM] >>
      Cases_on `place_type cenv base_e` >> simp[]
      >- (irule ci_mono_bind >> conj_tac
          >- (rpt gen_tac >> BETA_TAC >> irule ci_mono_bind >> conj_tac
              >- (rpt gen_tac >> BETA_TAC >> irule ci_mono_bind >>
                  simp[ci_mono_comp_return, ci_mono_compile_mapping_subscript]) >>
              IF_CASES_TAC >>
              simp[ci_mono_compile_keccak256_key, ci_mono_comp_return]) >>
          irule ci_mono_lower_value_cfn >> metis_tac[]) >>
      Cases_on `t` >> simp[LET_THM] >>
      rpt (CHANGED_TAC (
        rpt gen_tac >>
        (irule ci_mono_bind >> conj_tac) >>
        simp[ci_mono_comp_return, ci_mono_compile_tuple_subscript,
             ci_mono_compile_array_subscript] >>
        TRY (irule ci_mono_lower_value_cfn >> metis_tac[])))) >>
  metis_tac[]
QED

Theorem ci_mono_compile_acc_cfn[local]:
  ∀ cfn cenv addr_e item sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_acc cfn cenv addr_e item sa))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `item`
  >- (rewrite_tac[Once compile_acc_def] >> irule ci_mono_lower_value_cfn >> metis_tac[]) >>
  simp[compile_acc_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >>
  TRY (irule ci_mono_emit_inst >> NO_TAC) >>
  TRY (irule ci_mono_trans >>
       qexists_tac `SND (lower_value cfn cenv (BaseT AddressT) addr_e sa)` >>
       conj_tac >- (irule ci_mono_lower_value_cfn >> metis_tac[]) >>
       simp[ci_mono_emit_op] >> NO_TAC) >>
  irule ci_mono_trans >>
  qexists_tac `SND (emit_op EXTCODESIZE
    [FST (lower_value cfn cenv (BaseT AddressT) addr_e sa)]
    (SND (lower_value cfn cenv (BaseT AddressT) addr_e sa)))` >>
  conj_tac >- (
    irule ci_mono_trans >>
    qexists_tac `SND (lower_value cfn cenv (BaseT AddressT) addr_e sa)` >>
    conj_tac >- (irule ci_mono_lower_value_cfn >> metis_tac[]) >>
    simp[ci_mono_emit_op]) >>
  simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_attribute_cfn[local]:
  ∀ cfn cenv ret_ty ty base_e field sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_attribute cfn cenv ret_ty ty base_e field sa))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_attribute_def] >> BETA_TAC >>
  irule ci_mono_bind >> conj_tac
  >- (rpt gen_tac >> simp[LET_THM] >>
      irule ci_mono_bind >> conj_tac >>
      simp[ci_mono_emit_op, ci_mono_comp_return] >>
      rpt gen_tac >> simp[ci_mono_comp_return])
  >> metis_tac[]
QED

(* ===== Kernel audit for changed place helpers ===== *)

val () = List.app (fn (name,theorem) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
  in
    if null (Thm.hyp theorem) andalso null axioms andalso
       List.all (fn label => label = "DISK_THM") oracles then
      print ("PLACE_HELPER_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
    else raise Fail ("admitted place helper: " ^ name)
  end)
  [("ci_mono_compile_subscript_cfn",ci_mono_compile_subscript_cfn),
   ("ci_mono_compile_attribute_cfn",ci_mono_compile_attribute_cfn),
   ("ci_mono_compile_mapping_subscript",ci_mono_compile_mapping_subscript),
   ("ci_mono_compile_keccak256_key",ci_mono_compile_keccak256_key),
   ("ci_mono_compile_make_array_cfn",ci_mono_compile_make_array_cfn)]

Theorem ci_mono_as_stack_val[local]:
  ∀ ty p sa. SND (as_stack_val ty p) = SND p
Proof
  rpt gen_tac >> Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem ci_mono_as_ptr_val[local]:
  ∀ ty loc p sa. SND (as_ptr_val ty loc p) = SND p
Proof
  rpt gen_tac >> Cases_on `p` >> simp[as_ptr_val_def]
QED

Theorem ci_mono_compile_clamp[local]:
  ∀ val_op ty sa. ci_mono sa (SND (compile_clamp val_op ty sa))
Proof
  rpt gen_tac >> simp[compile_clamp_def, LET_THM, pairTheory.UNCURRY] >> IF_CASES_TAC >> gvs[] >> rpt (rpt gen_tac >> (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind) >> (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void])) >> simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem ci_mono_compile_select[local]:
  ∀ cmp a b sa. ci_mono sa (SND (compile_select cmp a b sa))
Proof
  rpt gen_tac >> simp[builtinSimpleTheory.compile_select_def, LET_THM, pairTheory.UNCURRY_DEF] >> irule ci_mono_bind >> simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_bind >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_env_var[local]:
  ∀ item sa. ci_mono sa (SND (compile_env_var item sa))
Proof
  rpt gen_tac >> Cases_on `item` >> simp[compile_env_var_def] >> TRY (simp[ci_mono_emit_op] >> NO_TAC) >> irule ci_mono_bind >> simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_bind >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_invert[local]:
  ∀ v ty cenv sa. ci_mono sa (SND (compile_invert v ty cenv sa))
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[compile_invert_def, ci_mono_emit_op]
QED

Theorem ci_mono_emit_multi_op:
  ∀ opc ops n sa. ci_mono sa (SND (emit_multi_op opc ops n sa))
Proof
  rpt gen_tac >>
`!n sa. ci_mono sa (SND (fresh_vars n sa))` by (
  Induct >> simp[fresh_vars_def, ci_mono_comp_return] >>
  rpt gen_tac >>
  irule ci_mono_bind >>
  simp[ci_mono_fresh_var] >>
  rpt strip_tac >>
  irule ci_mono_bind >>
  simp[ci_mono_comp_return]
) >>
simp[emit_multi_op_def] >>
irule ci_mono_bind >>
simp[] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >>
simp[ci_mono_emit_inst, ci_mono_comp_return]
QED

Theorem ci_mono_store_multi_results:
  ∀ buf_op results offset sa. ci_mono sa (SND (store_multi_results buf_op results offset sa))
Proof
  Induct_on `results` >- simp[store_multi_results_def, ci_mono_comp_return] >> rpt strip_tac >> once_rewrite_tac[store_multi_results_def] >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >> simp[]
QED

Theorem ci_mono_compile_store_byte_chunks:
  ∀ data_ptr bs offset sa. ci_mono sa (SND (compile_store_byte_chunks data_ptr bs offset sa))
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> rpt strip_tac >- simp[compile_store_byte_chunks_def, ci_mono_comp_return] >> simp[Once compile_store_byte_chunks_def, LET_THM] >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >> first_x_assum (qspecl_then [`TAKE 32 (v4::v5 ++ REPLICATE 31 0w)`, `word_of_bytes T 0w (TAKE 32 (v4::v5 ++ REPLICATE 31 0w))`] mp_tac) >> simp[]
QED

Theorem ci_mono_compile_store_words[local]:
  ∀ buf_op vs offset sa. ci_mono sa (SND (compile_store_words buf_op vs offset sa))
Proof
  Induct_on `vs` >- simp[compile_store_words_def, ci_mono_comp_return] >> rpt strip_tac >> once_rewrite_tac[compile_store_words_def] >> simp_tac std_ss [LET_THM] >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_emit_op]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> simp[ci_mono_emit_void]
QED

Theorem ci_mono_clamp_and_return[local]:
  ∀ res ty sa. ci_mono sa (SND (clamp_and_return res ty sa))
Proof
  simp[clamp_and_return_def] >> metis_tac[ci_mono_ignore_bind, ci_mono_compile_clamp, ci_mono_comp_return]
QED

Theorem ci_mono_wrap_truncate[local]:
  ∀ res ty sa. ci_mono sa (SND (wrap_truncate res ty sa))
Proof
  rpt gen_tac >> simp[Once wrap_truncate_def] >> IF_CASES_TAC >> simp[ci_mono_comp_return] >> IF_CASES_TAC >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_safe_add[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_add x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_add_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_sub[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_sub x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_sub_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_mul_overflow_check[local]:
  ∀ x y res is_signed bits sa. ci_mono sa (SND (compile_mul_overflow_check x y res is_signed bits sa))
Proof
  rpt gen_tac >> simp[Once compile_mul_overflow_check_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_mul[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_mul x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_mul_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_compile_mul_overflow_check ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_div[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_div x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_div_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_mod[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_mod x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_mod_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_decimal_div[local]:
  ∀ x y d ty sa. ci_mono sa (SND (compile_safe_decimal_div x y d ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_decimal_div_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_pow[local]:
  ∀ x y ty base_literal exp_literal sa.
    ci_mono sa
      (SND (compile_safe_pow x y ty base_literal exp_literal sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_pow_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_compile_clamp ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_compare[local]:
  ∀ op x y ty sa. ci_mono sa (SND (compile_compare op x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_compare_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_inst ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_neg_helper[local]:
  ∀ v ty sa. ci_mono sa (SND (compile_neg v ty sa))
Proof
  rpt gen_tac >> simp[Once compile_neg_def, LET_THM, pairTheory.UNCURRY] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_builtin_abs[local]:
  ∀ val_op sa. ci_mono sa (SND (compile_builtin_abs val_op sa))
Proof
  rpt gen_tac >> simp[Once builtinSimpleTheory.compile_builtin_abs_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE irule ci_mono_compile_select ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_binop[local]:
  ∀ op x y ty base_literal exp_literal sa.
    ci_mono sa
      (SND (compile_binop op x y ty base_literal exp_literal sa))
Proof
  rpt gen_tac >> simp[Once compile_binop_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  simp[ci_mono_compile_safe_add, ci_mono_compile_safe_sub, ci_mono_compile_safe_mul, ci_mono_compile_safe_div, ci_mono_compile_safe_mod, ci_mono_compile_safe_decimal_div, ci_mono_compile_safe_pow, ci_mono_compile_compare, ci_mono_emit_op] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_wrap_truncate ORELSE irule ci_mono_compile_select ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_inst ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_bytelike_literal:
  ∀ bs max_len sa. ci_mono sa (SND (compile_bytelike_literal bs max_len sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.compile_bytelike_literal_def, LET_THM] >>
  BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >>
  conj_tac >- simp[ci_mono_compile_alloc_buffer] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >>
  conj_tac >- simp[ci_mono_emit_void] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >>
  conj_tac >- simp[ci_mono_compile_store_byte_chunks] >>
  rpt strip_tac >> simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_literal_vv[local]:
  ∀ ty l sa. ci_mono sa (SND (compile_literal_vv ty l sa))
Proof
  rpt gen_tac >> Cases_on `l`
  >~ [`BoolL b`] >- (Cases_on `b` >>
      simp[exprLoweringTheory.compile_literal_vv_def, ci_mono_comp_return])
  >~ [`IntL n`] >- simp[exprLoweringTheory.compile_literal_vv_def, ci_mono_comp_return]
  >~ [`DecimalL n`] >- simp[exprLoweringTheory.compile_literal_vv_def, ci_mono_comp_return]
  >~ [`StringL s`] >- (simp[exprLoweringTheory.compile_literal_vv_def] >>
      irule ci_mono_bind >>
      simp[ci_mono_comp_return, ci_mono_compile_bytelike_literal])
  >> Cases_on `ty` >>
  simp[exprLoweringTheory.compile_literal_vv_def, ci_mono_comp_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[ci_mono_comp_return] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[ci_mono_comp_return] >>
  irule ci_mono_bind >>
  simp[ci_mono_comp_return, ci_mono_compile_bytelike_literal]
QED

Theorem ci_mono_compile_name_vv[local]:
  ∀ cenv ty id sa. ci_mono sa (SND (compile_name_vv cenv ty id sa))
Proof
  rpt gen_tac >>
  simp[exprLoweringTheory.compile_name_vv_def] >>
  BasicProvers.every_case_tac >>
  simp[ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_ignore_bind >> simp[ci_mono_comp_return, ci_mono_emit_inst]
QED

Theorem ci_mono_compile_blockhash[local]:
  ∀ n_op sa. ci_mono sa (SND (compile_blockhash n_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_blockhash_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem ci_mono_compile_blobhash[local]:
  ∀ n_op sa. ci_mono sa (SND (compile_blobhash n_op sa))
Proof
  simp[builtinMiscTheory.compile_blobhash_def, ci_mono_emit_op]
QED

Theorem ci_mono_compile_addmod[local]:
  ∀ a b c sa. ci_mono sa (SND (compile_addmod a b c sa))
Proof
  rpt gen_tac >>
  simp[builtinMathTheory.compile_addmod_def] >>
  irule ci_mono_ignore_bind >> simp[ci_mono_emit_void, ci_mono_emit_op]
QED

Theorem ci_mono_compile_mulmod[local]:
  ∀ a b c sa. ci_mono sa (SND (compile_mulmod a b c sa))
Proof
  rpt gen_tac >>
  simp[builtinMathTheory.compile_mulmod_def] >>
  irule ci_mono_ignore_bind >> simp[ci_mono_emit_void, ci_mono_emit_op]
QED

Theorem ci_mono_compile_pow_mod256[local]:
  ∀ x y sa. ci_mono sa (SND (compile_pow_mod256 x y sa))
Proof
  simp[builtinMathTheory.compile_pow_mod256_def, ci_mono_emit_op]
QED


Theorem ci_mono_compile_ceil[local]:
  ∀ v d sa. ci_mono sa (SND (compile_ceil v d sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_ceil_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_compile_select]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_compile_select]
QED

Theorem ci_mono_compile_floor[local]:
  ∀ v d sa. ci_mono sa (SND (compile_floor v d sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_floor_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_compile_select]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_compile_select]
QED

Theorem ci_mono_compile_builtin_calldatasize[local]:
  ∀ sa. ci_mono sa (SND (compile_builtin_calldatasize sa))
Proof
  simp[builtinSimpleTheory.compile_builtin_calldatasize_def, ci_mono_emit_op]
QED

Theorem ci_mono_compile_builtin_len[local]:
  ∀ ic v loc sa. ci_mono sa (SND (compile_builtin_len ic v loc sa))
Proof
  simp[builtinSimpleTheory.compile_builtin_len_def, ci_mono_compile_ptr_load]
QED

Theorem ci_mono_compile_bytestring_hash[local]:
  ∀ ptr_op sa. ci_mono sa (SND (compile_bytestring_hash ptr_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.compile_bytestring_hash_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_list_membership_in[local]:
  ∀ needle ops sa. ci_mono sa (SND (compile_list_membership_in needle ops sa))
Proof
  recInduct exprLoweringTheory.compile_list_membership_in_ind >>
  rpt strip_tac >>
  simp[exprLoweringTheory.compile_list_membership_in_def, ci_mono_comp_return, ci_mono_emit_op] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[] >>
  rpt strip_tac >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_list_membership_notin[local]:
  ∀ needle ops sa. ci_mono sa (SND (compile_list_membership_notin needle ops sa))
Proof
  recInduct exprLoweringTheory.compile_list_membership_notin_ind >>
  rpt strip_tac >>
  simp[exprLoweringTheory.compile_list_membership_notin_def, ci_mono_comp_return] >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_array_membership_loop[local]:
  ∀ needle arr_op len_op elem_size offset_base load_opc is_in sa.
    ci_mono sa (SND (compile_array_membership_loop needle arr_op len_op elem_size offset_base load_opc is_in sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.compile_array_membership_loop_def, LET_THM] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
                          ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block,
                          ci_mono_comp_return]) ORELSE
       IF_CASES_TAC ORELSE gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
       ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block,
       ci_mono_comp_return]
QED

Theorem ci_mono_compile_var_array_membership[local]:
  ∀ cenv needle arr_vv rhs_ty is_in sa. ci_mono sa (SND (compile_var_array_membership cenv needle arr_vv rhs_ty is_in sa))
Proof
  rpt gen_tac >>
  simp[exprLoweringTheory.compile_var_array_membership_def, LET_THM] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[] >- simp[ci_mono_emit_op] >> Cases_on `rhs_ty` >> simp[ci_mono_comp_return] >> rename1 `ArrayT _ sz` >> Cases_on `sz` >> simp[ci_mono_comp_return]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[] >- (Cases_on `rhs_ty` >> simp[ci_mono_comp_return] >> rename1 `ArrayT _ sz` >> Cases_on `sz` >> simp[ci_mono_comp_return] >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> simp[ci_mono_emit_op]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> simp[ci_mono_emit_op]) >> rpt strip_tac >> simp[ci_mono_emit_inst]) >> simp[ci_mono_comp_return]) >> rpt strip_tac >> simp[ci_mono_compile_array_membership_loop]
QED

Theorem ci_mono_compile_keccak256_bytes[local]:
  ∀ ptr_op sa. ci_mono sa (SND (compile_keccak256_bytes ptr_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_keccak256_bytes_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_keccak256_bytesm[local]:
  ∀ val_op m sa. ci_mono sa (SND (compile_keccak256_bytesm val_op m sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_keccak256_bytesm_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_keccak256_word[local]:
  ∀ val_op sa. ci_mono sa (SND (compile_keccak256_word val_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_keccak256_word_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_method_id_hash:
  ∀ ty v sa. ci_mono sa (SND (compile_method_id_hash ty v sa))
Proof
  ho_match_mp_tac builtinHashingTheory.compile_method_id_hash_ind >>
  simp[builtinHashingTheory.compile_method_id_hash_def,
       ci_mono_compile_keccak256_bytes, ci_mono_compile_keccak256_bytesm]
QED

Theorem ci_mono_compile_method_id_runtime[local]:
  ∀ ty v b sa. ci_mono sa (SND (compile_method_id_runtime ty v b sa))
Proof
  rpt gen_tac >> Cases_on `b` >>
  rewrite_tac[builtinHashingTheory.compile_method_id_runtime_def, COND_CLAUSES] >>
  BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
                         ci_mono_compile_alloc_buffer, ci_mono_compile_method_id_hash]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
       ci_mono_compile_alloc_buffer, ci_mono_compile_method_id_hash]
QED

Theorem ci_mono_compile_sha256_bytes[local]:
  ∀ ptr_op sa. ci_mono sa (SND (compile_sha256_bytes ptr_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_sha256_bytes_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_sha256_bytesm[local]:
  ∀ val_op m sa. ci_mono sa (SND (compile_sha256_bytesm val_op m sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_sha256_bytesm_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_sha256_word[local]:
  ∀ val_op sa. ci_mono sa (SND (compile_sha256_word val_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_sha256_word_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_ecrecover[local]:
  ∀ hash_op v_op r_op s_op sa. ci_mono sa (SND (compile_ecrecover hash_op v_op r_op s_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_ecrecover_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_ecadd[local]:
  ∀ x1 y1 x2 y2 sa. ci_mono sa (SND (compile_ecadd x1 y1 x2 y2 sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_ecadd_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_ecmul[local]:
  ∀ x y scalar sa. ci_mono sa (SND (compile_ecmul x y scalar sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_ecmul_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_assert_slice_bounds[local]:
  ∀ start_op len_op src_len sa. ci_mono sa (SND (compile_assert_slice_bounds start_op len_op src_len sa))
Proof
  rpt gen_tac >> simp[builtinBytesTheory.compile_assert_slice_bounds_def] >> rpt (CHANGED_TAC (rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE conj_tac ORELSE gen_tac) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]))
QED

Theorem ci_mono_compile_bytestring_src:
  ∀ src_ptr sa. ci_mono sa (SND (compile_bytestring_src src_ptr sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_bytestring_src_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]) ORELSE
       gen_tac ORELSE strip_tac ORELSE CASE_TAC) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]
QED

Theorem ci_mono_compile_slice_data[local]:
  ∀ src_len src_data start_op len_op out_size sa. ci_mono sa (SND (compile_slice_data src_len src_data start_op len_op out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_data_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]) ORELSE
       gen_tac ORELSE strip_tac ORELSE CASE_TAC) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]
QED

Theorem ci_mono_compile_slice_out_buf[local]:
  ∀ out_size sa. ci_mono sa (SND (compile_slice_out_buf out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_out_buf_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]) ORELSE
       gen_tac ORELSE strip_tac ORELSE CASE_TAC) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]
QED

Theorem ci_mono_compile_slice_calldata[local]:
  ∀ start_op len_op out_size sa. ci_mono sa (SND (compile_slice_calldata start_op len_op out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_calldata_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds, ci_mono_compile_slice_out_buf]) ORELSE
       gen_tac ORELSE strip_tac ORELSE CASE_TAC ORELSE
       (Cases_on `av` >> rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC)) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds, ci_mono_compile_slice_out_buf]
QED

Theorem ci_mono_compile_slice_code[local]:
  ∀ start_op len_op out_size sa. ci_mono sa (SND (compile_slice_code start_op len_op out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_code_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds, ci_mono_compile_slice_out_buf]) ORELSE
       gen_tac ORELSE strip_tac ORELSE CASE_TAC ORELSE
       (Cases_on `av` >> rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC)) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds, ci_mono_compile_slice_out_buf]
QED

Theorem ci_mono_compile_slice_extcode[local]:
  ∀ addr_op start_op len_op out_buf out_data sa. ci_mono sa (SND (compile_slice_extcode addr_op start_op len_op out_buf out_data sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_extcode_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]) ORELSE
       gen_tac ORELSE strip_tac ORELSE CASE_TAC) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]
QED

Theorem ci_mono_compile_slice_memory[local]:
  ∀ src_ptr start_op len_op out_size sa. ci_mono sa (SND (compile_slice_memory src_ptr start_op len_op out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_memory_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds, ci_mono_compile_bytestring_src, ci_mono_compile_slice_data]) ORELSE
       gen_tac ORELSE strip_tac ORELSE CASE_TAC ORELSE
       (Cases_on `av` >> rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC)) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds, ci_mono_compile_bytestring_src, ci_mono_compile_slice_data]
QED

Theorem ci_mono_compile_uint2str[local]:
  ∀ val_op n_digits buf_size sa.
    ci_mono sa (SND (compile_uint2str val_op n_digits buf_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinStringsTheory.compile_uint2str_def, LET_THM] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block, ci_mono_compile_select]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block, ci_mono_compile_select]
QED

Theorem ci_mono_compile_as_wei_value_decimal[local]:
  ∀ val_op scale decimal_divisor sa. ci_mono sa (SND (compile_as_wei_value_decimal val_op scale decimal_divisor sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_as_wei_value_decimal_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_as_wei_value_int[local]:
  ∀ val_op scale is_signed sa. ci_mono sa (SND (compile_as_wei_value_int val_op scale is_signed sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_as_wei_value_int_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_load_bytestring_as_word[local]:
  ∀ v shift_opc sa. ci_mono sa (SND (load_bytestring_as_word v shift_opc sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.load_bytestring_as_word_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_type_convert[local]:
  ∀ v conv_op sa. ci_mono sa (SND (compile_type_convert v conv_op sa))
Proof
  rpt gen_tac >> Cases_on `conv_op` >>
  rewrite_tac[exprLoweringTheory.compile_type_convert_def, LET_THM] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
                          ci_mono_compile_alloc_buffer, ci_mono_load_bytestring_as_word]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
       ci_mono_compile_alloc_buffer, ci_mono_load_bytestring_as_word] >>
  TRY (pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
       rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
            (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
            gen_tac ORELSE strip_tac) >>
       simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> NO_TAC) >>
  TRY (pairarg_tac >> simp[] >>
       rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
            (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
            gen_tac ORELSE strip_tac) >>
       simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> NO_TAC) >>
  rpt (ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt gen_tac >> rpt strip_tac) >> TRY (ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac) >> simp[ci_mono_comp_return, ci_mono_emit_void]
QED

Theorem ci_mono_compile_extract32[local]:
  ∀ src_ptr start_op sa. ci_mono sa (SND (compile_extract32 src_ptr start_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_extract32_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_clamp_extract32[local]:
  ∀ val_op clamp sa. ci_mono sa (SND (compile_clamp_extract32 val_op clamp sa))
Proof
  rpt gen_tac >> Cases_on `clamp` >>
  rewrite_tac[builtinBytesTheory.compile_clamp_extract32_def, LET_THM] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_encode_static[local]:
  ∀ dst src sa. ci_mono sa (SND (compile_abi_encode_static dst src sa))
Proof
  rpt gen_tac >>
  rewrite_tac[abiEncoderTheory.compile_abi_encode_static_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_encode_static_info[local]:
  ∀ dst src info sa.
    ci_mono sa (SND (compile_abi_encode_static_info dst src info sa))
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[abiEncoderTheory.compile_abi_encode_static_info_def,
       ci_mono_compile_abi_encode_static, ci_mono_comp_return,
       ci_mono_emit_void, ci_mono_ignore_bind]
QED

Theorem ci_mono_compile_abi_encode_dyn_static_loop[local]:
  ∀ dst src info abi_sz mem_sz len_op sa.
    ci_mono sa
      (SND (compile_abi_encode_dyn_static_loop dst src info abi_sz
        mem_sz len_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[abiEncoderTheory.compile_abi_encode_dyn_static_loop_def] >>
  BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_alloc_buffer] >>
  rpt strip_tac >> simp[LET_THM] >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- simp[ci_mono_emit_void] >>
  rpt strip_tac >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >-
         simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
              ci_mono_compile_alloc_buffer,
              ci_mono_compile_abi_encode_static_info]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
       ci_mono_fresh_label, ci_mono_new_block, ci_mono_comp_return,
       ci_mono_compile_alloc_buffer,
       ci_mono_compile_abi_encode_static_info]
QED

Theorem ci_mono_compile_abi_zero_pad[local]:
  ∀ ptr length count sa. ci_mono sa (SND (compile_abi_zero_pad ptr length count sa))
Proof
  rpt gen_tac >>
  rewrite_tac[abiEncoderTheory.compile_abi_zero_pad_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_int_clamp[local]:
  ∀ val_op bits is_signed sa. ci_mono sa (SND (compile_abi_int_clamp val_op bits is_signed sa))
Proof
  rpt gen_tac >> simp[abiEncoderTheory.compile_abi_int_clamp_def, LET_THM] >> BETA_TAC >> IF_CASES_TAC >> (ho_match_mp_tac ci_mono_ignore_bind ORELSE ho_match_mp_tac ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_bind, ci_mono_ignore_bind]
QED

Theorem ci_mono_compile_abi_bytes_clamp[local]:
  ∀ val_op m sa. ci_mono sa (SND (compile_abi_bytes_clamp val_op m sa))
Proof
  rpt gen_tac >> simp[abiEncoderTheory.compile_abi_bytes_clamp_def, LET_THM] >> BETA_TAC >> rpt (rpt gen_tac >> (ho_match_mp_tac ci_mono_ignore_bind ORELSE ho_match_mp_tac ci_mono_bind) >> conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_clamp_basetype[local]:
  ∀ val_op clamp sa. ci_mono sa (SND (compile_abi_clamp_basetype val_op clamp sa))
Proof
  Cases_on `clamp` >> simp[abiEncoderTheory.compile_abi_clamp_basetype_def, ci_mono_comp_return, ci_mono_compile_abi_int_clamp, ci_mono_compile_abi_bytes_clamp] >> rpt gen_tac >> TRY (irule ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_ignore_bind >> simp[ci_mono_emit_op, ci_mono_emit_void] >> NO_TAC) >> TRY (irule ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_ignore_bind >> simp[ci_mono_emit_op, ci_mono_emit_void] >> NO_TAC) >> TRY (irule ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> rpt strip_tac >> FIRST [irule ci_mono_ignore_bind, irule ci_mono_bind] >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> rpt strip_tac >> FIRST [irule ci_mono_ignore_bind, irule ci_mono_bind] >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return])
QED

Theorem ci_mono_compile_abi_decode_static[local]:
  ∀ src_op dst_op load_opc clamp_fn sa.
    (∀ v sa'. ci_mono sa' (SND (clamp_fn v sa'))) ⇒
    ci_mono sa (SND (compile_abi_decode_static src_op dst_op load_opc clamp_fn sa))
Proof
  rpt strip_tac >> simp[abiEncoderTheory.compile_abi_decode_static_def] >> BETA_TAC >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (first_x_assum irule) >> simp[ci_mono_emit_void]
QED

Theorem ci_mono_compile_getelemptr_abi[local]:
  ∀ src_op is_dyn abi_offset load_opc sa.
    ci_mono sa (SND (compile_getelemptr_abi src_op is_dyn abi_offset load_opc sa))
Proof
  rpt gen_tac >> simp[abiEncoderTheory.compile_getelemptr_abi_def] >> BETA_TAC >> rpt IF_CASES_TAC >> gvs[] >> rpt ((irule ci_mono_ignore_bind ORELSE irule ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> rpt strip_tac) >> TRY (IF_CASES_TAC >> gvs[] >> rpt ((irule ci_mono_ignore_bind ORELSE irule ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> rpt strip_tac)) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_decode_dyn_elem_ptr[local]:
  ∀ load_opc elem_src src_data hi_op elem_abi_sz sa.
    ci_mono sa (SND (compile_abi_decode_dyn_elem_ptr load_opc elem_src src_data hi_op elem_abi_sz sa))
Proof
  rpt gen_tac >>
  rewrite_tac[abiEncoderTheory.compile_abi_decode_dyn_elem_ptr_def] >> BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_create_tuple_in_memory[local]:
  ∀ buf_op elems offset sa.
    ci_mono sa (SND (compile_create_tuple_in_memory buf_op elems offset sa))
Proof
  ho_match_mp_tac builtinAbiTheory.compile_create_tuple_in_memory_ind >>
  rpt strip_tac
  >- simp[builtinAbiTheory.compile_create_tuple_in_memory_def, ci_mono_comp_return]
  >> rewrite_tac[builtinAbiTheory.compile_create_tuple_in_memory_def] >> BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_emit_op]
  >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[ci_mono_emit_void])
  >> rpt strip_tac >> first_x_assum irule
QED

Theorem ci_mono_compile_extcodesize_check[local]:
  ∀ addr_op sa. ci_mono sa (SND (compile_extcodesize_check addr_op sa))
Proof
  rpt gen_tac >> simp[exprLoweringTheory.compile_extcodesize_check_def] >> BETA_TAC >> irule ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem ci_mono_compile_return_value_decode:
  ∀ buf_op min_sz max_sz sa.
    ci_mono sa (SND (compile_return_value_decode buf_op min_sz max_sz sa))
Proof
  rpt gen_tac >> once_rewrite_tac[exprLoweringTheory.compile_return_value_decode_def] >> BETA_TAC >> rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >> conj_tac >| [rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_select], all_tac]) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_select]
QED

(* Reuse ci_mono_typed_memory_family and ci_mono_compile_store_memory above
   for both aggregate construction and external-call default materialization. *)
Theorem ci_mono_compile_materialize_vv[local]:
  ∀cenv ty vv sa. ci_mono sa (SND (compile_materialize_vv cenv ty vv sa))
Proof
  rpt gen_tac >> rewrite_tac[compile_materialize_vv_def] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_alloc_buffer] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_unwrap_value] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- simp[ci_mono_compile_store_memory] >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_encode_child_branches[local]:
  (¬is_dyn ⇒ ∀dst sa.
     ci_mono sa (SND (compile_abi_encode_to_buf dst child_ptr child_info sa))) ⇒
  (is_dyn ⇒ ∀dst sa.
     ci_mono sa (SND (compile_abi_encode_to_buf dst child_ptr child_info sa))) ⇒
  ∀dst static_ofst dyn_ofst_ptr sa.
    ci_mono sa (SND (compile_abi_encode_child dst child_ptr child_info
      is_dyn static_ofst dyn_ofst_ptr sa))
Proof
  rpt strip_tac >>
  simp[Once abiEncoderTheory.compile_abi_encode_child_def] >>
  ho_match_mp_tac ci_mono_bind >>
  conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >> Cases_on `is_dyn` >> gvs[]
  >- (rpt (ho_match_mp_tac ci_mono_bind ORELSE
           ho_match_mp_tac ci_mono_ignore_bind ORELSE
           (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void,
                             ci_mono_comp_return]) ORELSE
           gen_tac ORELSE strip_tac) >>
      simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >>
      first_x_assum irule >> simp[])
QED

(* Helper: the unfolded child body produced by the mutual induction rule. *)
Theorem ci_mono_compile_abi_encode_child_body[local]:
  (∀dst. ¬is_dyn ⇒ ∀sa.
     ci_mono sa (SND (compile_abi_encode_to_buf dst child_ptr child_info sa))) ⇒
  (∀dst. is_dyn ⇒ ∀sa.
     ci_mono sa (SND (compile_abi_encode_to_buf dst child_ptr child_info sa))) ⇒
  ∀dst static_ofst dyn_ofst_ptr sa.
    ci_mono sa
      (SND
        (do static_loc <- emit_op ADD [dst; Lit (n2w static_ofst)];
            if ¬is_dyn then
              compile_abi_encode_to_buf static_loc child_ptr child_info
            else
              do dyn_ofst <- emit_op MLOAD [dyn_ofst_ptr];
                 child_dst <- emit_op ADD [dst; dyn_ofst];
                 child_len <-
                   compile_abi_encode_to_buf child_dst child_ptr child_info;
                 emit_void MSTORE [static_loc; dyn_ofst];
                 new_dyn <- emit_op ADD [dyn_ofst; child_len];
                 emit_void MSTORE [dyn_ofst_ptr; new_dyn];
                 comp_return child_len
              od
         od sa))
Proof
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >>
  conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >> Cases_on `is_dyn` >> gvs[]
  >- (rpt (ho_match_mp_tac ci_mono_bind ORELSE
           ho_match_mp_tac ci_mono_ignore_bind ORELSE
           (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void,
                             ci_mono_comp_return]) ORELSE
           gen_tac ORELSE strip_tac) >>
      simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >>
      first_x_assum irule >> simp[])
QED

(* Helper: premise shape emitted by compile_abi_encode_child_ind. *)
Theorem ci_mono_compile_abi_encode_child_body_ind[local]:
  (∀dst. ¬is_dyn ⇒ ∀sa.
     ci_mono sa (SND (compile_abi_encode_to_buf dst child_ptr child_info sa))) ⇒
  (∀dst. ¬¬is_dyn ⇒ ∀sa.
     ci_mono sa (SND (compile_abi_encode_to_buf dst child_ptr child_info sa))) ⇒
  ∀dst static_ofst dyn_ofst_ptr sa.
    ci_mono sa
      (SND
        (do static_loc <- emit_op ADD [dst; Lit (n2w static_ofst)];
            if ¬is_dyn then
              compile_abi_encode_to_buf static_loc child_ptr child_info
            else
              do dyn_ofst <- emit_op MLOAD [dyn_ofst_ptr];
                 child_dst <- emit_op ADD [dst; dyn_ofst];
                 child_len <-
                   compile_abi_encode_to_buf child_dst child_ptr child_info;
                 emit_void MSTORE [static_loc; dyn_ofst];
                 new_dyn <- emit_op ADD [dyn_ofst; child_len];
                 emit_void MSTORE [dyn_ofst_ptr; new_dyn];
                 comp_return child_len
              od
         od sa))
Proof
  rpt strip_tac >>
  irule ci_mono_compile_abi_encode_child_body >>
  simp[]
QED

Theorem ci_mono_compile_abi_encode_complex_step[local]:
  (∀child_ptr sa.
     ci_mono sa (SND (compile_abi_encode_child dst child_ptr child_info
       is_dyn head_offset dyn_ptr sa))) ⇒
  (∀sa. ci_mono sa
     (SND (compile_abi_encode_complex_elems dst src elems
       (src_offset + mem_sz) (head_offset + abi_sz) dyn_ptr sa))) ⇒
  ∀sa. ci_mono sa
    (SND
      (do elem_src <- emit_op ADD [src; Lit (n2w src_offset)];
          compile_abi_encode_child dst elem_src child_info is_dyn
            head_offset dyn_ptr;
          compile_abi_encode_complex_elems dst src elems
            (mem_sz + src_offset) (abi_sz + head_offset) dyn_ptr
       od sa))
Proof
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (first_x_assum irule) >>
  rpt strip_tac >>
  last_x_assum (qspec_then `sa` mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem ci_mono_compile_abi_encode:
  (∀ dst child_ptr child_info is_dyn static_ofst dyn_ofst_ptr sa.
    ci_mono sa (SND (compile_abi_encode_child dst child_ptr child_info is_dyn static_ofst dyn_ofst_ptr sa))) ∧
  (∀ dst src info sa.
    ci_mono sa (SND (compile_abi_encode_to_buf dst src info sa))) ∧
  (∀ dst src elems src_offset head_offset dyn_ptr sa.
    ci_mono sa (SND (compile_abi_encode_complex_elems dst src elems src_offset head_offset dyn_ptr sa))) ∧
  (∀ dst src elem_info elem_abi_sz elem_mem_sz len_op sa.
    ci_mono sa (SND (compile_abi_encode_dyn_loop dst src elem_info elem_abi_sz elem_mem_sz len_op sa)))
Proof
  ho_match_mp_tac abiEncoderTheory.compile_abi_encode_child_ind >>
  (* Keep the child case isolated so its branch-specific induction hypotheses
     are not mixed with the other nine mutual-recursion cases. *)
  conj_tac >- (
    rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
    simp[Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
    rpt strip_tac >>
    ho_match_mp_tac ci_mono_bind >>
    conj_tac >- simp[ci_mono_emit_op] >>
    rpt strip_tac >> Cases_on `is_dyn` >> gvs[]
    >- (rpt (ho_match_mp_tac ci_mono_bind ORELSE
             ho_match_mp_tac ci_mono_ignore_bind ORELSE
             (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void,
                               ci_mono_comp_return]) ORELSE
             gen_tac ORELSE strip_tac) >>
        simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >>
        first_x_assum irule >> simp[])) >>
  (* AbiPrimWord / static word copy. *)
  conj_tac >- (
    rpt gen_tac >>
    simp[Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM,
         ci_mono_compile_abi_encode_static]) >>
  (* AbiBytestring. *)
  conj_tac >- (
    rpt gen_tac >>
    simp[Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
    rpt (ho_match_mp_tac ci_mono_bind ORELSE
         ho_match_mp_tac ci_mono_ignore_bind ORELSE
         (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void,
                           ci_mono_comp_return]) ORELSE
         gen_tac ORELSE strip_tac) >>
    simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) >>
  (* AbiCopy. *)
  conj_tac >- (
    rpt gen_tac >>
    simp[Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
    ho_match_mp_tac ci_mono_ignore_bind >>
    conj_tac >- simp[ci_mono_emit_void] >>
    rpt strip_tac >> simp[ci_mono_comp_return]) >>
  (* AbiDynArray. *)
  conj_tac >- (
    rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
    simp[Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
    rpt strip_tac >>
    ho_match_mp_tac ci_mono_bind >>
    conj_tac >- simp[ci_mono_compile_alloc_buffer] >>
    rpt strip_tac >> simp[LET_THM] >>
    ho_match_mp_tac ci_mono_ignore_bind >>
    conj_tac >- simp[ci_mono_emit_void] >>
    rpt strip_tac >>
    ho_match_mp_tac ci_mono_bind >>
    conj_tac >- simp[ci_mono_emit_op] >>
    rpt strip_tac >>
    ho_match_mp_tac ci_mono_ignore_bind >>
    conj_tac >- simp[ci_mono_emit_void] >>
    rpt strip_tac >>
    ho_match_mp_tac ci_mono_bind >>
    conj_tac >- (
      IF_CASES_TAC >> gvs[]
      >- simp[ci_mono_compile_abi_encode_dyn_static_loop]
      >> rpt strip_tac >>
         ho_match_mp_tac ci_mono_bind >>
         conj_tac >- simp[ci_mono_emit_op] >>
         rpt strip_tac >> first_x_assum irule) >>
    rpt strip_tac >>
    rpt (ho_match_mp_tac ci_mono_bind ORELSE
         ho_match_mp_tac ci_mono_ignore_bind ORELSE
         (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void]) ORELSE
         gen_tac ORELSE strip_tac) >>
    simp[ci_mono_emit_op, ci_mono_emit_void]) >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  simp[Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
  let
    val base = [ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
                ci_mono_compile_alloc_buffer, ci_mono_compile_abi_encode_static,
                ci_mono_compile_abi_encode_static_info,
                ci_mono_compile_abi_encode_dyn_static_loop,
                ci_mono_compile_abi_zero_pad, ci_mono_fresh_label, ci_mono_new_block,
                ci_mono_emit_inst, ci_mono_fresh_var]
    val solve1 = rpt strip_tac >> simp base >> TRY (first_x_assum irule >> simp[])
    val decomp =
      rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
           (conj_tac >- solve1) ORELSE gen_tac ORELSE strip_tac)
    val finish = simp base >> TRY (first_x_assum irule >> simp[])
  in
    rpt strip_tac >>
    (* Complex-element recursion with the child call already opaque. *)
    TRY (
      irule ci_mono_compile_abi_encode_complex_step >>
      simp[] >> NO_TAC) >>
    (* First try: decompose directly *)
    TRY (decomp >> finish >> NO_TAC) >>
    (* Second try: IF_CASES_TAC then decompose each branch *)
    TRY (IF_CASES_TAC >> gvs[] >> decomp >> finish >> NO_TAC) >>
    (* Third try: nested IF_CASES_TAC *)
    TRY (IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >> decomp >> finish >> NO_TAC) >>
    (* compile_abi_encode_child: after materializing static_loc, select the
       induction hypothesis specialized to the static or dynamic branch. *)
    TRY (
      ho_match_mp_tac ci_mono_bind >> conj_tac >- simp base >>
      rpt strip_tac >> IF_CASES_TAC >> gvs[]
      >- (first_x_assum irule >> simp[])
      >- (decomp >> finish) >>
      NO_TAC) >>
    (* compile_abi_encode_complex_elems cons case: goal is
       do elem_src <- ..; <compile_abi_encode_child inlined>; complex_elems od
       Decompose as bind(elem_src, ignore_bind(child, complex_elems)) *)
    TRY (
      ho_match_mp_tac ci_mono_bind >> conj_tac >-
        (IF_CASES_TAC >> gvs[] >> simp base) >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (
        (* The inner do..od is compile_abi_encode_child with args inlined.
           We have IH: ∀child_ptr sa. ci_mono sa (SND (compile_abi_encode_child ...))
           But the goal is the inlined body, not the opaque call.
           Rewrite backwards with compile_abi_encode_child_def to fold it back. *)
        IF_CASES_TAC >> gvs[] >> decomp >> finish) >>
      rpt strip_tac >> first_x_assum irule >> NO_TAC) >>
    (* compile_abi_encode_complex_elems cons case:
       bind(elem_src, ignore_bind(child_inlined, complex_elems))
       The child call is inlined (compile_abi_encode_child expanded).
       We fold it back using once_rewrite_tac then use IH. *)
    TRY (
      ho_match_mp_tac ci_mono_bind >> conj_tac >-
        (IF_CASES_TAC >> gvs[] >> simp base) >>
      rpt strip_tac >>
      once_rewrite_tac[GSYM abiEncoderTheory.compile_abi_encode_child_def] >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >-
        (first_x_assum irule) >>
      rpt strip_tac >> first_x_assum irule >> NO_TAC) >>
    (* The only non-generic residual is compile_abi_encode_to_buf for a
       dynamic array.  Decompose its parent-offset cell explicitly. *)
    TRY (ACCEPT_TAC (Q.SPECL [`dst`, `src`, `sa`]
      ci_mono_compile_abi_encode_static)) >>
    TRY (irule ci_mono_compile_abi_encode_static_info) >>
    TRY (irule ci_mono_compile_abi_encode_dyn_static_loop) >>
    finish >>
    (ho_match_mp_tac ci_mono_bind >> conj_tac >- simp base >>
     rpt strip_tac >> simp[LET_THM] >>
     ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp base >>
     rpt strip_tac >>
     ho_match_mp_tac ci_mono_bind >> conj_tac >- simp base >>
     rpt strip_tac >>
     ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp base >>
     rpt strip_tac >>
     ho_match_mp_tac ci_mono_bind >> conj_tac >-
       (IF_CASES_TAC >> gvs[]
        >- simp[ci_mono_compile_abi_encode_dyn_static_loop]
        >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp base >>
           rpt strip_tac >> first_x_assum irule) >>
     rpt strip_tac >> decomp >> finish)
  end
QED

Theorem ci_mono_compile_abi_decode_bytes_bound[local]:
  ∀src_op hi_op len_op sa.
    ci_mono sa
      (SND
        ((if hi_op = Lit 0w then return ()
          else
            do data_start <- emit_op ADD [src_op; Lit 32w];
               data_end <- emit_op ADD [data_start; len_op];
               oob <- emit_op GT [data_end; hi_op];
               ok2 <- emit_op ISZERO [oob];
               emit_void ASSERT [ok2]
            od) sa))
Proof
  rpt gen_tac >> IF_CASES_TAC >- simp[ci_mono_comp_return] >>
  ntac 4 (ho_match_mp_tac ci_mono_bind >>
    conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac) >>
  simp[ci_mono_emit_void]
QED

Theorem ci_mono_compile_abi_decode:
  (∀ dst src_op load_opc hi_op info sa.
    ci_mono sa (SND (compile_abi_decode_to_buf dst src_op load_opc hi_op info sa))) ∧
  (∀ dst src_op load_opc hi_op elems abi_offset vyper_offset sa.
    ci_mono sa (SND (compile_abi_decode_complex_elems dst src_op load_opc hi_op elems abi_offset vyper_offset sa))) ∧
  (∀ dst src_op load_opc hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt sa.
    ci_mono sa (SND (compile_abi_decode_dyn_loop dst src_op load_opc hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt sa)))
Proof
  let
    val [c0,c1,c2,c3,c4,c5,c6] = CONJUNCTS abiEncoderTheory.compile_abi_decode_to_buf_def
    val db = fn t => ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[t] >> rpt strip_tac
    val dib = fn t => ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[t] >> rpt strip_tac
    val decode_ind = BETA_RULE (ISPECL
      [``λdst src_op load_opc hi_op info.
           ∀sa. ci_mono sa
             (SND (compile_abi_decode_to_buf dst src_op load_opc hi_op info sa))``,
       ``λdst src_op load_opc hi_op elems abi_offset vyper_offset.
           ∀sa. ci_mono sa
             (SND (compile_abi_decode_complex_elems dst src_op load_opc hi_op
               elems abi_offset vyper_offset sa))``,
       ``λdst src_op load_opc hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt.
           ∀sa. ci_mono sa
             (SND (compile_abi_decode_dyn_loop dst src_op load_opc hi_op
               elem_info elem_abi_sz elem_mem_sz i_ptr cnt sa))``]
      abiEncoderTheory.compile_abi_decode_to_buf_ind)
    val decode_prem = fst (dest_imp (concl decode_ind))
  in
  SUBGOAL_THEN decode_prem
    (fn prem_th => ACCEPT_TAC (MATCH_MP decode_ind prem_th)) >- (
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  (* DecPrimWord *)
  >- (rewrite_tac[c0] >> BETA_TAC >>
      irule ci_mono_compile_abi_decode_static >> simp[ci_mono_compile_abi_clamp_basetype])
  (* DecBytestring *)
  >- (rewrite_tac[c1] >>
      ntac 3 (db ci_mono_emit_op) >>
      dib ci_mono_emit_void >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
      >- (irule ci_mono_compile_abi_decode_bytes_bound) >>
      rpt strip_tac >>
      Cases_on `load_opc` >> simp[ci_mono_emit_void])
  (* DecDynArray *)
  >- (rpt strip_tac >> rewrite_tac[c2] >> BETA_TAC >>
      ntac 3 (db ci_mono_emit_op) >> dib ci_mono_emit_void >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (
        IF_CASES_TAC >> gvs[]
        >- simp[ci_mono_comp_return]
        >> rpt strip_tac >>
           ntac 5 (db ci_mono_emit_op) >>
           simp[ci_mono_emit_void]) >>
      rpt strip_tac >>
      db ci_mono_emit_op >> dib ci_mono_emit_void >>
      simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
      >- (ntac 3 (db ci_mono_emit_op) >>
          Cases_on `load_opc` >> simp[ci_mono_emit_void])
      >> db ci_mono_compile_alloc_buffer >> dib ci_mono_emit_void >>
      first_x_assum irule >> simp[])
  (* DecComplex *)
  >- (rpt strip_tac >> rewrite_tac[c3] >>
      simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
      >- (qpat_x_assum `∀static_sz. _ ∧ hi_op = Lit 0w ⇒ _`
            (qspec_then `FOLDR (λ(_0,abi_sz,_1) acc. abi_sz + acc) 0 elems` mp_tac) >>
          simp[]) >>
      ntac 3 (db ci_mono_emit_op) >> dib ci_mono_emit_void >>
      qpat_x_assum `∀static_sz. _ ∧ hi_op ≠ Lit 0w ⇒ _`
        (qspec_then `FOLDR (λ(_0,abi_sz,_1) acc. abi_sz + acc) 0 elems` mp_tac) >>
      simp[])
  (* complex_elems nil *)
  >- (rewrite_tac[c4] >> simp[ci_mono_comp_return])
  (* complex_elems cons *)
  >- (rpt strip_tac >> rewrite_tac[c5] >>
      BETA_TAC >> simp_tac pure_ss [LET_THM] >> BETA_TAC >>
      db ci_mono_compile_getelemptr_abi >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[ci_mono_emit_op] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
      >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
      rpt strip_tac >>
      first_x_assum (irule o SRULE[]) >> simp[])
  (* dyn_loop *)
  >> rpt strip_tac >> rewrite_tac[c6] >>
  BETA_TAC >> simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (db ci_mono_fresh_label) >>
  dib ci_mono_emit_inst >> dib ci_mono_new_block >>
  ntac 4 (db ci_mono_emit_op) >> dib ci_mono_emit_inst >> dib ci_mono_new_block >>
  ntac 4 (db ci_mono_emit_op) >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- (
    IF_CASES_TAC >> simp[ci_mono_compile_abi_decode_dyn_elem_ptr, ci_mono_comp_return]) >>
  rpt strip_tac >> ntac 3 (db ci_mono_emit_op) >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  rpt strip_tac >>
  db ci_mono_emit_op >>
  dib ci_mono_emit_void >>
  dib ci_mono_emit_inst >>
  dib ci_mono_new_block >>
  simp[ci_mono_comp_return])
  end
QED

Theorem ci_mono_compile_default_return_path:
  ∀ cenv return_type default_ty buf_op result_op default_op addr_op skip_check
    min_return_size max_return_size ret_dec_info sa.
    ci_mono sa (SND (compile_default_return_path cenv return_type default_ty
                      buf_op result_op default_op addr_op
                      skip_check min_return_size max_return_size
                      ret_dec_info sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.compile_default_return_path_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_inst] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >-
    simp[ci_mono_compile_store_memory] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >-
    (IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_compile_extcodesize_check]) >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_inst] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_return_value_decode] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >-
    simp[cj 1 ci_mono_compile_abi_decode] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_inst] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >> rpt strip_tac >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_stage_intcall_args:
  ∀ cenv vals flags tys sa.
    ci_mono sa (SND (compile_stage_intcall_args cenv vals flags tys sa))
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt conj_tac
  >- simp[Once compile_stage_intcall_args_def, ci_mono_comp_return]
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      simp[Once compile_stage_intcall_args_def] >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[ci_mono_unwrap_value] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- (first_x_assum (fn ih => irule (SRULE [] ih))) >>
      rpt strip_tac >> simp[ci_mono_comp_return])
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      simp[Once compile_stage_intcall_args_def] >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[ci_mono_unwrap_value] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[ci_mono_compile_alloc_buffer] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
      >- (IF_CASES_TAC >> simp[ci_mono_emit_void] >>
          IF_CASES_TAC >> simp[ci_mono_emit_void] >-
            (rpt strip_tac >>
             ho_match_mp_tac ci_mono_ignore_bind >>
             simp[ci_mono_compile_store_bytestring, ci_mono_comp_return])) >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- (first_x_assum (fn ih => irule (SRULE [] ih))) >>
      rpt strip_tac >> simp[ci_mono_comp_return])
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      simp[Once compile_stage_intcall_args_def] >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[ci_mono_unwrap_value] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- (first_x_assum (fn ih => irule (SRULE [] ih))) >>
      rpt strip_tac >> simp[ci_mono_comp_return])
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      simp[Once compile_stage_intcall_args_def] >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[ci_mono_unwrap_value] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- (first_x_assum (fn ih => irule (SRULE [] ih))) >>
      rpt strip_tac >> simp[ci_mono_comp_return])
QED

Theorem ci_mono_compile_multi_vvs:
  ∀cfn cenv es sa.
    (∀cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_multi_vvs cfn cenv es sa))
Proof
  Induct_on `es` >> rpt strip_tac
  >- simp[compile_multi_vvs_def, ci_mono_comp_return] >>
  simp[Once compile_multi_vvs_def] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_ext_call_gas_opt[local]:
  ∀gas_opt sa s.
    ci_mono sa s ⇒
    ci_mono sa
      (SND (case gas_opt of NONE => emit_op GAS [] s | SOME g => (g, s)))
Proof
  Cases >> simp[] >> rpt strip_tac >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_emit_op >> fs[]
QED

Theorem ci_mono_compile_ext_call_kwarg:
  ∀cfn cenv rt k e sa.
    (∀cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_ext_call_kwarg cfn cenv rt k e sa))
Proof
  rpt strip_tac >> rewrite_tac[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC >> ho_match_mp_tac ci_mono_bind >> rpt strip_tac >> BETA_TAC
  >- fs[]
  >- (ho_match_mp_tac ci_mono_bind >>
      simp[ci_mono_compile_materialize_vv, ci_mono_comp_return])
  >- (irule ci_mono_lower_value_cfn >> fs[]) >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_ext_call_kwargs[local]:
  ∀ks es cfn cenv rt sa.
    (∀cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_ext_call_kwargs cfn cenv rt ks es sa))
Proof
  Induct >> Cases_on `es` >> rpt strip_tac >>
  simp[compile_ext_call_kwargs_def, ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> irule ci_mono_compile_ext_call_kwarg >> fs[]) >>
  rpt strip_tac >> simp[pairTheory.UNCURRY] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[pairTheory.UNCURRY, ci_mono_comp_return]
QED

Theorem ci_mono_compile_extcall_store_values[local]:
  ∀cenv vals buf_op offset sa.
    ci_mono sa
      (SND (compile_extcall_store_values cenv vals buf_op offset sa))
Proof
  Induct_on `vals` >> rpt gen_tac
  >- simp[compile_extcall_store_values_def, ci_mono_comp_return] >>
  PairCases_on `h` >>
  simp[Once compile_extcall_store_values_def, LET_THM] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_unwrap_value] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >>
      simp[ci_mono_emit_void, ci_mono_compile_store_bytestring] >>
      IF_CASES_TAC >>
      simp[ci_mono_emit_void, ci_mono_compile_store_bytestring]) >>
  rpt strip_tac >> first_x_assum irule
QED

Theorem ci_mono_compile_extcall_store_args[local]:
  ∀ cfn cenv es tys buf_op offset sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_extcall_store_args cfn cenv es tys buf_op offset sa))
Proof
  ntac 7 gen_tac >> strip_tac >>
  MAP_EVERY qid_spec_tac [`sa`, `offset`, `buf_op`, `tys`, `es`, `cenv`] >>
  Induct_on `es`
  >- simp[compile_extcall_store_args_def, ci_mono_comp_return]
  >> rpt gen_tac >> Cases_on `tys`
  >> simp[Once compile_extcall_store_args_def, LET_THM]
  >> (ho_match_mp_tac ci_mono_bind >> conj_tac
      >- (rpt strip_tac >> irule ci_mono_lower_value_cfn >> metis_tac[])
      >> rpt strip_tac >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- (rpt strip_tac >> IF_CASES_TAC >>
          simp[ci_mono_comp_return, ci_mono_emit_op])
      >> rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
      >- (rpt strip_tac >> TRY IF_CASES_TAC >>
          simp[ci_mono_emit_void] >>
          TRY IF_CASES_TAC >>
          simp[ci_mono_compile_store_bytestring, ci_mono_emit_void])
      >> rpt strip_tac >> first_x_assum irule)
QED

Theorem ci_mono_compile_external_call_kwargs[local]:
  ∀ cenv addr_op arg_vals arg_types args_mem_size args_abi_size method_id_val
    return_abi_size min_return_size ret_mem_bytes
    use_staticcall call_value gas_op
    skip_check has_default default_op
    return_type default_ty
    args_enc_info ret_dec_info sa.
    ci_mono sa
      (SND (compile_external_call_kwargs cenv addr_op arg_vals arg_types
        args_mem_size args_abi_size method_id_val return_abi_size
        min_return_size ret_mem_bytes use_staticcall call_value gas_op
        skip_check has_default default_op return_type default_ty args_enc_info
        ret_dec_info sa))
Proof
  rpt gen_tac >> simp[compile_external_call_kwargs_def, LET_THM] >> BETA_TAC >> irule ci_mono_bind >> reverse conj_tac >- simp[ci_mono_compile_alloc_buffer] >> rpt strip_tac >> BETA_TAC >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >- simp[ci_mono_comp_return] >>
      rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
      >- simp[ci_mono_compile_alloc_buffer] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
      >- simp[ci_mono_compile_extcall_store_values] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
      >- simp[cj 2 ci_mono_compile_abi_encode] >>
      simp[ci_mono_comp_return]) >>
  rpt strip_tac >> irule ci_mono_bind >> simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_ignore_bind >> conj_tac >- (IF_CASES_TAC >> simp[ci_mono_compile_extcodesize_check, ci_mono_comp_return]) >>
  gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (gen_tac >> IF_CASES_TAC >> simp[ci_mono_emit_op]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >>
  conj_tac >- simp[ci_mono_fresh_label] >>
rpt strip_tac >>
irule ci_mono_bind >> simp[ci_mono_fresh_label] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> simp[ci_mono_emit_inst] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> simp[ci_mono_new_block] >>
rpt strip_tac >>
ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
rpt strip_tac >>
ho_match_mp_tac ci_mono_bind >> conj_tac
>- simp[ci_mono_compile_alloc_buffer] >>
rpt strip_tac >>
ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
>- (rpt strip_tac >>
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
    >- simp[ci_mono_emit_void] >>
    simp[ci_mono_emit_inst]) >>
rpt strip_tac >>
ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
>- simp[ci_mono_new_block] >>
rpt strip_tac >>
IF_CASES_TAC >> gvs[]
>- simp[ci_mono_comp_return]
>> IF_CASES_TAC >> gvs[]
>- (irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
    rpt strip_tac >> simp[ci_mono_compile_default_return_path])
>> irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
rpt strip_tac >>
irule ci_mono_bind >> simp[ci_mono_compile_return_value_decode] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> conj_tac
>- simp[ci_mono_compile_abi_decode]
>> simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_msg_data_to_memory:
  ∀sa. ci_mono sa (SND (compile_msg_data_to_memory sa))
Proof
  simp[compile_msg_data_to_memory_def, contextTheory.compile_alloc_dynamic_def] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_emit_op] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_emit_op] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >>
  simp[ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_raw_call[local]:
  ∀addr dp dl gas value call_ty max_outsize rof sa.
    ci_mono sa
      (SND (compile_raw_call addr dp dl gas value call_ty max_outsize rof sa))
Proof
  rpt gen_tac >> Cases_on `call_ty` >>
  simp[compile_raw_call_def, LET_THM] >>
  rpt (FIRST [
    CHANGED_TAC (simp[LET_THM, pairTheory.FORALL_PROD,
      pairTheory.UNCURRY_DEF, ci_mono_emit_op, ci_mono_emit_void,
      ci_mono_emit_inst, ci_mono_compile_alloc_buffer,
      ci_mono_fresh_label, ci_mono_new_block, ci_mono_compile_select,
      ci_mono_comp_return]),
    gen_tac,
    ho_match_mp_tac ci_mono_bind >> conj_tac,
    ho_match_mp_tac ci_mono_ignore_bind >> conj_tac,
    IF_CASES_TAC])
QED

Theorem ci_mono_compile_raw_call_calldata[local]:
  ∀cfn cenv ret_ty ty rcf args default_ret sa.
    (∀cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_call cfn cenv ret_ty ty
      (RawCallCalldataTarget rcf) args default_ret sa))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `args` >- simp[compile_call_def, pairTheory.UNCURRY, ci_mono_emit_inst] >>
  rename1 `addr_e::rest` >> Cases_on `rest`
  >- simp[compile_call_def, pairTheory.UNCURRY, ci_mono_emit_inst] >>
  rename1 `addr_e::value_e::tail` >> Cases_on `tail` >>
  Cases_on `rcf.rcf_max_outsize = 0` >>
  simp[compile_call_def, LET_THM, pairTheory.UNCURRY, ci_mono_emit_inst] >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_compile_raw_call >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_emit_op >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_lower_value_cfn >>
  (conj_tac >- simp[]) >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_compile_msg_data_to_memory >>
  irule ci_mono_lower_value_cfn >> simp[]
QED

(* Cache only the INVALID branches: never normalize the large IntCall /
   ExtCall bodies while speculatively closing these primitive cases. *)
val ci_mono_invalid_call_tac =
  let
    val invalid_calls = map
      (SIMP_RULE pure_ss [LET_THM, pairTheory.UNCURRY, pairTheory.SND])
      (map (fn n => cj n compile_call_def) [4, 6, 7, 8, 9])
  in
    CONV_TAC
      (RAND_CONV (RAND_CONV (FIRST_CONV (map REWR_CONV invalid_calls)))) >>
    REWRITE_TAC [pairTheory.SND] >> irule ci_mono_emit_inst
  end;

Theorem ci_mono_compile_call[local]:
  ∀ cfn cenv ret_ty ty target args default_ret sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_call cfn cenv ret_ty ty target args default_ret sa))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `target` >>
  TRY (ci_mono_invalid_call_tac >> NO_TAC) >>
  TRY (irule ci_mono_compile_raw_call_calldata >> simp[] >> NO_TAC)
  >- ( (* IntCall *)
    simp[compile_call_def, LET_THM, pairTheory.UNCURRY] >>
rpt IF_CASES_TAC >> gvs[] >>
rpt (CHANGED_TAC (
  (irule ci_mono_trans >>
   first_assum (irule_at (Pos last)) >>
   simp[ci_mono_store_multi_results, ci_mono_emit_multi_op, ci_mono_emit_op,
        ci_mono_emit_void, ci_mono_compile_stage_intcall_args,
        ci_mono_compile_alloc_buffer]) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_store_multi_results) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_emit_multi_op) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_emit_op) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_emit_void) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_compile_stage_intcall_args) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_compile_alloc_buffer) ORELSE
  (irule ci_mono_compile_multi_vvs)
)) >>
rpt strip_tac >> first_assum irule)
  >- ( (* ExtCall *)
    PairCases_on `p` >> simp[compile_call_def, LET_THM, pairTheory.UNCURRY] >>
    Cases_on `args` >> simp[ci_mono_emit_inst] >>
    rpt IF_CASES_TAC >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    rpt (CHANGED_TAC (
      (irule ci_mono_ext_call_gas_opt) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_lower_value_cfn >> simp[]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_emit_op >> simp[]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_compile_multi_vvs >> simp[]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_compile_ext_call_kwargs >> simp[]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_compile_extcall_store_args >> simp[]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_compile_alloc_buffer >> simp[]) ORELSE
      (irule ci_mono_trans >>
       first_assum (irule_at (Pos last)) >>
       simp[ci_mono_compile_alloc_buffer, ci_mono_emit_op,
            ci_mono_compile_external_call_kwargs, ci_mono_comp_return]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_compile_external_call_kwargs) ORELSE
      (irule ci_mono_lower_value_cfn >> simp[]) ORELSE
      (irule ci_mono_compile_multi_vvs >> simp[]) ORELSE
      (irule ci_mono_compile_extcall_store_args >> simp[])
    )) >>
    gvs[] >> rpt strip_tac >>
    TRY (first_assum irule >> NO_TAC) >>
    TRY (irule ci_mono_refl >> NO_TAC) >>
    simp[ci_mono_emit_inst, ci_mono_comp_return, ci_mono_refl])
  >> (* Send *)
  simp[Once compile_call_def, LET_THM] >>
  Cases_on `args` >> simp[pairTheory.UNCURRY, ci_mono_emit_inst] >>
  Cases_on `t` >> simp[pairTheory.UNCURRY, ci_mono_emit_inst] >>
  IF_CASES_TAC >> simp[pairTheory.UNCURRY, ci_mono_emit_inst] >>
  qpat_x_assum `LENGTH _ = _` mp_tac >>
  rename1 `LENGTH gas_es = if has_gas then _ else _` >> strip_tac >>
  `gas_es = [] \/ ?gas_e. gas_es = [gas_e]` by
    (Cases_on `has_gas` >> gvs[listTheory.LENGTH_EQ_NUM_compute]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_emit_void >> irule ci_mono_trans >> irule_at (Pos last) ci_mono_emit_op >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_lower_value_cfn >> (conj_tac >- simp[]) >>
  TRY (irule ci_mono_lower_value_cfn >> simp[] >> NO_TAC) >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_lower_value_cfn >> (conj_tac >- simp[]) >>
  irule ci_mono_lower_value_cfn >> simp[]
QED

(* Guarded callbacks preserve monotonicity even on invalid child calls. *)
Theorem ci_mono_invalid_expr_call[local]:
  ci_mono st (SND (invalid_expr_call ty st))
Proof
  simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM, pairTheory.UNCURRY,
       ci_mono_emit_inst]
QED

Theorem ci_mono_expr_child_callback:
  (∀ce ty e st. expr_size e < bound ⇒
    ci_mono st (SND (f ce ty e st))) ⇒
  (∀ce ty e st.
    ci_mono st (SND (expr_child_callback bound f ce ty e st)))
Proof
  rpt strip_tac >> simp[exprCallBoundsTheory.expr_child_callback_def] >>
  IF_CASES_TAC >> simp[ci_mono_invalid_expr_call]
QED

Theorem ci_mono_builtin_child_callback[local]:
  (∀ce ret_ty ty bi args st. list_size expr_size args < bound ⇒
    ci_mono st (SND (f ce ret_ty ty bi args st))) ⇒
  (∀ce ret_ty ty bi args st.
    ci_mono st (SND (builtin_child_callback bound f ce ret_ty ty bi args st)))
Proof
  rpt strip_tac >> simp[exprCallBoundsTheory.builtin_child_callback_def] >>
  IF_CASES_TAC >> simp[ci_mono_invalid_expr_call]
QED

Theorem ci_mono_type_child_callback[local]:
  (∀ce vv_ty ty tb ret_ty args st. list_size expr_size args < bound ⇒
    ci_mono st (SND (f ce vv_ty ty tb ret_ty args st))) ⇒
  (∀ce vv_ty ty tb ret_ty args st.
    ci_mono st (SND (type_child_callback bound f ce vv_ty ty tb ret_ty args st)))
Proof
  rpt strip_tac >> simp[exprCallBoundsTheory.type_child_callback_def] >>
  IF_CASES_TAC >> simp[ci_mono_invalid_expr_call]
QED

(* Paired sequencing interface for the body definitions' explicit lets. *)
Theorem ci_mono_uncurry[local]:
  (∀s. ci_mono s (SND (m s))) ∧
  (∀a s. ci_mono s (SND (k a s))) ⇒
  ci_mono st (SND (UNCURRY k (m st)))
Proof
  strip_tac >>
  qspecl_then [`m`, `k`, `st`] mp_tac ci_mono_bind >>
  simp[comp_bind_def, LET_THM, pairTheory.UNCURRY]
QED

Theorem ci_mono_compile_expr_ifexp[local]:
  (∀ce ty e s. ci_mono s (SND (f ce ty e s))) ⇒
  ci_mono st (SND (compile_expr_body f g h cenv ty
    (IfExp ann cond_e then_e else_e) st))
Proof
  strip_tac >> simp[compile_expr_body_def, LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn, ci_mono_fresh_var,
               ci_mono_fresh_label, ci_mono_emit_inst, ci_mono_new_block]
       >> rpt gen_tac >> BETA_TAC) >>
  IF_CASES_TAC >> simp[ci_mono_refl]
QED

Theorem ci_mono_compile_expr_structlit[local]:
  (∀ce ty e s. ci_mono s (SND (f ce ty e s))) ⇒
  ci_mono st (SND (compile_expr_body f g h cenv ty
    (StructLit ann name fields) st))
Proof
  strip_tac >> simp[compile_expr_body_def, LET_THM] >>
  irule ci_mono_uncurry >> reverse conj_tac
  >- simp[ci_mono_compile_alloc_buffer]
  >> rpt gen_tac >> BETA_TAC >>
  irule ci_mono_uncurry >> reverse conj_tac
  >- simp[ci_mono_compile_struct_lit_cfn]
  >> simp[ci_mono_refl]
QED

Theorem ci_mono_compile_expr_toplevelname[local]:
  ci_mono st (SND (compile_expr_body f g h cenv ty
    (TopLevelName ann nsid) st))
Proof
  simp[compile_expr_body_def, LET_THM] >>
  Cases_on `FLOOKUP cenv.ce_vars (module_var_key nsid)`
  >- (simp[] >> irule ci_mono_uncurry >> simp[ci_mono_emit_inst, ci_mono_refl])
  >> rename1 `SOME loc` >> Cases_on `loc` >>
  simp[ci_mono_refl] >>
  irule ci_mono_uncurry >> simp[ci_mono_emit_inst, ci_mono_refl]
QED

Theorem ci_mono_compile_expr_pop[local]:
  ci_mono st (SND (compile_expr_body f g h cenv ty (Pop ann target) st))
Proof
  simp[compile_expr_body_def, LET_THM] >>
  Cases_on `target` >> simp[] >>
  irule ci_mono_uncurry >>
  simp[ci_mono_compile_dynarray_pop, ci_mono_refl]
QED

Theorem ci_mono_compile_named_modular[local]:
  (∀ce rt at a bt b mt m s.
    ci_mono s (SND (compile_addmod_names ce rt at a bt b mt m s))) ∧
  (∀ce rt at a bt b mt m s.
    ci_mono s (SND (compile_mulmod_names ce rt at a bt b mt m s))) ∧
  (∀ce rt at a bt b s.
    ci_mono s (SND (compile_powmod256_names ce rt at a bt b s)))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_addmod_names_def, compile_mulmod_names_def,
       compile_powmod256_names_def, LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_compile_name_vv, ci_mono_unwrap_value]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_stack_val, ci_mono_compile_addmod,
       ci_mono_compile_mulmod, ci_mono_compile_pow_mod256]
QED

(* Lift a predicate through list/expr cases and collapse cases whose
   branches are all equal; both families are generated from the datatypes. *)
val case_lift_thms =
  let val tys = [``:'a list``, ``:expr``]
      fun constant ty = Prim_rec.prove_case_const_thm
        {case_def = TypeBase.case_def_of ty,
         nchotomy = TypeBase.nchotomy_of ty}
  in map TypeBase.case_rand_of tys @ map constant tys end;

Theorem ci_mono_compile_expr_builtin[local]:
  (∀ce rt t bi es s. ci_mono s (SND (g ce rt t bi es s))) ⇒
  ci_mono st (SND (compile_expr_body f g h cenv ty (Builtin ann bi args) st))
Proof
  strip_tac >> Cases_on `bi` >>
  simp([compile_expr_body_def, LET_THM, ci_mono_compile_named_modular] @
       case_lift_thms)
QED

Theorem ci_mono_compile_expr_body[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ∧
  (∀ce rt t bi es s. ci_mono s (SND (g ce rt t bi es s))) ∧
  (∀ce vt t tb rt es s. ci_mono s (SND (h ce vt t tb rt es s))) ⇒
  ci_mono st (SND (compile_expr_body f g h cenv ty e st))
Proof
  strip_tac >> Cases_on `e` >>
  simp[ci_mono_compile_expr_ifexp, ci_mono_compile_expr_structlit,
       ci_mono_compile_expr_toplevelname, ci_mono_compile_expr_pop,
       ci_mono_compile_expr_builtin] >>
  simp[compile_expr_body_def, LET_THM, ci_mono_compile_literal_vv,
       ci_mono_compile_name_vv, ci_mono_compile_subscript_cfn,
       ci_mono_compile_attribute_cfn, ci_mono_compile_call, ci_mono_refl]
QED

Theorem ci_mono_builtin_scalar[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ∀bi. (bi = Neg ∨ bi = Abs ∨ bi = BlockHash ∨ bi = BlobHash ∨
         bi = Ceil ∨ bi = Floor ∨ (∃n. bi = Uint2Str n) ∨
         (∃n. bi = CalldataSlice n) ∨ bi = AddMod ∨ bi = MulMod ∨
         bi = PowMod256) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn, ci_mono_compile_keccak256_word]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_stack_val, ci_mono_as_ptr_val,
       ci_mono_compile_neg_helper, ci_mono_compile_builtin_abs,
       ci_mono_compile_blockhash, ci_mono_compile_blobhash,
       ci_mono_compile_ceil, ci_mono_compile_floor,
       ci_mono_compile_uint2str, ci_mono_compile_slice_calldata,
       ci_mono_compile_addmod, ci_mono_compile_mulmod,
       ci_mono_compile_pow_mod256, ci_mono_emit_op]
QED

Theorem ci_mono_builtin_method_id[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty MethodId args st))
Proof
  strip_tac >> Cases_on `method_id_literal (HD args)` >>
  simp[compile_builtin_dispatch_body_def, LET_THM, ci_mono_compile_literal_vv] >>
  irule ci_mono_uncurry >> reverse conj_tac >- simp[ci_mono_lower_value_cfn] >>
  rw[ci_mono_as_stack_val, ci_mono_as_ptr_val, ci_mono_compile_method_id_runtime]
QED

Theorem ci_mono_builtin_branching_scalar[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ∀bi. (bi = Not ∨ bi = Len ∨ (∃d. bi = AsWeiValue d)) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn]
       >> rpt gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  simp[ci_mono_as_stack_val, ci_mono_compile_invert, ci_mono_emit_op,
       ci_mono_compile_builtin_len, ci_mono_compile_builtin_calldatasize,
       ci_mono_compile_as_wei_value_decimal, ci_mono_compile_as_wei_value_int]
QED

Theorem ci_mono_builtin_environment[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ∀bi. ((∃i. bi = Env i) ∨ (∃i. bi = Acc i) ∨ bi = CalldataLen) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def, LET_THM, ci_mono_as_stack_val,
       ci_mono_compile_env_var, ci_mono_compile_acc_cfn,
       ci_mono_compile_builtin_calldatasize]
QED

Theorem ci_mono_builtin_hash[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ∀bi. (bi = Keccak256 ∨ bi = Sha256) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt IF_CASES_TAC >> rpt TOP_CASE_TAC >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_stack_val, ci_mono_compile_keccak256_bytes,
       ci_mono_compile_keccak256_bytesm, ci_mono_compile_keccak256_word,
       ci_mono_compile_sha256_bytes, ci_mono_compile_sha256_bytesm,
       ci_mono_compile_sha256_word]
QED

Theorem ci_mono_builtin_membership[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND
    (case e of
       Builtin ann (MakeArray et bnd) elems =>
         (let (ops, st') = compile_multi_exprs f cenv elems st in
          if is_in then as_stack_val ret_ty (compile_list_membership_in needle ops st')
          else as_stack_val ret_ty (compile_list_membership_notin needle ops st'))
     | _ =>
         (let (vv, st') = f cenv rhs_ty e st in
          as_stack_val ret_ty
            (compile_var_array_membership cenv needle vv rhs_ty is_in st'))))
Proof
  strip_tac >> Cases_on `e` >> simp[LET_THM] >> rpt TOP_CASE_TAC >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_compile_multi_exprs]
       >> rpt gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  simp[ci_mono_as_stack_val, ci_mono_compile_list_membership_in,
       ci_mono_compile_list_membership_notin, ci_mono_compile_var_array_membership]
QED

Theorem ci_mono_builtin_bop[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Bop op) args st))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def, LET_THM] >>
  IF_CASES_TAC
  >- (irule ci_mono_uncurry >> reverse conj_tac
      >- simp[ci_mono_lower_value_cfn]
      >> rpt gen_tac >> BETA_TAC >> irule (SRULE [LET_THM] ci_mono_builtin_membership) >> simp[]) >>
  IF_CASES_TAC >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn, ci_mono_compile_bytestring_hash,
               ci_mono_emit_op]
       >> rpt gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_emit_op]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_stack_val, ci_mono_compile_binop, ci_mono_emit_op]
QED

Theorem ci_mono_compile_ecadd_points[local]:
  ∀p1 p2 st. ci_mono st (SND (compile_ecadd_points p1 p2 st))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_ecadd_points_def, comp_ignore_bind_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind >> conj_tac
       >- simp[ci_mono_compile_alloc_buffer, ci_mono_emit_op,
               ci_mono_emit_void, ci_mono_comp_return]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_ecmul_point[local]:
  ∀p scalar st. ci_mono st (SND (compile_ecmul_point p scalar st))
Proof
  rpt gen_tac >> rewrite_tac[builtinMiscTheory.compile_ecmul_point_def, comp_ignore_bind_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind >> conj_tac
       >- simp[ci_mono_compile_alloc_buffer, ci_mono_emit_op,
               ci_mono_emit_void, ci_mono_comp_return]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_make_tuple_cfn:
  ∀cfn cenv es buf_op cur_offset st.
    (∀ce ty e s. ci_mono s (SND (cfn ce ty e s))) ⇒
    ci_mono st (SND (compile_make_tuple cfn cenv es buf_op cur_offset st))
Proof
  gen_tac >> gen_tac >> Induct >> rpt gen_tac >> strip_tac
  >- simp[compile_make_tuple_def, ci_mono_comp_return] >>
  simp[Once compile_make_tuple_def, LET_THM, comp_ignore_bind_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind >> conj_tac
       >- simp[ci_mono_emit_op, ci_mono_unwrap_value, ci_mono_compile_store_memory]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[]
QED

Theorem ci_mono_builtin_ec[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ∀bi. (bi = ECRecover ∨ bi = ECAdd ∨ bi = ECMul) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn, ci_mono_unwrap_value]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_stack_val, ci_mono_as_ptr_val, ci_mono_compile_ecrecover,
       ci_mono_compile_ecadd_points, ci_mono_compile_ecmul_point]
QED

Theorem ci_mono_builtin_concat[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Concat n) args st))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_compile_alloc_buffer, ci_mono_emit_op,
               ci_mono_compile_concat_cfn, ci_mono_emit_void]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_refl]
QED

Theorem ci_mono_builtin_makearray[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND
    (compile_builtin_dispatch_body f cenv ret_ty ty (MakeArray elem_ty bnd) args st))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `elem_ty` >> simp[LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_compile_alloc_buffer]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_ptr_val, ci_mono_compile_make_array_cfn,
       ci_mono_compile_make_tuple_cfn]
QED

Theorem ci_mono_builtin_slice[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty (Slice n) args st))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn, ci_mono_compile_slice_out_buf,
               ci_mono_compile_bytestring_src, ci_mono_compile_alloc_buffer,
               ci_mono_emit_op, ci_mono_emit_void]
       >> rpt gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn, ci_mono_compile_slice_out_buf,
               ci_mono_compile_bytestring_src, ci_mono_compile_alloc_buffer,
               ci_mono_emit_op, ci_mono_emit_void]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_ptr_val, ci_mono_compile_slice_calldata,
       ci_mono_compile_slice_code, ci_mono_compile_slice_extcode,
       ci_mono_compile_slice_data, ci_mono_compile_slice_memory] >>
  pairarg_tac >> gvs[] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_ptr_val, ci_mono_compile_slice_extcode, ci_mono_compile_slice_data]
QED

Theorem ci_mono_type_builtin_convert[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty Convert ret_ty args st))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  irule ci_mono_uncurry >> reverse conj_tac
  >- simp[ci_mono_lower_value_cfn] >>
  rpt gen_tac >> BETA_TAC >> Cases_on `ret_ty` >>
  simp[ci_mono_as_stack_val, ci_mono_compile_type_convert]
QED

Theorem ci_mono_type_builtin_constants[local]:
  ∀tb. (tb = Empty ∨ tb = MaxValue ∨ tb = MinValue ∨ tb = Epsilon) ⇒
  ci_mono st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty tb ret_ty args st))
Proof
  Cases >> simp[] >> simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[ci_mono_refl] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_compile_builtin_empty_complex]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_refl] >> pairarg_tac >> simp[ci_mono_refl]
QED

Theorem ci_mono_type_builtin_extract32[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty Extract32 ret_ty args st))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_lower_value_cfn, ci_mono_compile_extract32]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_stack_val, ci_mono_compile_clamp_extract32]
QED


Theorem ci_mono_lower_abi_encode:
  ci_mono st (SND (lower_abi_encode ensure method_id src info maxlen st))
Proof
  simp[builtinAbiTheory.lower_abi_encode_def, LET_THM] >>
  ntac 2 (ho_match_mp_tac ci_mono_bind >> conj_tac
          >- simp[ci_mono_compile_alloc_buffer, ci_mono_comp_return]
          >> rpt gen_tac) >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (Cases_on `method_id` >> simp[ci_mono_comp_return] >>
      gen_tac >> ho_match_mp_tac ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_emit_op] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_abi_encode] >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[ci_mono_emit_void] >>
      gen_tac >> ho_match_mp_tac ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_lower_abi_decode:
  ci_mono st (SND (lower_abi_decode data info amin amax outsz st))
Proof
  simp[builtinAbiTheory.lower_abi_decode_def, LET_THM] >>
  ntac 2 (ho_match_mp_tac ci_mono_bind >> conj_tac
          >- simp[ci_mono_emit_op] >> rpt gen_tac) >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (gen_tac >> IF_CASES_TAC >>
      rpt (ho_match_mp_tac ci_mono_bind >> conj_tac
           >- simp[ci_mono_emit_op] >> rpt gen_tac) >>
      simp[ci_mono_emit_void]) >>
  rpt gen_tac >>
  ntac 3 (ho_match_mp_tac ci_mono_bind >> conj_tac
          >- simp[ci_mono_compile_alloc_buffer, ci_mono_comp_return, ci_mono_emit_op]
          >> rpt gen_tac) >>
  ho_match_mp_tac ci_mono_ignore_bind >>
  simp[ci_mono_compile_abi_decode, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_encode_input[local]:
  ci_mono st (SND (compile_abi_encode_input cenv ensure tys ops st))
Proof
  simp[builtinAbiTheory.compile_abi_encode_input_def] >>
  IF_CASES_TAC >> simp[ci_mono_comp_return] >> TRY IF_CASES_TAC >>
  simp[ci_mono_comp_return] >>
  (ho_match_mp_tac ci_mono_bind >> conj_tac
   >- simp[ci_mono_compile_alloc_buffer] >>
   rpt gen_tac >> ho_match_mp_tac ci_mono_ignore_bind >>
   simp[ci_mono_emit_void, ci_mono_compile_create_tuple_in_memory,
        ci_mono_comp_return])
QED

Theorem ci_mono_type_builtin_abi_encode[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty
    (AbiEncode ensure method_id) ret_ty args st))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_compile_multi_exprs, ci_mono_compile_abi_encode_input]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_ptr_val, ci_mono_lower_abi_encode]
QED

Theorem ci_mono_compile_abi_decode_input[local]:
  ci_mono st (SND (compile_abi_decode_input ty op st))
Proof
  Cases_on `ty` >>
  TRY (simp[builtinAbiTheory.compile_abi_decode_input_def,
            ci_mono_comp_return] >> NO_TAC) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  TRY (simp[builtinAbiTheory.compile_abi_decode_input_def,
            ci_mono_comp_return] >> NO_TAC) >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[builtinAbiTheory.compile_abi_decode_input_def, ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_alloc_buffer] >> rpt gen_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- simp[ci_mono_emit_void] >> rpt gen_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_emit_op] >> rpt gen_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >>
  simp[ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_type_builtin_abi_decode[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty
    (AbiDecode n) ret_ty args st))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (irule ci_mono_uncurry >> reverse conj_tac
       >- simp[ci_mono_unwrap_value, ci_mono_compile_abi_decode_input]
       >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_as_ptr_val, ci_mono_lower_abi_decode]
QED

Theorem ci_mono_compile_builtin_dispatch_body[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st))
Proof
  strip_tac >> Cases_on `bi` >>
  simp[ci_mono_builtin_scalar, ci_mono_builtin_method_id,
       ci_mono_builtin_branching_scalar,
       ci_mono_builtin_environment, ci_mono_builtin_hash, ci_mono_builtin_bop,
       ci_mono_builtin_ec, ci_mono_builtin_concat, ci_mono_builtin_makearray,
       ci_mono_builtin_slice]
QED

Theorem ci_mono_compile_type_builtin_dispatch_body[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ci_mono st (SND (compile_type_builtin_dispatch_body f cenv vv_ty ty tb ret_ty args st))
Proof
  strip_tac >> Cases_on `tb` >>
  simp[ci_mono_type_builtin_convert, ci_mono_type_builtin_constants,
       ci_mono_type_builtin_extract32, ci_mono_type_builtin_abi_encode,
       ci_mono_type_builtin_abi_decode]
QED

(* Why it holds: only emit (appends to cs_current_insts) and new_block
   (conses onto cs_blocks) write those two fields (compileEnvScript.sml);
   every other operation threads the state through comp_bind. compile_expr
   reaches its children only through expr/builtin/type_child_callback,
   which either recurse on a strictly smaller argument or fall back to
   invalid_expr_call (a single emit). The ci_mono_*_cfn lemmas above take
   ci_mono of an arbitrary callback as a hypothesis. *)
Theorem compile_expr_ci_mono:
  (∀ cenv ty e st. ci_mono st (SND (compile_expr cenv ty e st))) ∧
  (∀ cenv ret_ty ty bi args st.
    ci_mono st (SND (compile_builtin_dispatch cenv ret_ty ty bi args st))) ∧
  (∀ cenv vv_ty ty tb ret_ty args st.
    ci_mono st (SND (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args st)))
Proof
  ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_expr_raw_def] >>
  simp[ci_mono_compile_expr_body, ci_mono_compile_builtin_dispatch_body,
       ci_mono_compile_type_builtin_dispatch_body,
       ci_mono_expr_child_callback, ci_mono_builtin_child_callback,
       ci_mono_type_child_callback]
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

(* compile_expr and lower_value compile_expr only append code and hand out
   variables and instruction ids from their start counters on. *)
Theorem compile_expr_grows:
  (∀cenv ty e st vv st'.
     compile_expr cenv ty e st = (vv, st') ⇒
     cs_extends st st' ∧ st.cs_next_var ≤ st'.cs_next_var ∧
     st.cs_next_id ≤ st'.cs_next_id) ∧
  (∀cenv ty e st op st'.
     lower_value compile_expr cenv ty e st = (op, st') ⇒
     cs_extends st st' ∧ st.cs_next_var ≤ st'.cs_next_var ∧
     st.cs_next_id ≤ st'.cs_next_id)
Proof
  conj_tac >> rpt gen_tac >> strip_tac >| [
    qspecl_then [`cenv`, `ty`, `e`, `st`] mp_tac (cj 1 compile_expr_ci_mono),
    qspecl_then [`cenv`, `ty`, `e`, `st`] mp_tac
      ci_mono_lower_value_compile_expr] >>
  simp[ci_mono_def]
QED

Theorem compile_binop_grows:
  ∀op x y ty base_literal exp_literal st z st'.
    compile_binop op x y ty base_literal exp_literal st = (z, st') ⇒
    cs_extends st st' ∧ st.cs_next_var ≤ st'.cs_next_var ∧
    st.cs_next_id ≤ st'.cs_next_id
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`op`, `x`, `y`, `ty`, `base_literal`, `exp_literal`, `st`]
    mp_tac ci_mono_compile_binop >>
  simp[ci_mono_def]
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

(* The DRET continuation only destructs the opaque packing result and returns
   IntRet, so it can never equal an OK result. *)
Theorem pack_dret_dynamic_IntRet_not_OK[local]:
  !cursor pairs s ordinary vals out.
    (\(ptrs,final_cursor,st).
       IntRet
         <|iret_values := TAKE ordinary (DROP 1 vals) ++ ptrs;
           iret_adopt_fmp := SOME final_cursor|>
         (st with vs_fmp := final_cursor))
      (pack_dret_dynamic cursor pairs s) <> OK out
Proof
  rpt strip_tac >>
  Cases_on `pack_dret_dynamic cursor pairs s` >>
  Cases_on `r` >>
  pairarg_tac >>
  gvs[]
QED

(* Helper: step_inst_base preserves call/tx/block context for ANY instruction
   that returns OK. Unlike step_inst_base_preserves_inst_idx, we don't need
   ~is_terminator because jump_to only modifies vs_prev_bb/vs_current_bb/vs_inst_idx. *)
Theorem step_inst_base_ok_terminator_jump[local]:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
    inst.inst_opcode = DJMP
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  simp_tac(srw_ss())[] >>
  gvs[pack_dret_dynamic_IntRet_not_OK, AllCaseEqs()]
QED

Theorem step_inst_base_ok_jmp_ctxs[local]:
  !inst s s'.
    inst.inst_opcode = JMP /\ step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >>
  gvs[jump_to_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem step_inst_base_ok_jnz_ctxs[local]:
  !inst s s'.
    inst.inst_opcode = JNZ /\ step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >>
  gvs[jump_to_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem step_inst_base_ok_djmp_ctxs[local]:
  !inst s s'.
    inst.inst_opcode = DJMP /\ step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >>
  gvs[jump_to_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem step_inst_base_ok_jump_ctxs[local]:
  !inst s s'.
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) /\
    step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  metis_tac[step_inst_base_ok_jmp_ctxs,
            step_inst_base_ok_jnz_ctxs,
            step_inst_base_ok_djmp_ctxs]
QED

Theorem step_inst_base_ok_terminator_ctxs[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ is_terminator inst.inst_opcode ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  drule_all step_inst_base_ok_terminator_jump >> strip_tac >>
  metis_tac[step_inst_base_ok_jump_ctxs]
QED

Theorem step_inst_base_preserves_call_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_ok_terminator_ctxs] >>
  Cases_on `inst.inst_opcode = INVOKE` >- gvs[step_inst_base_def] >>
  qspecl_then [`0`, `ARB`, `inst`, `s`, `s'`] mp_tac
    step_preserves_call_ctx >>
  ASM_SIMP_TAC bool_ss [step_inst_non_invoke]
QED

Theorem step_inst_base_preserves_tx_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    s'.vs_tx_ctx = s.vs_tx_ctx
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_ok_terminator_ctxs] >>
  Cases_on `inst.inst_opcode = INVOKE` >- gvs[step_inst_base_def] >>
  qspecl_then [`0`, `ARB`, `inst`, `s`, `s'`] mp_tac
    step_preserves_tx_ctx >>
  ASM_SIMP_TAC bool_ss [step_inst_non_invoke]
QED

Theorem step_inst_base_preserves_block_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_ok_terminator_ctxs] >>
  Cases_on `inst.inst_opcode = INVOKE` >- gvs[step_inst_base_def] >>
  qspecl_then [`0`, `ARB`, `inst`, `s`, `s'`] mp_tac
    step_preserves_block_ctx >>
  ASM_SIMP_TAC bool_ss [step_inst_non_invoke]
QED

Theorem step_inst_base_preserves_ctxs[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  metis_tac[step_inst_base_preserves_call_ctx,
            step_inst_base_preserves_tx_ctx,
            step_inst_base_preserves_block_ctx]
QED

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
  rpt gen_tac >> strip_tac >> rpt conj_tac >> irule (SRULE [] run_inst_seq_preserves_field) >> qexists `emitted_insts st st'` >> rpt strip_tac >> gvs[] >> drule step_inst_base_preserves_ctxs >> simp[]
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

(* Issue #560 integrity gate, including local proof-interface helpers. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles then ()
     else raise Fail "admitted memory-construction proof interface"
  end)
  [ci_mono_typed_memory_family, ci_mono_compile_store_memory,
   ci_mono_compile_struct_lit_cfn, ci_mono_compile_make_array_elems_cfn,
   ci_mono_compile_make_array_cfn, ci_mono_compile_zero_words,
   ci_mono_compile_builtin_empty_complex,
   builtinSimpleTheory.compile_zero_words_zero,
   builtinSimpleTheory.compile_zero_words_one_order,
   builtinSimpleTheory.compile_zero_words_two_order,
   builtinSimpleTheory.compile_builtin_empty_complex_length_order,
   builtinSimpleTheory.compile_builtin_empty_complex_fixed_order];

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles then ()
     else raise Fail "admitted memory-construction regression theorem"
  end)
  [exprLoweringTheory.compile_empty_word_dispatch,
   exprLoweringTheory.compile_empty_memory_dispatch,
   exprLoweringTheory.compile_make_array_empty_length,
   exprLoweringTheory.compile_make_array_word_order,
   exprLoweringTheory.compile_make_fixed_array_word_order,
   exprLoweringTheory.compile_make_tuple_word_order,
   exprLoweringTheory.compile_struct_lit_word_order,
   exprLoweringTheory.compile_make_array_empty_full_capacity,
   exprLoweringTheory.compile_make_array_typed_tuple_order];

(* Retained general compiler admissions and their existing structural corollary
   are excluded; all other exported proofs must be closed.
   compile_expr_extends_insts inherits compile_expr_ci_mono's admission. *)
val () = List.app
  (fn (name,th) =>
    if List.exists (fn allowed => name = allowed)
      ["compile_expr_correct", "compile_binop_correct", "compile_neg_correct",
       "compile_expr_ci_mono", "compile_expr_extends_insts"] then ()
    else let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail ("expression lowering proof is not closed: " ^ name)
    end)
  (DB.thms "exprLoweringProps");
