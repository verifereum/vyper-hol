(*
 * Internal return relations and shared value/layout/RET facts.
 *
 * TOP-LEVEL:
 *   return_unlock_state          — exact VM epilogue effect (all guards)
 *   intret_q                     — IntRet in result_rel before that effect
 *   intret_q_source_epilogue     — source transient-epilogue bridge
 *   return_unlock_changes_source_relation — old-contract counterevidence
 * The word and stack-tuple return fragments are in stmtSimReturnWord and
 * stmtSimReturnTuple.
 *)

Theory stmtSimReturn
Ancestors
  stmtSimProps
  exprSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts exprSimTypedAlloc
  gasContext gasExemptCert
  bodySimFull bodySim bodyPtrDefs gasOutcomeFullCompose gasOutcomeFull
  fragGasOriginPtr fragGasOriginPtrExec fragGasSeqPtr gasShadowState
  vyperStorageTrace vyperStorageFootprint
  ptrDiscipline ptrSafeRun memSafeRun unitTransformDefs gasSummary
  venomExecSemantics venomInst venomState vyperTypeSystem
  list rich_list pair finite_map fragExec freshWrites
  vyperTypeABI
  transientLockProps nonreentrantEquiv accountsRelProps context localPtrsProps
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs venomMemDefs vyperContext vfmExecution vfmState
  vyperInterpreter vyperState vyperValue vyperTyping vyperExprNoControl
  vyperStatePreservation
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* The statement-level source Return only raises ReturnException.  Its
   function epilogue releases the guard later; compiled RET releases it now.
   Record that exact effect, including the one executed store instruction.
   Persistent guards use the legacy unlocked value 3, transient guards 0. *)
Definition return_unlock_state_def:
  return_unlock_state cenv s =
    let (nr,key,ut,iv) = cenv.ce_nonreentrant in
      if nr /\ ~iv then
        (if ut then tstore (n2w key) 0w s else sstore (n2w key) 3w s)
          with vs_inst_idx := SUC s.vs_inst_idx
      else s
End

Definition return_unlock_insts_def:
  return_unlock_insts cenv id =
    let (nr,key,ut,iv) = cenv.ce_nonreentrant in
      if nr /\ ~iv then
        [mk_inst id (if ut then TSTORE else SSTORE)
           [Lit (n2w key); Lit (if ut then 0w else 3w)] []]
      else []
End

(* Exact epilogue-aware RetQ: result_rel holds BEFORE the unlock, with
   exactly ce_returns_count stack words (excluding the memory-return []
   alternative when the count is positive).  The returned VM state is
   precisely its optional unlock, not an arbitrary state with selected
   effects equal.  No guard cases are excluded. *)
Definition intret_q_def:
  intret_q H func cenv cx ret_tv v (es : evaluation_state) r <=>
    ?ir s. r = IntRet ir (return_unlock_state cenv s) /\
           LENGTH ir.iret_values = cenv.ce_returns_count /\
           result_rel H func ret_tv cenv cx (INR (ReturnException v), es)
             (IntRet ir s)
End

Theorem intret_q_gas_obs:
  intret_q H func cenv cx ret_tv v (es with gas_obs := readings) r =
  intret_q H func cenv cx ret_tv v es r
Proof
  simp[intret_q_def, result_rel_gas_obs]
QED

(* Reassociate source return evaluation at the forced-value boundary. *)
Theorem eval_return_forced:
  !cx e es.
    eval_stmt cx (Return (SOME e)) es =
    bind (do raw <- eval_expr cx e; read_result cx raw od)
      (\v. raise (ReturnException v)) es
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,est)` >>
  Cases_on `raw` >> simp[]
QED

(* A word type is not tuple-like, so compile_internal_return_from_env
   hands compile_internal_return no member types. *)
Theorem word_type_elem_types:
  !cenv ty.
    is_word_type ty ==>
    (case ty of
       TupleT tys => tys
     | StructT nsid =>
         MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
                            (nsid_to_string nsid))
     | _ => []) = []
Proof
  Cases_on `ty` >> simp[is_word_type_def]
QED

(* The optional release emits at most one store and reserves no variables. *)
Theorem compile_return_unlock_shape:
  !cenv sa sb.
    compile_return_unlock cenv sa = ((),sb) ==>
    sb.cs_blocks = sa.cs_blocks /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      return_unlock_insts cenv sa.cs_next_id /\
    sb.cs_next_var = sa.cs_next_var /\ cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[compile_return_unlock_def, compile_nonreentrant_unlock_def,
      return_unlock_insts_def, comp_return_def, emit_void_def,
      comp_bind_def, fresh_id_def, emit_def] >>
  irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]
QED

Theorem compile_return_unlock_frag:
  !cenv sa sb ctx sv.
    compile_return_unlock cenv sa = ((),sb) /\
    sv.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~sv.vs_call_ctx.cc_static ==>
    frag_exec ctx sa sb (\s. s = sv)
      (\s. s = return_unlock_state cenv sv) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[compile_return_unlock_def, compile_nonreentrant_unlock_def,
      return_unlock_state_def, comp_return_def, emit_void_def,
      comp_bind_def, fresh_id_def, emit_def, emitted_insts_def,
      DROP_LENGTH_APPEND, IS_PREFIX_APPEND] >>
  simp[run_inst_seq_def, is_terminator_def] >>
  TRY (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
       simp[mk_inst_def, exec_write2_def, eval_operands_def, eval_operand_def,
            arithmeticTheory.ADD1]) >>
  simp[venom_state_component_equality]
QED

Theorem return_unlock_frames[simp]:
  !cenv s.
    (return_unlock_state cenv s).vs_memory = s.vs_memory /\
    (return_unlock_state cenv s).vs_current_bb = s.vs_current_bb /\
    (return_unlock_state cenv s).vs_vars = s.vs_vars /\
    (return_unlock_state cenv s).vs_labels = s.vs_labels
Proof
  rpt gen_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, tstore_def, sstore_def]
QED

(* Move a load-only variable/index frame across the exact release. *)
Theorem return_unlock_load_frame:
  !cenv s vars n id.
    LENGTH (return_unlock_insts cenv id) <= n ==>
    (return_unlock_state cenv s) with <|vs_vars := vars; vs_inst_idx := n|> =
    return_unlock_state cenv
      (s with <|vs_vars := vars;
                vs_inst_idx := n - LENGTH (return_unlock_insts cenv id)|>)
Proof
  rpt gen_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, return_unlock_insts_def,
       tstore_def, sstore_def] >>
  strip_tac >> `SUC (n - 1) = n` by decide_tac >> simp[]
QED

Theorem compile_internal_word_return_code:
  is_word_type ty /\ cenv.ce_return_buf = NONE /\ cenv.ce_returns_count = 1 /\
  compile_internal_return_from_env cenv ty src_ty op rpc st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    return_unlock_insts cenv st.cs_next_id ++
    [mk_inst (st.cs_next_id + LENGTH (return_unlock_insts cenv st.cs_next_id))
       RET [op;rpc] []]
Proof
  rpt strip_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[compile_internal_return_from_env_def, compile_internal_return_def,
       compile_return_unlock_def, compile_nonreentrant_unlock_def,
       return_unlock_insts_def, word_type_elem_types,
       comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_void_def, emit_inst_def, fresh_id_def, emit_def]
QED

Theorem eval_operand_return_index[local,simp]:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operand_return_sstore[local,simp]:
  !op key value s.
    eval_operand op (sstore key value s) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def, sstore_def]
QED

(* Both guard representations preserve all operands. *)
Theorem eval_operand_return_unlock:
  !cenv s op.
    eval_operand op (return_unlock_state cenv s) = eval_operand op s
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def]
QED

Theorem step_internal_word_return[local]:
  !id op rpc s.
    step_inst_base (mk_inst id RET [op;rpc] []) s =
      case eval_operand op s of
        NONE => Error "ret: undefined return value"
      | SOME w => case eval_operand rpc s of
          NONE => Error "ret: undefined return value"
        | SOME pc => IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |> s
Proof
  rpt gen_tac >> simp[step_inst_base_def, eval_operands_def] >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand rpc s` >> simp[]
QED

Theorem step_persistent_return_unlock:
  !id key s.
    ~s.vs_call_ctx.cc_static ==>
    step_inst_base (mk_inst id SSTORE [Lit key; Lit 3w] []) s =
      OK (sstore key 3w s)
Proof
  simp[step_inst_base_def, exec_write2_def, eval_operand_def]
QED

(* Lift the exact optional-store/RET sequence into the containing function. *)
Theorem internal_word_return_run:
  !cenv st st' func ctx s op rpc w pc.
  fn_has_code st st' func /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    return_unlock_insts cenv st.cs_next_id ++
    [mk_inst (st.cs_next_id + LENGTH (return_unlock_insts cenv st.cs_next_id))
       RET [op;rpc] []] /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME w /\ eval_operand rpc s = SOME pc /\
  ~s.vs_call_ctx.cc_static ==>
  run_from 0 ctx func s =
    IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |>
      (return_unlock_state cenv s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `st'.cs_current_insts = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. _` (fn th =>
    assume_tac (Q.SPEC `0` th) >> assume_tac (Q.SPEC `1` th)) >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[return_unlock_insts_def, return_unlock_state_def] >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
       mk_inst_def, is_terminator_def,
       SRULE [mk_inst_def] step_internal_word_return,
       SRULE [mk_inst_def] step_persistent_return_unlock,
       SRULE [mk_inst_def] transientLockPropsTheory.step_TSTORE_lit,
       eval_operand_def] >>
  simp[Once exec_block_def, step_inst_non_invoke, mk_inst_def,
       SRULE [mk_inst_def] step_internal_word_return, arithmeticTheory.ADD1]
QED

(* No scope holds a local once the frame is left. *)
Theorem state_rel_scopes_nil:
  !H func cenv cx es s.
    state_rel H func cenv cx es s ==>
    state_rel H func cenv cx (es with scopes := []) s
Proof
  rw[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
     logs_rel_def, local_ptrs_rel_def, local_region_def, lookup_scopes_def]
QED

Theorem constructor_exit_state_rel:
  same_frame cenv cenv' /\ state_rel H func cenv' cx es s ==>
  state_rel H func cenv cx (es with scopes := []) s
Proof
  strip_tac >> dxrule state_rel_scopes_nil >> strip_tac >>
  gvs[same_frame_def, compile_env_component_equality, state_rel_def,
      local_ptrs_rel_def, local_region_def, lookup_scopes_def,
      storage_vars_rel_def, transient_vars_rel_def, logs_rel_def,
      log_entry_equiv_def, listTheory.LIST_REL_EL_EQN, immutables_rel_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!name tv v byte_offset. _` (drule_all_then strip_assume_tac) >>
  simp[]
QED

Theorem state_rel_return_index[local,simp]:
  !H func cenv cx es s n.
    state_rel H func cenv cx es (s with vs_inst_idx := n) <=>
    state_rel H func cenv cx es s
Proof
  simp[state_rel_def, local_ptrs_rel_inst_idx, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def,
       contract_storage_def, contract_transient_def]
QED

(* For the source's transient guard representation, RetQ implies ordinary
   result_rel after exactly the source function epilogue.  Persistent guards
   remain covered by the main exact VM contract; the source release primitive
   only writes transient storage, so no persistent/source parity is claimed. *)
Theorem intret_q_source_epilogue:
  !H func cenv cx ret_tv v es r nr key iv.
    cenv.ce_nonreentrant = (nr,key,T,iv) /\
    intret_q H func cenv cx ret_tv v es r ==>
    ?es'.
      (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target key
       else vyperState$return ()) es = (INL (),es') /\
      result_rel H func ret_tv cenv cx (INR (ReturnException v),es') r
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `intret_q _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intret_q_def]) >>
  Cases_on `nr` >> Cases_on `iv` >>
  gvs[return_unlock_state_def, result_rel_def, vyperStateTheory.return_def,
      release_nonreentrant_lock_execution] >>
  qmatch_goalsub_abbrev_tac `state_rel H func cenv cx vs1 _` >>
  `vs1 = (es with tStorage := (cx.txn.target =+ update_storage (n2w key) 0w
            (es.tStorage cx.txn.target)) es.tStorage)
         with storage_trace := vs1.storage_trace` by
    simp[Abbr `vs1`, evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> PURE_REWRITE_TAC[state_rel_storage_trace] >>
  irule state_rel_transient_update >> simp[] >>
  metis_tac[storage_dead_update_zero]
QED

(* Evidence that the old unchanged-source contract is genuinely false for
   a held transient guard, rather than merely difficult for metis. *)

Theorem return_unlock_changes_source_relation:
  !H func cenv cx es s key.
    MEM key (SND H) /\ key < dimword (:256) /\
    cenv.ce_nonreentrant = (T,key,T,F) /\
    state_rel H func cenv cx es s /\ tload (n2w key) s <> 0w ==>
    ~state_rel H func cenv cx es (return_unlock_state cenv s)
Proof
  rpt gen_tac >> strip_tac >>
  `storage_read_live H T (es.tStorage cx.txn.target) (n2w key)
     (BaseTV (UintT 256))` by
    (irule nonreentrant_slot_read_live >> simp[]) >>
  drule_all state_rel_transient_lookup >> strip_tac >>
  simp[return_unlock_state_def] >> strip_tac >>
  drule_all state_rel_transient_lookup >> simp[]
QED

(* A word returns as the one word of its typed encoding. *)
Theorem intret_vals_match_word:
  !tenv t tv v.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==>
    intret_vals_match tv v [typed_val_to_w256 tv v]
Proof
  Cases_on `t` >>
  simp[is_word_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[intret_vals_match_def] >> Cases_on `v` >> simp[]
QED

(* ===== A tuple of words on the stack ===== *)

(* The words compile_load_tuple_elements loads from the tuple at w: one per
   element type, from offset off on, each type's type_memory_bytes on. *)
Definition tuple_words_def:
  tuple_words cenv (w : bytes32) [] off mem = [] /\
  tuple_words cenv w (t::ts) off mem =
    mem_word_at (w2n (w + n2w off)) mem ::
    tuple_words cenv w ts (off + type_memory_bytes cenv t) mem
End

Theorem tuple_elem_load_head_run:
  !bop off sa pv sm v sb s w load.
    emit_op ADD [bop; Lit off] sa = (pv, sm) /\
    compile_load_memory pv load sm = (v, sb) /\
    eval_operand bop s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    sb.cs_next_var = sa.cs_next_var + 1 + (if load then 1 else 0) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    (?x. v = Var x /\ not_fresh_at sb x) /\
    ?t vs. run_inst_seq (emitted_insts sa sb) s = OK t /\
           t = s with vs_vars := vs /\
           (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
           eval_operand v t = SOME
             (if load then mem_word_at (w2n (w + off)) s.vs_memory else w + off)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `load` >>
  gvs[contextTheory.compile_load_memory_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
      fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       venomInstTheory.mk_inst_def, is_terminator_def,
       not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  simp[run_inst_seq_def] >>
  simp[Once step_inst_base_def] >>
  simp[exec_pure2_def, exec_read1_def,
       eval_operand_def, bind_outputs_def, lookup_var_update_var] >>
  simp[Once step_inst_base_def, exec_read1_def, eval_operand_def,
       bind_outputs_def, lookup_var_update_var] >>
  simp[update_var_def, mload_def, mem_word_at_def, lookup_var_def,
       FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `s with vs_vars := VV` >> qexists `VV` >>
  simp[Abbr `VV`, FLOOKUP_UPDATE] >> rw[] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, DECIDE ``a <= a + 1n``]
QED

Theorem tuple_elem_head_run[local]:
  !bop off sa pv sm v sb s w.
    emit_op ADD [bop; Lit off] sa = (pv, sm) /\
    emit_op MLOAD [pv] sm = (v, sb) /\
    eval_operand bop s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 2 /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    (?x. v = Var x /\ not_fresh_at sb x) /\
    ?t vs. run_inst_seq (emitted_insts sa sb) s = OK t /\
           t = s with vs_vars := vs /\
           (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
           eval_operand v t = SOME (mem_word_at (w2n (w + off)) s.vs_memory)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPEC `T` (Q.GEN `load` (SPEC_ALL tuple_elem_load_head_run))) >>
  simp[contextTheory.compile_load_memory_def] >> disch_then drule_all >> simp[]
QED

Theorem eval_operand_old_vars:
  !sa s t op.
    t.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def]
QED

Theorem tuple_load_cons_compose:
  !sa sh sf x rest s vs1 vs2 a ws.
    sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
    sf.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sf /\
    same_blocks sa sh /\ same_blocks sh sf /\
    sa.cs_next_var <= sh.cs_next_var /\ sh.cs_next_var <= sf.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sh) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sh sf) /\
    not_fresh_at sh x /\
    (!x. MEM (Var x) rest ==> not_fresh_at sf x) /\
    run_inst_seq (emitted_insts sa sh) s = OK (s with vs_vars := vs1) /\
    (!x. not_fresh_at sa x ==>
         lookup_var x (s with vs_vars := vs1) = lookup_var x s) /\
    eval_operand (Var x) (s with vs_vars := vs1) = SOME a /\
    run_inst_seq (emitted_insts sh sf) (s with vs_vars := vs1) =
      OK (s with vs_vars := vs2) /\
    (!x. not_fresh_at sh x ==>
         lookup_var x (s with vs_vars := vs2) =
         lookup_var x (s with vs_vars := vs1)) /\
    eval_operands rest (s with vs_vars := vs2) = SOME ws ==>
    sf.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sf /\
    same_blocks sa sf /\ sa.cs_next_var <= sf.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sf) /\
    (!y. MEM (Var y) (Var x::rest) ==> not_fresh_at sf y) /\
    ?t vs. run_inst_seq (emitted_insts sa sf) s = OK t /\
           t = s with vs_vars := vs /\
           (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
           eval_operands (Var x::rest) t = SOME (a::ws)
Proof
  rpt gen_tac >> strip_tac >>
  `emitted_insts sa sf = emitted_insts sa sh ++ emitted_insts sh sf` by
    metis_tac[emitted_insts_append] >>
  `same_blocks sa sf` by fs[same_blocks_def] >>
  `sa.cs_next_var <= sf.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sh x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at sh x ==> not_fresh_at sf x` by
    metis_tac[not_fresh_at_mono] >>
  `run_inst_seq (emitted_insts sa sf) s = OK (s with vs_vars := vs2)` by
    (simp[] >>
     qpat_assum `run_inst_seq (emitted_insts sa sh) _ = OK _`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  gvs[eval_operand_def] >> simp[eval_operands_def, eval_operand_def] >>
  conj_tac >- metis_tac[] >> qexists `vs2` >> simp[] >> metis_tac[]
QED

(* compile_load_tuple_elements runs from any state where its bop is
   defined: it loads tuple_words, writing only fresh variables. *)
Theorem compile_load_tuple_elements_run:
  !tys cenv bop off sa elems sb s w.
    compile_load_tuple_elements cenv bop tys off sa = (elems, sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    ?t vs. run_inst_seq (emitted_insts sa sb) s = OK t /\
           t = s with vs_vars := vs /\
           (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
           eval_operands elems t =
             SOME (tuple_words cenv w tys off s.vs_memory)
Proof
  Induct
  >- (rw[compile_load_tuple_elements_def, comp_return_def] >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def,
           eval_operands_def, tuple_words_def] >>
      qexists `s.vs_vars` >> simp[venom_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_load_tuple_elements _ _ _ _ _ = _` mp_tac >>
  simp[compile_load_tuple_elements_def, comp_bind_def, LET_THM] >>
  rename1 `type_memory_bytes cenv ht` >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  gvs[] >>
  rename1 `emit_op ADD _ sa = (pv, sm)` >>
  rename1 `emit_op MLOAD _ sm = (v, sh)` >>
  rename1 `compile_load_tuple_elements _ _ _ _ sh = (rest, sf)` >>
  drule_all tuple_elem_head_run >> strip_tac >> gvs[] >>
  `(!x. bop = Var x ==> not_fresh_at sh x) /\
   eval_operand bop (s with vs_vars := vs) = SOME w` by
    (conj_tac
     >- metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD] >>
     Cases_on `bop` >> gvs[eval_operand_def]) >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sh.cs_next_var` by simp[] >>
  `sh.cs_next_var <= sf.cs_next_var` by simp[] >>
  `sf.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sf` by simp[] >>
  drule_all tuple_load_cons_compose >> strip_tac >>
  gvs[tuple_words_def] >> metis_tac[]
QED

(* A word type takes one word, at the value level and in the lowering. *)
Theorem word_type_sizes:
  !tenv t tv cenv.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==>
    type_memory_size tv = 32 /\ type_memory_bytes cenv t = 32
Proof
  Cases_on `t` >> simp[is_word_type_def]
  >~ [`FlagT`]
  >- simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS,
          type_memory_size_def, type_memory_bytes_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, evaluate_type_def, type_memory_size_def,
       type_memory_bytes_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, evaluate_type_def, type_memory_size_def,
       type_memory_bytes_def]
QED

(* The words of a tuple of word values laid out at w + off are their typed
   encodings, where the tuple's words fit below 2 ** 256. *)
Theorem tuple_words_typed:
  !tys tvs vs off cenv tenv w mem.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    values_have_types tvs vs /\ EVERY is_word_type tys /\
    tuple_in_memory vs tvs (w2n w + off) mem /\
    w2n w + off + 32 * LENGTH tys <= dimword (:256) ==>
    tuple_words cenv w tys off mem =
      MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[tuple_words_def, value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `evaluate_type tenv ty1 = SOME tv1` >>
  drule_all word_type_sizes >>
  disch_then (qspec_then `cenv` strip_assume_tac) >>
  qpat_x_assum `tuple_in_memory _ _ _ _` mp_tac >>
  simp[val_in_memory_def] >> strip_tac >>
  `w2n (w + n2w off) = w2n w + off` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  conj_tac
  >- (simp[] >> irule val_in_memory_word_type >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> qexistsl [`tenv`] >>
  gvs[arithmeticTheory.ADD_ASSOC]
QED

(* A non-word value's footprint fits below 2 ** 256: it sits in an
   allocation or a live local's region, both below the frontier. *)

Theorem eval_operands_snoc[local]:
  !ops s vals op v.
    eval_operands ops s = SOME vals /\ eval_operand op s = SOME v ==>
    eval_operands (ops ++ [op]) s = SOME (vals ++ [v])
Proof
  Induct >> rw[eval_operands_def] >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

(* RET of the values of ops and the return PC. *)
Theorem step_ret_values:
  !id ops rpc s vals pc.
    eval_operands ops s = SOME vals /\ lookup_var rpc s = SOME pc ==>
    step_inst_base (mk_inst id RET (ops ++ [Var rpc]) []) s =
      IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s
Proof
  rpt strip_tac >>
  `eval_operands (ops ++ [Var rpc]) s = SOME (vals ++ [pc])` by
    (irule eval_operands_snoc >> simp[eval_operand_def]) >>
  `?h t. vals ++ [pc] = h::t` by (Cases_on `vals` >> simp[]) >>
  `FRONT (h::t) = vals` by
    (qpat_x_assum `_ = h::t` (SUBST1_TAC o SYM) >> simp[FRONT_APPEND]) >>
  simp[step_inst_base_def, venomInstTheory.mk_inst_def]
QED

Theorem compile_tuple_load_all_words:
  !tys cenv src off.
    EVERY is_word_type tys ==>
    compile_tuple_load_all cenv src tys off =
    compile_load_tuple_elements cenv src tys off
Proof
  Induct >>
  simp[compile_tuple_load_all_def, compile_load_tuple_elements_def,
       contextTheory.compile_load_memory_def]
QED

Theorem compile_tuple_load_all_grows:
  !tys cenv base off sa elems sb.
    compile_tuple_load_all cenv base tys off sa = (elems, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  Induct >- simp[compile_tuple_load_all_def, comp_return_def, cs_extends_refl] >>
  rpt gen_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `compile_load_memory pv (is_word_type ht) sm = (v, sh)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `cs_extends sm sh /\ sm.cs_next_var <= sh.cs_next_var` by
    (Cases_on `is_word_type ht` >>
     gvs[contextTheory.compile_load_memory_def, comp_return_def] >>
     metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND, cs_extends_refl]) >>
  first_x_assum drule >> strip_tac >>
  metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_load_tuple_elements_extends:
  !tys cenv base off sa elems sb.
    compile_load_tuple_elements cenv base tys off sa = (elems, sb) ==>
    cs_extends sa sb
Proof
  Induct >>
  rw[compile_load_tuple_elements_def, comp_return_def, comp_bind_def,
     cs_extends_refl] >>
  rpt (pairarg_tac >> gvs[]) >>
  `!opc ops. cs_appends (emit_op opc ops)` by simp[cs_appends_emit_helpers] >>
  fs[cs_appends_def] >> res_tac >> metis_tac[cs_extends_trans]
QED

Theorem eval_operands_inst_idx[local]:
  !ops s n. eval_operands ops (s with vs_inst_idx := n) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operands_vars_inst_idx:
  !ops s v n.
    eval_operands ops (s with <| vs_vars := v; vs_inst_idx := n |>) =
    eval_operands ops (s with vs_vars := v)
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem word_tuple_size:
  !tys tvs tenv.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    EVERY is_word_type tys ==>
    type_memory_size_list tvs = 32 * LENGTH tys
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def] >>
  rpt strip_tac >> drule_all word_type_sizes >>
  disch_then (qspec_then `ARB` strip_assume_tac) >> res_tac >> simp[]
QED

Theorem intret_vals_match_tuple:
  !tvs vs.
    1 < LENGTH tvs /\ LENGTH vs = LENGTH tvs ==>
    intret_vals_match (TupleTV tvs) (ArrayV (TupleV vs))
      (MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs)))
Proof
  rpt strip_tac >> Cases_on `tvs` >> Cases_on `vs` >> gvs[] >>
  rename1 `LENGTH t1 = LENGTH t2` >> Cases_on `t1` >> Cases_on `t2` >>
  gvs[intret_vals_match_def]
QED

(* A typed tuple: its type's element types and its elements. *)
Theorem tuple_type_value:
  !tenv tys ret_tv v.
    evaluate_type tenv (TupleT tys) = SOME ret_tv /\
    value_has_type ret_tv v ==>
    ?tvs vs. ret_tv = TupleTV tvs /\ v = ArrayV (TupleV vs) /\
             LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
             values_have_types tvs vs
Proof
  rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]
QED

Theorem return_forced_admissible:
  gas_admissible (eval_stmt cx (Return (SOME e))) (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `eval_stmt cx (Return (SOME e)) (es with gas_obs := gs) = (INR ex, ee)` by
    (pure_rewrite_tac[eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[Once bind_def]) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

Theorem return_forced_exempt:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (Return (SOME e))) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx (Return (SOME e))) (return ()) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. ignore_bind (raise (ReturnException v)) (return ()))` by
    (simp[ignore_bind_def, FUN_EQ_THM, bind_def, eval_return_forced] >>
     gen_tac >> Cases_on `eval_expr cx e x` >>
     rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >>
     rename1 `read_result cx v est` >>
     Cases_on `read_result cx v est` >>
     rename1 `read_result cx v est = (forced,forced_es)` >>
     Cases_on `forced` >> simp[raise_def]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_value >> simp[]
QED

(* ===== Full-family internal returns ===== *)

(* The release changes only the guard's storage and the instruction index. *)
Theorem return_unlock_state_frames:
  !cenv s id.
    (return_unlock_state cenv s).vs_inst_idx =
      s.vs_inst_idx + LENGTH (return_unlock_insts cenv id) /\
    (return_unlock_state cenv s).vs_allocas = s.vs_allocas /\
    (return_unlock_state cenv s).vs_halted = s.vs_halted
Proof
  rpt gen_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, return_unlock_insts_def, tstore_def,
       sstore_def, arithmeticTheory.ADD1]
QED

(* A literal guard store is a straight-line step: no memory, no pointer,
   no GAS mark, and no variable taint. *)
Theorem return_unlock_origin_ptr:
  compile_return_unlock cenv sa = ((),su) /\ fn_has_code sa su func /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn'. G' = G /\ tn'.t_var = tn.t_var /\ tn'.t_mem = tn.t_mem /\
    !D. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
          (OK (return_unlock_state cenv s), G', tn')
Proof
  strip_tac >> drule compile_return_unlock_shape >> strip_tac >>
  qspecl_then [`sa`, `su`, `func`, `return_unlock_insts cenv sa.cs_next_id`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[return_unlock_insts_def, return_unlock_state_def] >>
  TRY (qexists_tac `tn` >> rw[] >>
       irule (cj 1 gas_origin_ptr_path_rules) >> simp[] >> NO_TAC) >>
  (qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME i` >>
  qmatch_goalsub_abbrev_tac `OK (u with vs_inst_idx := _)` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_persistent_return_unlock,
         transientLockPropsTheory.step_TSTORE_lit] >>
  `~u.vs_halted /\ u.vs_allocas = s.vs_allocas /\
   u.vs_requests = s.vs_requests /\ u.vs_fmp = s.vs_fmp` by
    simp[Abbr `u`, tstore_def, sstore_def] >>
  `step_prov PG G i u = G` by
    simp[Abbr `i`, step_prov_def, set_prov_def, mk_inst_def,
         finite_mapTheory.DRESTRICT_UNIV] >>
  qexists_tac `step_taint i s u tn` >>
  conj_tac
  >- (`i.inst_outputs = []` by simp[Abbr `i`, mk_inst_def] >>
      simp[step_taint_def, set_var_taint_def, pred_setTheory.COMPL_EMPTY,
           finite_mapTheory.DRESTRICT_UNIV]) >>
  conj_tac
  >- (`new_site_bytes s u = {}` by
        (simp[new_site_bytes_def, pred_setTheory.EXTENSION,
              finite_mapTheory.FLOOKUP_DEF] >>
         rw[] >> CCONTR_TAC >> fs[] >> TRY decide_tac >> metis_tac[]) >>
      `range_bytes (step_writes i s u) = {}` by
        simp[Abbr `i`, step_writes_def, mk_inst_def, range_bytes_def,
             codegenRelTheory.source_memory_write_ranges_def,
             pred_setTheory.EXTENSION] >>
      `written_taint tn i s = {}` by
        simp[Abbr `i`, written_taint_def, mk_inst_def] >>
      simp[step_taint_def, mem_taint_def]) >>
  gen_tac >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG) (s, G, tn) []
     (OK (u with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)),
      step_prov PG G i u, step_taint i s u tn)` by
    (mp_tac (SPEC_ALL straight_line_origin_ptr_edge) >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
     disch_then irule >>
     simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          ptr_inst_ok_def, access_ok_def, taint_ok_def, op_taint_def,
          step_inst_non_invoke] >>
     gvs[mk_inst_def] >> rw[] >> gvs[]) >>
  qpat_x_assum `step_prov _ _ _ _ = G`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  irule (REWRITE_RULE [APPEND] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
           (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
  qexistsl_tac [`G`, `u with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)`,
                `step_taint i s u tn`] >>
  simp[] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[])
QED

(* RET of words already on hand, with untainted operands. *)
Theorem emitted_ret_origin_ptr[local]:
  emit_inst RET (ops ++ [Var rpc]) [] sa = ((), sb) /\
  fn_has_code sa sb func /\ eval_operands ops s = SOME vals /\
  lookup_var rpc s = SOME pc /\
  EVERY (\op. op_taint tn op = {}) (ops ++ [Var rpc]) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) []
    (IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s, G, tn)
Proof
  strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `!fuel. step_inst fuel ctx
     (mk_inst sa.cs_next_id RET (ops ++ [Var rpc]) []) s =
     IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     metis_tac[step_ret_values, mk_inst_def]) >>
  irule (cj 3 gas_origin_ptr_path_rules) >>
  simp[exit_result_def, gas_origin_ptr_edge_def,
       fragGasOriginTheory.gas_origin_edge_def,
       fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
  conj_tac
  >- (qexists_tac `0` >>
      simp[gasEventsTheory.gas_events_step_def, mk_inst_def,
           memSafeRunTheory.mem_safe_step_non_invoke,
           unitTransformDefsTheory.inst_mem_below_frontier_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           codegenRelTheory.source_memory_write_ranges_def]) >>
  qexists_tac `0` >>
  simp[gasCountTheory.gas_count_step_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ptr_inst_ok_def, mk_inst_def] >>
  simp[ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* The release, then RET to the saved PC.  The ghost endpoint does not
   depend on the dead mask, so one witness serves every horizon. *)
Theorem compile_return_none_int_origin_ptr:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
  compile_stmt cenv lctx ty (Return NONE) sa = ((), sb) /\
  fn_has_code sa sb func /\ ret_pc_ok cenv sa s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\ allocas_from lo s /\
  op_taint tn (Var rpc) = {} /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn'. !D.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
      (IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
         (return_unlock_state cenv s), G', tn')
Proof
  strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_return_unlock cenv sa` >> rename1 `_ = (u, su)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends sa su` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends su sb` by metis_tac[cs_extends_emit_inst] >>
  `fn_has_code sa su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split] >>
  mp_tac (SPEC_ALL return_unlock_origin_ptr) >>
  impl_tac >- fs[] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >> gen_tac >>
  `?pc. lookup_var rpc s = SOME pc` by metis_tac[ret_pc_ok_def] >>
  qabbrev_tac `s1 = return_unlock_state cenv s` >>
  `lookup_var rpc s1 = SOME pc /\ allocas_from lo s1 /\ ~s1.vs_halted /\
   s1.vs_current_bb = su.cs_current_bb /\
   s1.vs_inst_idx = LENGTH su.cs_current_insts` by
    (simp[Abbr `s1`, lookup_var_def, return_unlock_frames,
          return_unlock_state_frames, allocas_from_def] >>
     qspecl_then [`cenv`, `s`, `sa.cs_next_id`] mp_tac
       return_unlock_state_frames >> simp[] >>
     rpt strip_tac >> fs[allocas_from_def, lookup_var_def] >> metis_tac[]) >>
  `op_taint tn' (Var rpc) = {}` by fs[op_taint_def] >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s1, G', tn') []
     (IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s1, G', tn')` by
    (irule (Q.INST [`ops` |-> `[]`] emitted_ret_origin_ptr) >>
     simp[eval_operands_def] >>
     qexistsl_tac [`pc`, `rpc`, `su`, `sb`] >> fs[]) >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Theorem compile_return_none_int_frag_full:
  !DF lo d ctx shadow_ctx PG func shadow_func
   cx lctx cenv ty ret_tv es rpc slot_size.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
    cenv.ce_returns_count = 0 ==>
    stmt_frag_full
      (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx
      (\H v ee gt r. intret_q H func cenv cx ret_tv v ee r)
      cenv
      (stmt_env cenv lctx ty (Return NONE))
      (stmt_env cenv lctx ty (Return NONE))
      (eval_stmt cx (Return NONE)) es
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `compile_stmt cenv lctx ty (Return NONE) sa = ((), sb)` by
    (qpat_x_assum `stmt_env cenv lctx ty (Return NONE) sa = (cenv', sb)` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[]) >>
  qabbrev_tac `r = IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
                     (return_unlock_state cenv s0)` >>
  `?G' tn'. !H. valid_horizon cx st0 H es.storage_trace ==>
     gas_origin_ptr_path (DF H, lo, gas_explicit_sites ctx shadow_ctx, ctx,
                          func, PG) (s0, G0, tn0) [] (r, G', tn')` by
    (Cases_on `?H. valid_horizon cx st0 H es.storage_trace` >> gvs[] >>
     first_assum (drule_then strip_assume_tac) >>
     `~s0.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
     `allocas_from lo s0 /\ op_taint tn0 (Var rpc) = {}` by
       fs[ghost_inv_at_def] >>
     drule_all compile_return_none_int_origin_ptr >>
     disch_then (strip_assume_tac o
       Q.INST [`tn` |-> `tn0`, `G` |-> `G0`,
               `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL) >>
     metis_tac[]) >>
  irule (Q.INST [`res` |-> `INR (ReturnException NoneV)`, `ee` |-> `es`]
           gas_outcome_full_exit) >>
  conj_tac >- fs[] >>
  conj_tac >- simp[Once evaluate_def, raise_def] >>
  qexistsl_tac [`G'`, `r`, `tn'`] >>
  simp[Abbr `r`, exit_result_def] >>
  rpt strip_tac >> res_tac >> simp[stmt_exit_ptr_def] >>
  simp[intret_q_def, result_rel_def, intret_vals_match_def] >>
  TRY disj2_tac >> qexists_tac `s0` >> simp[] >>
  `state_rel H func cenv cx es s0` by fs[stmt_state_rel_def] >>
  drule state_rel_scopes_nil >>
  strip_tac >>
  `es with <|scopes := []; gas_obs := tail|> =
   (es with scopes := []) with gas_obs := tail` by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[state_rel_gas_obs] >>
  first_assum ACCEPT_TAC
QED

Theorem internal_frame_ret_none_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx cenv ret_tv rpc slot_size.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
    cenv.ce_returns_count = 0 ==>
    frame_ret_ok_full
      (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx
      (\H v ee gt r. intret_q H func cenv cx ret_tv v ee r) cenv NoneT
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[frame_ret_ok_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo` >> fs[type_stmt_def] >>
  `cenv'.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
   cenv'.ce_returns_count = 0 /\
   cenv'.ce_nonreentrant = cenv.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  mp_tac (Q.SPECL
    [`DF`, `lo`, `d`, `ctx`, `shadow_ctx`, `PG`, `func`, `shadow_func`,
     `cx`, `lctx`, `cenv'`, `NoneT`, `ret_tv`, `es`, `rpc`, `slot_size`]
    compile_return_none_int_frag_full) >>
  simp[] >>
  pure_rewrite_tac[stmt_frag_full_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  simp[stmt_exit_ptr_def] >> strip_tac >> simp[] >>
  disj2_tac >> gvs[intret_q_def, result_rel_def] >>
  `return_unlock_state cenv' s = return_unlock_state cenv s` by
    simp[return_unlock_state_def] >>
  qexists_tac `s` >> simp[] >>
  drule_all (Q.INST
    [`es` |-> `ee with <|scopes := []; gas_obs := tail|>`]
    constructor_exit_state_rel) >> simp[]
QED

(* A word return releases the guard and then RETs the value and the PC. *)
Theorem compile_internal_word_return_parts[local]:
  is_word_type ty /\ cenv.ce_return_buf = NONE /\ cenv.ce_returns_count = 1 /\
  compile_internal_return_from_env cenv ty src_ty op rpc sm = ((),sb) ==>
  ?su. compile_return_unlock cenv sm = ((),su) /\
       emit_inst RET [op; rpc] [] su = ((),sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, compile_internal_return_def,
       word_type_elem_types, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `compile_return_unlock cenv sm` >> rename1 `_ = (u, su)` >>
  Cases_on `u` >> simp[]
QED

Theorem return_unlock_shadow_prefix:
  compile_return_unlock cenv sa = ((),sb) /\
  compile_return_unlock cenv sa' = ((),sb') /\
  gas_shadow_state sb sb' ==>
  gas_shadow_state sa sa'
Proof
  rpt strip_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[compile_return_unlock_def, compile_nonreentrant_unlock_def,
      comp_return_def, emit_void_def, comp_bind_def, fresh_id_def, emit_def,
      gas_shadow_state_def]
QED

Theorem emitted_ret_shadow_prefix[local]:
  emit_inst RET [op; rpc] [] sm = ((), sb) /\
  emit_inst RET [shadow_op; rpc] [] shadow_sm = ((), shadow_sb) /\
  gas_shadow_state sb shadow_sb ==>
  op = shadow_op /\ gas_shadow_state sm shadow_sm
Proof
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[gas_shadow_state_def, gas_shadow_inst_def, mk_inst_def]
QED

Theorem return_word_compile_parts[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
  cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
  is_word_type ty /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv', sb) /\
  fn_has_code sa sb func ==>
  cenv' = cenv /\
  ?op sm su. lower_value compile_expr cenv ty e sa = (op, sm) /\
    compile_return_unlock cenv sm = ((),su) /\
    emit_inst RET [op; Var rpc] [] su = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\
    fn_has_code su sb func
Proof
  strip_tac >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `lower_value compile_expr cenv ty e sa = (_, sm)` >>
  rename1 `fn_has_code sa sb func` >>
  drule_all compile_internal_word_return_parts >> strip_tac >>
  qexists_tac `su` >> simp[] >>
  drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends sm su` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends su sb` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends sa sm` by metis_tac[compile_expr_grows] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem return_word_operand[local]:
  IS_SOME (type_stmt env ty (Return (SOME e))) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_post H ctx func cenv cx e es sa sb s0 ee v op s ==>
  eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  strip_tac >>
  `expr_type e = ty` by
    (gvs[type_stmt_def, AllCaseEqs()] >>
     metis_tac[compileEnvTheory.type_widens_to_word]) >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_word] >>
  gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

(* The release and RET after a word operand; one ghost endpoint for every
   dead mask. *)
Theorem return_word_suffix_origin_ptr[local]:
  compile_return_unlock cenv sm = ((),su) /\
  emit_inst RET [op; Var rpc] [] su = ((),sb) /\
  fn_has_code sm su func /\ fn_has_code su sb func /\
  eval_operand op s = SOME w /\ lookup_var rpc s = SOME pc /\
  op_taint tn op = {} /\ op_taint tn (Var rpc) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\ allocas_from lo s /\
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?G' tn'. !D.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
      (IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |>
         (return_unlock_state cenv s), G', tn')
Proof
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`] (SPEC_ALL return_unlock_origin_ptr)) >>
  impl_tac >- fs[] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >> gen_tac >>
  drule compile_return_unlock_shape >> strip_tac >>
  qabbrev_tac `s1 = return_unlock_state cenv s` >>
  `lookup_var rpc s1 = SOME pc /\ eval_operand op s1 = SOME w /\
   allocas_from lo s1 /\ ~s1.vs_halted /\
   s1.vs_current_bb = su.cs_current_bb /\
   s1.vs_inst_idx = LENGTH su.cs_current_insts` by
    (simp[Abbr `s1`, lookup_var_def, return_unlock_frames,
          eval_operand_return_unlock, allocas_from_def] >>
     qspecl_then [`cenv`, `s`, `sm.cs_next_id`] mp_tac
       return_unlock_state_frames >> simp[] >>
     rpt strip_tac >> fs[allocas_from_def, lookup_var_def] >> metis_tac[]) >>
  `op_taint tn' op = {} /\ op_taint tn' (Var rpc) = {}` by
    (Cases_on `op` >> fs[op_taint_def]) >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s1, G', tn') []
     (IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |> s1, G', tn')` by
    (irule (Q.INST [`ops` |-> `[op]`] emitted_ret_origin_ptr) >>
     simp[eval_operands_def] >>
     qexistsl_tac [`op`, `pc`, `rpc`, `su`, `sb`] >> fs[]) >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

(* Scalar internal returns retain the expression's joint source prefix. *)
Theorem compile_return_word_int_frag_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx cenv ty tv es e env
   rpc slot_size.
   cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
   cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
   is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
   expr_sim_inv cenv cx env es /\
   stmt_exprs_ok cenv (Return (SOME e)) /\
   IS_SOME (type_stmt env ty (Return (SOME e))) /\
   call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
   (!ety. expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
            cenv cx ety e es /\
          expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
            cenv cx ety e es)
   ==>
   stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx
     (\H v ee gt r. intret_q H func cenv cx tv v ee r) cenv
     (stmt_env cenv lctx ty (Return (SOME e)))
     (stmt_env cenv lctx ty (Return (SOME (gas_shadow_expr e))))
     (eval_stmt cx (Return (SOME e))) es
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Return (SOME e)) sa = _`
    (mp_then Any mp_tac return_word_compile_parts) >> simp[] >>
    disch_then drule_all >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Return (SOME (gas_shadow_expr e))) shadow_sa = _`
    (mp_then Any mp_tac return_word_compile_parts) >> simp[] >>
    disch_then drule_all >> strip_tac >>
  rename1 `lower_value compile_expr cenv ty (gas_shadow_expr e) shadow_sa =
             (shadow_op, shadow_sm)` >>
  rename1 `compile_return_unlock cenv shadow_sm = ((), shadow_su)` >>
  `op = shadow_op /\ gas_shadow_state su shadow_su` by
    metis_tac[emitted_ret_shadow_prefix] >>
  `gas_shadow_state sm shadow_sm` by
    metis_tac[return_unlock_shadow_prefix] >>
  qpat_x_assum `op = shadow_op` SUBST_ALL_TAC >>
  rpt (qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `!ety. _` (qspec_then `ty` strip_assume_tac) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                           `shadow_op`, `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  `?pc. lookup_var rpc s0 = SOME pc` by metis_tac[ret_pc_ok_def] >>
  match_mp_tac (GEN_ALL gas_outcome_full_bind_all) >>
  qexists_tac `\H res mid G1 tn1 t. ?v. res = INL v /\
     expr_post H ctx func cenv cx e es sa sm s0 mid v shadow_op t /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
     ptr_val_ok cx (post_value_type cenv e) v shadow_op G1 tn1 t /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted` >>
  rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_raise]
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ (bind _ _)`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`gas_outcome_full _ _ _ _ (bind (eval_expr _ _) _)`]
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> gvs[] >>
      Cases_on `res` >> gvs[expr_exit_def, stmt_exit_ptr_def] >>
      gen_tac >> disj1_tac >>
      Cases_on `r` >> gvs[expr_exit_def] >>
      Cases_on `y` >> gvs[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  (* the value is on hand: release and RET *)
  rpt strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  `?v. res = INL v /\
       expr_post H0 ctx func cenv cx e es sa sm s0 mid v shadow_op t /\
       ghost_inv_at (DF H0) lo d cenv cx mid G1 tn1 t /\
       ptr_val_ok cx (post_value_type cenv e) v shadow_op G1 tn1 t /\
       t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted` by
    metis_tac[] >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >> simp[] >>
  `eval_operand shadow_op t = SOME (typed_val_to_w256 tv v)` by
    metis_tac[return_word_operand] >>
  `lookup_var rpc t = SOME pc` by metis_tac[expr_post_def] >>
  `op_taint tn1 shadow_op = {} /\ op_taint tn1 (Var rpc) = {}` by
    metis_tac[ptr_val_ok_def, ghost_inv_at_def] >>
  `~t.vs_call_ctx.cc_static /\ allocas_from lo t` by
    fs[expr_post_def, stmt_state_rel_def, state_rel_def, ghost_inv_at_def] >>
  drule_all return_word_suffix_origin_ptr >>
  disch_then (strip_assume_tac o
    Q.INST [`tn` |-> `tn1`, `G` |-> `G1`,
            `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL) >>
  irule (Q.INST [`res` |-> `INR (ReturnException v)`, `ee` |-> `mid`]
           gas_outcome_full_exit) >>
  TRY (conj_tac >- (fs[] >> NO_TAC)) >>
  qexistsl_tac [`G'`, `mid`,
    `IntRet <|iret_values := [typed_val_to_w256 tv v];
              iret_adopt_fmp := NONE|> (return_unlock_state cenv t)`,
    `tn'`, `v`] >>
  qpat_assum `~t.vs_halted` (fn th => simp[th, exit_result_def, raise_def]) >>
  rpt strip_tac >> simp[stmt_exit_ptr_def] >>
  simp[intret_q_def, result_rel_def] >>
  TRY disj2_tac >> qexists_tac `t` >> simp[] >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid v shadow_op t` by
    (qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       drule >> simp[]) >>
  `state_rel H func cenv cx mid t` by
    fs[expr_post_def, stmt_state_rel_def] >>
  rpt conj_tac >>
  TRY (metis_tac[intret_vals_match_word] >> NO_TAC) >>
  drule state_rel_scopes_nil >>
  strip_tac >>
  `mid with <|scopes := []; gas_obs := tail|> =
   (mid with scopes := []) with gas_obs := tail` by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[state_rel_gas_obs] >>
  first_assum ACCEPT_TAC
QED

Theorem internal_frame_ret_word_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx cenv ty tv rpc slot_size.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
    cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
    frame_ret_ok_full
      (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx
      (\H v ee gt r. intret_q H func cenv cx tv v ee r) cenv ty
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[frame_ret_ok_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo`
  >- gvs[type_stmt_def, is_word_type_def] >>
  rename1 `Return (SOME e)` >>
  `cenv'.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
   cenv'.ce_returns_count = 1 /\ cenv'.ce_return_buf = NONE /\
   cenv'.ce_nonreentrant = cenv.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  mp_tac (Q.SPECL
    [`DF`, `lo`, `d`, `ctx`, `shadow_ctx`, `PG`, `func`, `shadow_func`,
     `cx`, `lctx`, `cenv'`, `ty`, `tv`, `es`, `e`, `env`, `rpc`, `slot_size`]
    compile_return_word_int_frag_full) >>
  simp[] >>
  pure_rewrite_tac[stmt_frag_full_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  simp[stmt_exit_ptr_def] >> strip_tac >> simp[] >>
  disj2_tac >> gvs[intret_q_def, result_rel_def] >>
  `return_unlock_state cenv' s = return_unlock_state cenv s` by
    fs[return_unlock_state_def] >>
  qexists_tac `s` >> simp[] >>
  drule_all (Q.INST
    [`es` |-> `ee with <|scopes := []; gas_obs := tail|>`]
    constructor_exit_state_rel) >> simp[]
QED
