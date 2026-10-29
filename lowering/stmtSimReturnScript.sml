(*
 * Statement simulation: return from an internal function (#637, #638)
 *
 * The return statement over stmt_frag (stmtSim), for an internal function
 * that returns one word on the stack: the value's fragment, the optional
 * guard release, then RET with the value and the defined return PC.
 *
 * A tuple of two or more words returned on the stack: the
 * value's fragment leaves a pointer to the tuple in memory, whose words
 * compile_load_tuple_elements loads (an ADD and an MLOAD each) for the RET.
 *
 * TOP-LEVEL:
 *   return_unlock_state          — exact VM epilogue effect (all guards)
 *   intret_q                     — IntRet in result_rel before that effect
 *   intret_q_source_epilogue      — source transient-epilogue bridge
 *   return_unlock_changes_source_relation — old-contract counterevidence
 *   compile_return_word_int_frag — word return, for every outcome of e
 *   compile_return_tuple_int_frag — stack tuple return, for every outcome
 * Helpers: code shape, tuple loads/encoding, execution and scope/index frames.
 *)

Theory stmtSimReturn
Ancestors
  list rich_list pair finite_map fragExec exprSim exprSimLeaves stmtSim
  freshWrites vyperTypeABI
  transientLockProps nonreentrantEquiv context localPtrsProps
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding venomMemDefs
  vyperContext vfmExecution vfmState
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
  intret_q func cenv cx ret_tv v (es : evaluation_state) r <=>
    ?ir s. r = IntRet ir (return_unlock_state cenv s) /\
           LENGTH ir.iret_values = cenv.ce_returns_count /\
           result_rel func ret_tv cenv cx (INR (ReturnException v), es)
             (IntRet ir s)
End

(* Reassociate source return evaluation at the forced-value boundary. *)
Theorem eval_return_forced[local]:
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
    sv.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_def, exec_write2_def, eval_operand_def,
       arithmeticTheory.ADD1] >>
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
Theorem return_unlock_load_frame[local]:
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

Theorem step_persistent_return_unlock[local]:
  !id key s.
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
  eval_operand op s = SOME w /\ eval_operand rpc s = SOME pc ==>
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
  !func cenv cx es s.
    state_rel func cenv cx es s ==>
    state_rel func cenv cx (es with scopes := []) s
Proof
  rw[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
     logs_rel_def, local_ptrs_rel_def, local_region_def, lookup_scopes_def]
QED

Theorem state_rel_return_index[local,simp]:
  !func cenv cx es s n.
    state_rel func cenv cx es (s with vs_inst_idx := n) <=>
    state_rel func cenv cx es s
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
  !func cenv cx ret_tv v es r nr key iv.
    cenv.ce_nonreentrant = (nr,key,T,iv) /\
    intret_q func cenv cx ret_tv v es r ==>
    ?es'.
      (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target key
       else vyperState$return ()) es = (INL (),es') /\
      result_rel func ret_tv cenv cx (INR (ReturnException v),es') r
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `intret_q _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intret_q_def]) >>
  Cases_on `nr` >> Cases_on `iv` >>
  gvs[return_unlock_state_def, result_rel_def, vyperStateTheory.return_def,
      release_nonreentrant_lock_execution] >>
  irule state_rel_transient_update >> simp[]
QED

(* Evidence that the old unchanged-source contract is genuinely false for
   a held transient guard, rather than merely difficult for metis. *)
Theorem return_unlock_changes_source_relation:
  !func cenv cx es s key.
    cenv.ce_nonreentrant = (T,key,T,F) /\
    state_rel func cenv cx es s /\ tload (n2w key) s <> 0w ==>
    ~state_rel func cenv cx es (return_unlock_state cenv s)
Proof
  rpt gen_tac >> strip_tac >>
  simp[return_unlock_state_def] >> strip_tac >>
  qpat_assum `state_rel _ _ _ _ s`
    (mp_tac o GEN_ALL o MATCH_MP state_rel_transient_lookup) >>
  disch_then (qspec_then `n2w key` assume_tac) >>
  qpat_x_assum `state_rel _ _ _ _ (tstore _ _ _)`
    (mp_tac o GEN_ALL o MATCH_MP state_rel_transient_lookup) >>
  disch_then (qspec_then `n2w key` mp_tac) >> simp[]
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

(* return e in an internal function whose result, a word, goes back on the
   stack (ce_returns_count = 1, no return buffer): e's fragment, whose
   errors exit, the exact optional unlock, then RET [operand; return PC]. *)
Theorem compile_return_word_int_frag:
  !ctx func cx lctx cenv ty e es res es' rpc rsz ret_tv.
    eval_stmt cx (Return (SOME e)) es = (res, es') /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_returns_count = 1 /\ cenv.ce_return_buf = NONE /\
    expr_type e = ty /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME ret_tv /\
    expr_sim ctx func cenv cx ty e es /\
    (!sa op sb. lower_value compile_expr cenv ty e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx (intret_q func cenv cx ret_tv) cenv
      (stmt_env cenv lctx ty (Return (SOME e))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv ty e sa` >> rename1 `_ = (op, s1)` >>
  simp[] >>
  Cases_on `compile_internal_return_from_env cenv ty (expr_type e) op (Var rpc) s1` >>
  rename1 `_ = (u, s2)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule_all compile_internal_word_return_code >> strip_tac >>
  `cs_extends sa s1` by metis_tac[] >>
  `cs_extends s1 s2` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND] >> metis_tac[]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    (irule fn_has_code_split >> simp[]) >>
  (* the source *)
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  pure_rewrite_tac[eval_return_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (r1, es1)` >> simp[Once bind_def, raise_def] >> strip_tac >>
  `expr_res_ok r1` by (
    Cases_on `r1`
    >- gvs[expr_res_ok_def] >>
    qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
    simp[bind_def] >> Cases_on `eval_expr cx e es` >>
    rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
    imp_res_tac read_result_no_control >>
    imp_res_tac (cj 1 eval_expr_no_control) >>
    gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- (
    (* the value: RET with it and the return PC *)
    gvs[expr_post_def, return_def] >>
    qpat_x_assum `expr_val_rel _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
    rename1 `eval_operand op sv = SOME w` >>
    `w = typed_val_to_w256 ret_tv v` by
      (qpat_x_assum `!tv. _` (qspec_then `ret_tv` mp_tac) >> simp[]) >>
    `?pc. lookup_var rpc sv = SOME pc` by
      (qpat_x_assum `ret_pc_ok _ _ _` mp_tac >> simp[ret_pc_ok_def] >>
       strip_tac >> rename1 `lookup_var rpc s0 = SOME old_pc` >>
       qexists_tac `old_pc` >> first_x_assum irule >> simp[]) >>
    `run_from 0 ctx func sv =
     IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |>
       (return_unlock_state cenv sv)` by
      (irule internal_word_return_run >>
       qexistsl_tac [`op`, `pc`, `Var rpc`, `s1`, `s2`] >>
       simp[eval_operand_def]) >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func sv <> Error e) ==> _`
      (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
    `state_rel func cenv cx (es' with scopes := []) sv` by
      (irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
    qexists_tac `fuel'` >>
    simp[exit_result_def, stmt_exit_def, intret_q_def] >>
    disj2_tac >> qexists_tac `sv` >>
    simp[result_rel_def] >> metis_tac[intret_vals_match_word]) >>
  qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

(* Integrity gate for the forced return boundary and RET consumer. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "RETURN_FORCE_AUDIT OK\n"
     else raise Fail "forced return inherited admission"
  end) [eval_return_forced, state_rel_scopes_nil, compile_return_word_int_frag];

(* ===== A tuple of words on the stack ===== *)

(* The words compile_load_tuple_elements loads from the tuple at w: one per
   element type, from offset off on, each type's type_memory_bytes on. *)
Definition tuple_words_def:
  tuple_words cenv (w : bytes32) [] off mem = [] /\
  tuple_words cenv w (t::ts) off mem =
    mem_word_at (w2n (w + n2w off)) mem ::
    tuple_words cenv w ts (off + type_memory_bytes cenv t) mem
End

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
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
      fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       venomInstTheory.mk_inst_def, is_terminator_def,
       not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  simp[run_inst_seq_def, step_inst_base_def, exec_pure2_def, exec_read1_def,
       eval_operand_def, bind_outputs_def, lookup_var_update_var] >>
  simp[update_var_def, mload_def, mem_word_at_def, lookup_var_def,
       FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `s with vs_vars := VV` >> qexists `VV` >>
  simp[Abbr `VV`, FLOOKUP_UPDATE] >> rw[] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, DECIDE ``a <= a + 1n``]
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
  rename1 `run_inst_seq (emitted_insts sh sf) _ = OK (_ with vs_vars := vs2)` >>
  `emitted_insts sa sf = emitted_insts sa sh ++ emitted_insts sh sf` by
    metis_tac[emitted_insts_append] >>
  `same_blocks sa sf` by fs[same_blocks_def] >>
  `not_fresh_at sf x` by (irule not_fresh_at_mono >> qexists `sh` >> simp[]) >>
  `run_inst_seq (emitted_insts sa sf) s = OK (s with vs_vars := vs2)` by
    (simp[] >>
     qpat_assum `run_inst_seq (emitted_insts sa sh) _ = OK _`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  `!y. not_fresh_at sa y ==>
       lookup_var y (s with vs_vars := vs2) = lookup_var y s` by
    (rpt strip_tac >>
     `not_fresh_at sh y` by
       (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     metis_tac[]) >>
  `lookup_var x (s with vs_vars := vs2) =
     SOME (mem_word_at (w2n (w + n2w off)) s.vs_memory)` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule not_fresh_at_mono >> qexists `sh` >> simp[]) >>
  qexists `vs2` >>
  simp[eval_operands_def, tuple_words_def, eval_operand_def]
QED

(* A word type takes one word, at the value level and in the lowering. *)
Theorem word_type_sizes[local]:
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
Theorem expr_val_at_bound:
  !func cenv cx t sa sb es v op s tv w.
    stmt_state_rel func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    eval_operand op s = SOME w ==>
    w2n w + val_footprint tv v < dimword (:256)
Proof
  rw[expr_val_at_def] >> first_x_assum (qspec_then `tv` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  TRY (simp[wordsTheory.w2n_lt] >> NO_TAC) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[])
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
     local_region_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Theorem eval_operands_snoc[local]:
  !ops s vals op v.
    eval_operands ops s = SOME vals /\ eval_operand op s = SOME v ==>
    eval_operands (ops ++ [op]) s = SOME (vals ++ [v])
Proof
  Induct >> rw[eval_operands_def] >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

(* RET of the values of ops and the return PC. *)
Theorem step_ret_values[local]:
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
  rpt gen_tac >>
  qspecl_then [`ops`, `s with vs_vars := v`, `n`] mp_tac
    eval_operands_inst_idx >>
  simp[]
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

Theorem intret_vals_match_tuple[local]:
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

(* return e of a tuple of words that goes back on the stack
   (ce_returns_count = LENGTH tys > 1, no return buffer): e's fragment,
   whose errors exit, leaves a pointer to the tuple in memory; the optional
   guard release precedes loading its words and returning with the return PC.
   The pointer's variable, if
   any, was handed out before the loads (a local's is, by
   local_ptrs_reserved), so they do not overwrite it.  Typing is required
   of the value after read_result, including results read from places. *)
Theorem compile_return_tuple_int_frag:
  !ctx func cx lctx cenv e es res es' rpc rsz tys ret_tv.
    eval_stmt cx (Return (SOME e)) es = (res, es') /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_returns_count = LENGTH tys /\ 1 < LENGTH tys /\
    cenv.ce_return_buf = NONE /\
    expr_type e = TupleT tys /\ EVERY is_word_type tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME ret_tv /\
    (!v es1. (do raw <- eval_expr cx e; read_result cx raw od) es =
               (INL v, es1) ==> value_has_type ret_tv v) /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    (!sa op sb. local_ptrs_reserved cenv sa /\
                lower_value compile_expr cenv (TupleT tys) e sa = (op, sb) ==>
                !x. op = Var x ==> not_fresh_at sb x) ==>
    stmt_frag ctx func cx lctx (intret_q func cenv cx ret_tv) cenv
      (stmt_env cenv lctx (TupleT tys) (Return (SOME e))) es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  `LENGTH tys <> 1 /\ 0 < LENGTH tys` by decide_tac >>
  `tys <> []` by (strip_tac >> gvs[]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def,
       compile_internal_return_from_env_def, compile_internal_return_def] >>
  Cases_on `lower_value compile_expr cenv (TupleT tys) e sa` >>
  rename1 `_ = (op, s1)` >> simp[] >>
  Cases_on `compile_return_unlock cenv s1` >>
  rename1 `_ = (uu, su)` >> Cases_on `uu` >> simp[] >>
  Cases_on `compile_load_tuple_elements cenv op tys 0 su` >>
  rename1 `_ = (elems, s2)` >> simp[] >>
  Cases_on `emit_inst RET (elems ++ [Var rpc]) [] s2` >>
  rename1 `_ = (u, s3)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  suspend "code"
QED

Resume compile_return_tuple_int_frag[code]:
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_return_unlock_shape >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at su x` by
    (fs[not_fresh_at_def] >> metis_tac[]) >>
  drule compile_load_tuple_elements_extends >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends s2 s3` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s3 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code s1 su func /\ fn_has_code su s2 func /\
   fn_has_code s1 s2 func /\ fn_has_code s2 s3 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  pure_rewrite_tac[eval_return_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (r1, es1)` >> simp[Once bind_def, raise_def] >> strip_tac >>
  `expr_res_ok r1` by (
    Cases_on `r1`
    >- gvs[expr_res_ok_def] >>
    qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
    simp[bind_def] >> Cases_on `eval_expr cx e es` >>
    rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
    imp_res_tac read_result_no_control >>
    imp_res_tac (cj 1 eval_expr_no_control) >>
    gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- suspend "value" >>
  qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_return_tuple_int_frag[value]:
  rename1 `expr_post func cenv cx e es sa s1 s0 es1 v op sv` >>
  `value_has_type ret_tv v` by
    (qpat_x_assum `!v es1. _ ==> _` (qspecl_then [`v`, `es1`] mp_tac) >>
     simp[]) >>
  drule_all tuple_type_value >> strip_tac >>
  gvs[expr_post_def, return_def] >>
  `~is_word_type (TupleT tys)` by simp[is_word_type_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  `tuple_in_memory vs tvs (w2n w + 0) sv.vs_memory` by
    (first_x_assum (qspec_then `TupleTV tvs` mp_tac) >>
     simp[val_in_memory_def]) >>
  `w2n w + 0 + 32 * LENGTH tys <= dimword (:256)` by
    (drule_all expr_val_at_bound >>
     simp[val_footprint_def, type_memory_size_def] >>
     drule_all word_tuple_size >> simp[]) >>
  `tuple_words cenv w tys 0 sv.vs_memory =
     MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))` by
    (irule tuple_words_typed >> metis_tac[]) >>
  `eval_operand op (return_unlock_state cenv sv) = SOME w` by
    simp[eval_operand_return_unlock] >>
  drule compile_load_tuple_elements_run >>
  disch_then (qspecl_then [`return_unlock_state cenv sv`, `w`] mp_tac) >>
  simp[] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 `run_inst_seq _ (return_unlock_state cenv sv) =
    OK ((return_unlock_state cenv sv) with vs_vars := lvars)` >>
  suspend "loads"
QED

Resume compile_return_tuple_int_frag[loads]:
  qabbrev_tac `words = MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))` >>
  qabbrev_tac `sl = (return_unlock_state cenv sv) with
    <| vs_vars := lvars; vs_inst_idx := LENGTH s2.cs_current_insts |>` >>
  `frag_exec ctx s1 su (\x. x = sv)
     (\x. x = return_unlock_state cenv sv) (\r. F)` by
    (irule compile_return_unlock_frag >> simp[]) >>
  `frag_exec ctx su s2 (\x. x = return_unlock_state cenv sv)
     (\x. x = sl) (\r. F)` by
    (irule frag_exec_run_inst_seq >> fs[same_blocks_def, IS_PREFIX_APPEND3] >>
     simp[Abbr `sl`]) >>
  `frag_exec ctx s1 s2 (\x. x = sv) (\x. x = sl) (\r. F)` by
    (irule frag_exec_seq >>
     qexistsl_tac [`\x. x = return_unlock_state cenv sv`, `su`] >> simp[]) >>
  qpat_x_assum `frag_exec ctx s1 s2 _ _ _` (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `sv`] mp_tac) >> simp[] >> strip_tac >>
  `?pc. lookup_var rpc sl = SOME pc` by
    (qpat_x_assum `ret_pc_ok _ _ _` mp_tac >> simp[ret_pc_ok_def] >>
     strip_tac >>
     `not_fresh_at su rpc` by
       (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     simp[Abbr `sl`, lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  `eval_operands elems sl = SOME words` by
    simp[Abbr `sl`, eval_operands_vars_inst_idx] >>
  suspend "ret"
QED

Resume compile_return_tuple_int_frag[ret]:
  qspecl_then [`s2`, `s3`, `func`,
               `[mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) []]`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb (LENGTH s2.cs_current_insts) =
     SOME (mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) []) sl =
     IntRet <| iret_values := words; iret_adopt_fmp := NONE |> sl` by
    (irule step_ret_values >> metis_tac[]) >>
  `run_from 0 ctx func sl =
     IntRet <| iret_values := words; iret_adopt_fmp := NONE |> sl` by
    (qpat_x_assum `step_inst_base _ sl = _` mp_tac >>
     qpat_x_assum `get_instruction bb _ = _` mp_tac >>
     simp[Abbr `sl`, run_from_def, Once exec_block_def, step_inst_non_invoke,
          venomInstTheory.mk_inst_def] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func sl <> Error e) ==> _`
    (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_from fv ctx func sv = _` >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func sv <> Error e) ==> _`
    (qspec_then `fv` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_from f0 ctx func s0 = _` >>
  suspend "post"
QED

Resume compile_return_tuple_int_frag[post]:
  qabbrev_tac `pre = sv with <| vs_vars := lvars;
    vs_inst_idx := LENGTH s2.cs_current_insts -
      LENGTH (return_unlock_insts cenv s1.cs_next_id) |>` >>
  `sl = return_unlock_state cenv pre` by
    (qunabbrev_tac `sl` >> qunabbrev_tac `pre` >>
     irule return_unlock_load_frame >> fs[same_blocks_def]) >>
  `state_rel func cenv cx (es' with scopes := []) pre` by
    (irule state_rel_frame >>
     simp[local_ptrs_rel_def, lookup_scopes_def, local_region_def] >>
     qexistsl [`es' with scopes := []`, `sv`] >> simp[Abbr `pre`] >>
     irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
  `LENGTH vs = LENGTH tvs /\ LENGTH tvs = LENGTH tys` by
    (drule values_have_types_length >> drule LIST_REL_LENGTH >> simp[]) >>
  `LENGTH words = LENGTH tys` by simp[Abbr `words`, LENGTH_ZIP] >>
  qexists_tac `f0` >>
  simp[exit_result_def, stmt_exit_def, intret_q_def] >>
  disj2_tac >> qexists_tac `pre` >>
  simp[result_rel_def, Abbr `words`] >>
  irule intret_vals_match_tuple >> simp[]
QED

Finalise compile_return_tuple_int_frag

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("internal return simulation is not kernel closed: " ^ name)
  end) (DB.thms "stmtSimReturn");
(* Check that the tuple consumer, including every resumed path, is closed. *)
val () =
  let val th = compile_return_tuple_int_frag
      val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "RETURN_FORCE_AUDIT tuple OK\n"
     else raise Fail "forced tuple return inherited admission"
  end;
