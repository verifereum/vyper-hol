(*
 * Statement simulation: return from an internal function (#637, #638)
 *
 * The return statement over stmt_frag (stmtSim), for an internal function
 * that returns one word on the stack: the value's fragment, then RET with
 * the value and the return PC, which ret_pc_ok in stmt_frag keeps defined.
 *
 * A tuple of two or more words returned on the stack: the
 * value's fragment leaves a pointer to the tuple in memory, whose words
 * compile_load_tuple_elements loads (an ADD and an MLOAD each) for the RET.
 *
 * TOP-LEVEL:
 *   intret_q                      — the RetQ of such a function: an IntRet
 *                                   in result_rel with the returned value
 *   intret_vals_match_word        — a word returns as its typed encoding
 *   compile_return_word_int_frag  — return e, for every outcome of e
 *   compile_return_tuple_int_frag — return e of a tuple of words, for every
 *                                   outcome of e
 *
 * Helpers: tuple_words, compile_load_tuple_elements_run, tuple_words_typed,
 *   expr_val_at_bound
 *)

Theory stmtSimReturn
Ancestors
  list rich_list finite_map fragExec exprSim exprSimLeaves stmtSim freshWrites
  vyperTypeABI
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding venomMemDefs
  vyperInterpreter vyperState vyperValue vyperTyping vyperExprNoControl
  vyperStatePreservation
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* An internal function's return, related to the source's as result_rel
   (compileEnv) does: an IntRet whose values match v, adopting no free
   memory pointer, with state_rel at the source state without its scopes.
   intret_vals_match checks the values only for stack returns; a memory
   return's are not on the stack. *)
Definition intret_q_def:
  intret_q func cenv cx ret_tv v (es : evaluation_state) r <=>
    ?ir s. r = IntRet ir s /\
           result_rel func ret_tv cenv cx (INR (ReturnException v), es) r
End

(* No scope holds a local once the frame is left. *)
Theorem state_rel_scopes_nil:
  !func cenv cx es s.
    state_rel func cenv cx es s ==>
    state_rel func cenv cx (es with scopes := []) s
Proof
  rw[state_rel_def, storage_rel_def, transient_rel_def, immutables_rel_def,
     logs_rel_def, local_ptrs_rel_def, local_region_def, lookup_scopes_def]
QED

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
   errors exit, then RET [e's operand; the return PC]. *)
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
       comp_ignore_bind_def, comp_return_def,
       compile_internal_return_from_env_def, compile_internal_return_def,
       word_type_elem_types] >>
  Cases_on `lower_value compile_expr cenv ty e sa` >> rename1 `_ = (op, s1)` >>
  simp[] >>
  Cases_on `emit_inst RET [op; Var rpc] [] s1` >> rename1 `_ = (u, s2)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends sa s1` by metis_tac[] >>
  `cs_extends s1 s2` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_split] >>
  qspecl_then [`s1`, `s2`, `func`, `[mk_inst s1.cs_next_id RET [op; Var rpc] []]`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb (LENGTH s1.cs_current_insts) =
     SOME (mk_inst s1.cs_next_id RET [op; Var rpc] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
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
       strip_tac >> qexists_tac `w'` >> first_x_assum irule >> simp[]) >>
    `run_from 0 ctx func sv =
     IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |> sv` by
      simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
           venomInstTheory.mk_inst_def, step_inst_base_def,
           eval_operands_def, eval_operand_def] >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func sv <> Error e) ==> _`
      (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
    `state_rel func cenv cx (es' with scopes := []) sv` by
      (irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
    qexists_tac `fuel'` >>
    simp[exit_result_def, stmt_exit_def, intret_q_def, result_rel_def] >>
    metis_tac[intret_vals_match_word]) >>
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
   whose errors exit, leaves a pointer to the tuple in memory; its words
   are loaded and returned with the return PC.  The pointer's variable, if
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
  Cases_on `compile_load_tuple_elements cenv op tys 0 s1` >>
  rename1 `_ = (elems, s2)` >> simp[] >>
  Cases_on `emit_inst RET (elems ++ [Var rpc]) [] s2` >>
  rename1 `_ = (u, s3)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  suspend "code"
QED

Resume compile_return_tuple_int_frag[code]:
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at s1 x` by metis_tac[] >>
  drule compile_load_tuple_elements_extends >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends s2 s3` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s3 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 s3 func` by
    metis_tac[fn_has_code_split] >>
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
  drule compile_load_tuple_elements_run >>
  disch_then (qspecl_then [`sv`, `w`] mp_tac) >> simp[] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 `run_inst_seq _ sv = OK (sv with vs_vars := lvars)` >>
  suspend "loads"
QED

Resume compile_return_tuple_int_frag[loads]:
  qabbrev_tac `words = MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))` >>
  qabbrev_tac `sl = sv with <| vs_vars := lvars; vs_inst_idx := LENGTH s2.cs_current_insts |>` >>
  `frag_exec ctx s1 s2 (\x. x = sv) (\x. x = sl) (\r. F)` by
    (irule frag_exec_run_inst_seq >> fs[same_blocks_def, IS_PREFIX_APPEND3] >>
     simp[Abbr `sl`]) >>
  qpat_x_assum `frag_exec ctx s1 s2 _ _ _` (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `sv`] mp_tac) >> simp[] >> strip_tac >>
  `?pc. lookup_var rpc sl = SOME pc` by
    (qpat_x_assum `ret_pc_ok _ _ _` mp_tac >> simp[ret_pc_ok_def] >>
     strip_tac >>
     `not_fresh_at s1 rpc` by
       (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     simp[Abbr `sl`, lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  `eval_operands elems sl = SOME words` by
    simp[Abbr `sl`, eval_operands_vars_inst_idx] >>
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
  `state_rel func cenv cx (es' with scopes := []) sl` by
    (irule state_rel_frame >>
     simp[local_ptrs_rel_def, lookup_scopes_def, local_region_def] >>
     qexistsl [`es' with scopes := []`, `sv`] >> simp[Abbr `sl`] >>
     irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
  `LENGTH vs = LENGTH tvs /\ LENGTH tvs = LENGTH tys` by
    (drule values_have_types_length >> drule LIST_REL_LENGTH >> simp[]) >>
  qexists_tac `f0` >>
  simp[exit_result_def, stmt_exit_def, intret_q_def, result_rel_def,
       Abbr `words`] >>
  disj2_tac >> irule intret_vals_match_tuple >> simp[]
QED

Finalise compile_return_tuple_int_frag

(* Check that the tuple consumer, including every resumed path, is closed. *)
val () =
  let val th = compile_return_tuple_int_frag
      val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "RETURN_FORCE_AUDIT tuple OK\n"
     else raise Fail "forced tuple return inherited admission"
  end;
