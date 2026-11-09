(* Internal return relations and shared value/layout/RET facts. *)

Theory stmtSimReturn
Ancestors
  stmtSimProps
  exprSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts exprSimTypedAlloc
  gasContext gasExemptCert
  fragGasOriginPtr bodyPtrDefs gasSummary bodySimFull gasOutcomeFull bodySim
  list rich_list finite_map fragExec freshWrites
  vyperTypeABI
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding venomMemDefs
  vyperInterpreter vyperState vyperValue vyperTyping vyperExprNoControl vyperTypeSystem
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

Theorem intret_q_gas_obs:
  intret_q func cenv cx ret_tv v (es with gas_obs := readings) r =
  intret_q func cenv cx ret_tv v es r
Proof
  simp[intret_q_def, result_rel_gas_obs]
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

Theorem constructor_exit_state_rel:
  same_frame cenv cenv' /\ state_rel func cenv' cx es s ==>
  state_rel func cenv cx (es with scopes := []) s
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

Theorem compile_return_none_int_origin_ptr:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
  compile_stmt cenv lctx ty (Return NONE) sa = ((), sb) /\
  fn_has_code sa sb func /\ ret_pc_ok cenv sa s /\
  ~ctx_has_dalloca ctx /\ stmt_state_rel ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r.
    r = IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) [] (r, G, tn) /\
    (!tail. eval_stmt cx (Return NONE)
      (es with gas_obs := gas_explicit [] s.vs_gas_readings ++ tail) =
      (INR (ReturnException NoneV), es with gas_obs := tail)) /\
    intret_q func cenv cx ret_tv NoneV (es with scopes := []) r /\
    op_taint tn (Var rpc) = {}
Proof
  strip_tac >>
  `emit_inst RET [Var rpc] [] sa = ((), sb)` by
    gvs[Once compile_stmt_def] >>
  `op_taint tn (Var rpc) = {}` by
    metis_tac[ghost_inv_at_def] >>
  `?pc. lookup_var rpc s = SOME pc` by
    metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `!fuel. step_inst fuel ctx (mk_inst sa.cs_next_id RET [Var rpc] []) s =
     IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     mp_tac (Q.SPECL [`sa.cs_next_id`, `[]`, `rpc`, `s`, `[]`, `pc`]
       step_ret_values) >> simp[eval_operands_def, mk_inst_def]) >>
  conj_tac
  >- (irule (cj 3 gas_origin_ptr_path_rules) >>
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
      metis_tac[ghost_inv_at_def]) >>
  conj_tac >- simp[Once evaluate_def, raise_def] >>
  simp[intret_q_def, result_rel_def, intret_vals_match_def] >>
  irule state_rel_scopes_nil >> gvs[stmt_state_rel_def]
QED

Theorem compile_return_none_int_frag_full:
  !D lo d ctx shadow_ctx PG func shadow_func
   cx lctx cenv ty ret_tv es rpc slot_size.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) ==>
    stmt_frag_full
      (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx
      (\v ee gt r. intret_q func cenv cx ret_tv v ee r)
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
  drule_all (Q.INST [`s` |-> `s0`, `G` |-> `G0`, `tn` |-> `tn0`,
                    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
               compile_return_none_int_origin_ptr) >>
  disch_then (qspecl_then [`shadow_ctx`, `ret_tv`, `PG`] strip_assume_tac) >>
  pure_rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `r`, `G0`, `tn0`] >>
  simp[gas_explicit_def, exit_result_def, stmt_exit_ptr_def, intret_q_gas_obs] >>
  gen_tac >> disj2_tac >> gvs[] >>
  qpat_x_assum `intret_q _ _ _ _ _ _ _` mp_tac >>
  simp[intret_q_def, result_rel_def, state_rel_def, storage_rel_def,
       transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def] >>
  metis_tac[]
QED

Theorem internal_frame_ret_none_full:
  !D lo d ctx shadow_ctx PG func shadow_func cx cenv ret_tv rpc slot_size.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) ==>
    frame_ret_ok_full
      (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx
      (\v ee gt r. intret_q func cenv cx ret_tv v ee r) cenv NoneT
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[frame_ret_ok_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo` >> fs[type_stmt_def] >>
  `cenv'.ce_return_pc = SOME (PtrVar (Var rpc) slot_size)` by
    fs[same_frame_def, compile_env_component_equality] >>
  mp_tac (Q.SPECL
    [`D`, `lo`, `d`, `ctx`, `shadow_ctx`, `PG`, `func`, `shadow_func`,
     `cx`, `lctx`, `cenv'`, `NoneT`, `ret_tv`, `es`, `rpc`, `slot_size`]
    compile_return_none_int_frag_full) >>
  simp[] >>
  pure_rewrite_tac[stmt_frag_full_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  simp[stmt_exit_ptr_def] >> strip_tac >> simp[] >>
  disj2_tac >> gvs[intret_q_def, result_rel_def] >>
  drule_all (Q.INST
    [`es` |-> `ee with <|scopes := []; gas_obs := tail|>`]
    constructor_exit_state_rel) >> simp[]
QED
