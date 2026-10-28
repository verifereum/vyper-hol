(*
 * Internal calls: the callee's side of a memory-backed return (#637, #638)
 *
 * An internal function whose result does not go back on the stack
 * (ce_returns_count = 0) gets a return buffer from its caller, the first
 * INVOKE operand.  return e stores e's value into that buffer
 * (compile_store_memory) and returns with RET and only the return PC.
 *
 * TOP-LEVEL:
 *   intret_mem_q — the RetQ of such a function: intret_q, with the
 *                  returned value in memory at the caller's buffer
 *   compile_internal_return_memory_frag — unlock, store and RET, from a
 *                  state where the value's operand holds it, end in an
 *                  IntRet that the exact intret_mem_q accepts
 * Helper:
 *   compile_internal_return_memory_frag_raw — store/RET without the unlock
 *)

Theory intCallReturnMem
Ancestors
  list rich_list
  fragExec exprSim stmtSimReturn intCallResult valueCopy instIdxIndep
  stmtLowering exprLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv valueEncoding
  vyperState vyperTyping venomExecSemantics venomInst venomState

(* An internal function's memory return: an IntRet satisfying the exact
   epilogue-aware intret_q (zero stack words when ce_returns_count = 0),
   with the returned value in the caller's buffer at address buf. *)
Definition intret_mem_q_def:
  intret_mem_q func cenv cx ret_tv (buf:bytes32) v
               (es : evaluation_state) r <=>
    intret_q func cenv cx ret_tv v es r /\
    ?ir s. r = IntRet ir s /\ val_in_memory ret_tv v (w2n buf) s.vs_memory
End

(* The low-level helper emits no unlock.  Keep its result explicitly raw;
   only the environment/epilogue-level theorem below promises intret_q. *)
Definition intret_mem_q_raw_def:
  intret_mem_q_raw func cenv cx ret_tv (buf:bytes32) v
                   (es : evaluation_state) r <=>
    ?ir s. r = IntRet ir s /\ ir.iret_values = [] /\
      result_rel func ret_tv cenv cx (INR (ReturnException v), es) r /\
      val_in_memory ret_tv v (w2n buf) s.vs_memory
End

(* RET with only the return PC: an IntRet with no values. *)
Theorem emit_ret_pc_frag[local]:
  !ctx sm sb rpc P Q R.
    emit_inst RET [rpc] [] sm = ((),sb) /\
    (!s. P s ==> (?pc. eval_operand rpc s = SOME pc) /\
                 R (IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s))
    ==>
    frag_exec ctx sm sb P Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[frag_exec_def] >> rpt strip_tac >> disj2_tac >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `run_from 0 ctx fn s =
     IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s` by
    simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
         mk_inst_def, step_inst_base_def, eval_operands_def] >>
  qexists_tac `0` >> simp[exit_result_def]
QED

(* Raw memory return with a literal zero stack-result count, independent
   of ce_returns_count and without any guard release.  After e's fragment,
   whose operand val_op holds
   e's value v (expr_val_rel): compile_store_memory copies v into the
   caller's buffer at bw, and RET returns.  The state relation is the one
   the return hands on, at the source state without its scopes (stmt_exit),
   so no local's region constrains the copy.  type_memory_bytes, the size
   the copy uses, is the compile environment's account of the size of v's
   type (build_compile_env_type_memory_bytes).  Only a return of e's own
   type is covered: compile_internal_return_from_env passes e's type as
   both the return type and the source type. *)
Theorem compile_internal_return_memory_frag_raw:
  !ctx func cenv cx es ty tv v val_op rpc elem_types buf_op sa sb bw.
    compile_internal_return cenv (SOME val_op) rpc 0 ty ty elem_types
      (SOME buf_op) sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
    w2n bw + type_memory_size tv + 64 < dimword (:256) ==>
    frag_exec ctx sa sb
      (\s. stmt_state_rel func cenv cx (es with scopes := []) s /\
           expr_val_rel cx ty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q_raw func cenv cx tv bw v (es with scopes := []))
Proof
  rpt gen_tac >> strip_tac >>
  (* the shape needs one state to run the store from *)
  reverse (Cases_on `?s0. stmt_state_rel func cenv cx (es with scopes := []) s0 /\
                          expr_val_rel cx ty v val_op s0 /\
                          eval_operand buf_op s0 = SOME bw`)
  >- (simp[frag_exec_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_store_memory cenv val_op buf_op ty ty sa` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ s0`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`cenv`, `val_op`, `buf_op`, `ty`, `sa`, `sm`, `s0`,
               `get_tenv cx`, `tv`, `v`, `w`, `bw`]
    mp_tac compile_store_memory_run >>
  impl_tac >- simp[] >> strip_tac >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends sm sb` by (irule cs_extends_emit_inst >> metis_tac[]) >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s. stmt_state_rel func cenv cx (es with scopes := []) s /\
                     val_in_memory tv v (w2n bw) s.vs_memory /\
                     ?pc. eval_operand rpc s = SOME pc`, `sm`] >>
  simp[] >> rpt conj_tac
  >~ [`frag_exec _ _ _ _ (\s. F) _`]
  >- (irule emit_ret_pc_frag >> qexists_tac `rpc` >> simp[] >>
      rpt strip_tac >>
      gvs[intret_mem_q_raw_def, result_rel_def,
          intret_vals_match_def, stmt_state_rel_def]) >>
  suspend "store"
QED

Resume compile_internal_return_memory_frag_raw[store]:
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def, IS_PREFIX_APPEND] >>
  rpt strip_tac >> disj1_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  rename1 `eval_operand val_op s = SOME sw` >>
  qspecl_then [`cenv`, `val_op`, `buf_op`, `ty`, `sa`, `sm`, `s`,
               `get_tenv cx`, `tv`, `v`, `sw`, `bw`]
    mp_tac compile_store_memory_run >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq _ s = OK t1` >>
  qexists_tac `t1` >> simp[stmt_state_rel_inst_idx, eval_op_inst_idx] >>
  conj_tac
  >- (irule result_state_memory_frame >> qexists_tac `s` >>
      simp[local_region_def, lookup_scopes_def]) >>
  qexists_tac `pc` >>
  qspecl_then [`rpc`, `sa`, `s`, `t1`] mp_tac store_result_operand_frame >>
  simp[]
QED

Finalise compile_internal_return_memory_frag_raw

(* Memory and fresh-variable writes commute with the exact epilogue.  The
   index on the pre-unlock witness omits precisely the release instruction. *)
Theorem return_unlock_memory_frame[local]:
  !cenv s vars mem n id.
    LENGTH (return_unlock_insts cenv id) <= n ==>
    (return_unlock_state cenv s) with
      <|vs_vars := vars; vs_memory := mem; vs_inst_idx := n|> =
    return_unlock_state cenv
      (s with <|vs_vars := vars; vs_memory := mem;
                vs_inst_idx := n - LENGTH (return_unlock_insts cenv id)|>)
Proof
  rpt gen_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, return_unlock_insts_def,
       tstore_def, sstore_def] >>
  strip_tac >> `SUC (n - 1) = n` by decide_tac >> simp[]
QED

(* TOP-LEVEL: release every applicable guard, copy to the caller's buffer,
   and return no stack words.  Unlike the raw helper this is the exact
   epilogue-aware contract, including persistent and transient guards. *)
Theorem compile_internal_return_memory_frag:
  !ctx func cenv cx es ty tv v val_op rpc elem_types buf_op sa su sb bw.
    compile_return_unlock cenv sa = ((),su) /\
    compile_internal_return cenv (SOME val_op) rpc cenv.ce_returns_count
      ty ty elem_types (SOME buf_op) su = ((),sb) /\
    cenv.ce_returns_count = 0 /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
    w2n bw + type_memory_size tv + 64 < dimword (:256) ==>
    frag_exec ctx sa sb
      (\s. stmt_state_rel func cenv cx (es with scopes := []) s /\
           expr_val_rel cx ty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q func cenv cx tv bw v (es with scopes := []))
Proof
  rpt gen_tac >> strip_tac >>
  simp[frag_exec_def] >> rpt strip_tac >>
  rename1 `stmt_state_rel func cenv cx (es with scopes := []) s0` >>
  drule compile_return_unlock_shape >> strip_tac >>
  `(!x. val_op = Var x ==> not_fresh_at su x) /\
   (!x. buf_op = Var x ==> not_fresh_at su x) /\
   (!x. rpc = Var x ==> not_fresh_at su x)` by
    (fs[not_fresh_at_def] >> metis_tac[]) >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_store_memory cenv val_op buf_op ty ty su` >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ s0`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`cenv`, `val_op`, `buf_op`, `ty`, `su`, `sm`,
               `return_unlock_state cenv s0`, `get_tenv cx`, `tv`, `v`, `w`, `bw`]
    mp_tac compile_store_memory_run >>
  impl_tac >- simp[eval_operand_return_unlock] >> strip_tac >>
  rename1 `run_inst_seq _ (return_unlock_state cenv s0) = OK t` >>
  suspend "frame"
QED

Resume compile_internal_return_memory_frag[frame]:
  `t = (return_unlock_state cenv s0) with
       <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. z with <|vs_vars := t.vs_vars;
                                         vs_memory := t.vs_memory|>``) >> simp[]) >>
  qabbrev_tac `pre = s0 with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
    vs_inst_idx := LENGTH sm.cs_current_insts -
      LENGTH (return_unlock_insts cenv sa.cs_next_id)|>` >>
  `t with vs_inst_idx := LENGTH sm.cs_current_insts =
     return_unlock_state cenv pre` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_memory := _|>`
       (fn th => once_rewrite_tac[th]) >>
     qspecl_then [`cenv`, `s0`, `t.vs_vars`, `t.vs_memory`,
                  `LENGTH sm.cs_current_insts`, `sa.cs_next_id`]
       mp_tac return_unlock_memory_frame >> simp[Abbr `pre`]) >>
  `stmt_state_rel func cenv cx (es with scopes := [])
     (s0 with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>)` by
    (irule result_state_memory_frame >> qexists_tac `s0` >>
     simp[local_region_def, lookup_scopes_def]) >>
  `stmt_state_rel func cenv cx (es with scopes := []) pre` by
    (qspecl_then [`func`, `cenv`, `cx`, `es with scopes := []`,
       `s0 with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>`,
       `LENGTH sm.cs_current_insts -
          LENGTH (return_unlock_insts cenv sa.cs_next_id)`]
       mp_tac stmt_state_rel_inst_idx >> simp[Abbr `pre`]) >>
  suspend "fragments"
QED

Resume compile_internal_return_memory_frag[fragments]:
  `cs_extends su sm` by
    (irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends sm sb` by (irule cs_extends_emit_inst >> metis_tac[]) >>
  `frag_exec ctx sa su (\s. s = s0)
     (\s. s = return_unlock_state cenv s0)
     (intret_mem_q func cenv cx tv bw v (es with scopes := []))` by
    (irule frag_exec_conseq >>
     qexistsl_tac [`\s. s = s0`, `\s. s = return_unlock_state cenv s0`,
                   `\r. F`] >> simp[] >>
     irule compile_return_unlock_frag >> simp[]) >>
  `frag_exec ctx su sm (\s. s = return_unlock_state cenv s0)
     (\s. s = return_unlock_state cenv pre)
     (intret_mem_q func cenv cx tv bw v (es with scopes := []))` by
    (irule frag_exec_run_inst_seq >>
     fs[same_blocks_def, IS_PREFIX_APPEND] >>
     qpat_x_assum `t with vs_inst_idx := _ = _` mp_tac >> simp[]) >>
  `eval_operand rpc t = SOME pc` by
    (qspecl_then [`rpc`, `su`, `return_unlock_state cenv s0`, `t`]
       mp_tac store_result_operand_frame >> simp[eval_operand_return_unlock]) >>
  `eval_operand rpc (return_unlock_state cenv pre) = SOME pc` by
    (qpat_x_assum `t with vs_inst_idx := _ = _`
       (mp_tac o AP_TERM ``eval_operand rpc``) >> simp[eval_op_inst_idx]) >>
  `frag_exec ctx sm sb (\s. s = return_unlock_state cenv pre) (\s. F)
     (intret_mem_q func cenv cx tv bw v (es with scopes := []))` by
    (irule emit_ret_pc_frag >> qexists_tac `rpc` >> simp[] >>
     simp[intret_mem_q_def, intret_q_def, result_rel_def,
          intret_vals_match_def] >>
     conj_tac >- (qexists_tac `pre` >> fs[stmt_state_rel_def]) >>
     simp[Abbr `pre`]) >>
  `frag_exec ctx sa sb (\s. s = s0) (\s. F)
     (intret_mem_q func cenv cx tv bw v (es with scopes := []))` by
    (irule frag_exec_seq >>
     qexistsl_tac [`\s. s = return_unlock_state cenv pre`, `sm`] >> simp[] >>
     conj_tac >- metis_tac[cs_extends_trans] >>
     irule frag_exec_seq >>
     qexistsl_tac [`\s. s = return_unlock_state cenv s0`, `su`] >> simp[]) >>
  qpat_x_assum `frag_exec ctx sa sb _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`fn`, `s0`] mp_tac) >> simp[]
QED

Finalise compile_internal_return_memory_frag

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("internal memory return is not kernel closed: " ^ name)
  end) (DB.thms "intCallReturnMem");
