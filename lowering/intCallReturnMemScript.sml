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
 *   compile_internal_return_memory_frag — the store and the RET, from a
 *                  state where the value's operand holds it, end in an
 *                  IntRet that intret_mem_q accepts
 *)

Theory intCallReturnMem
Ancestors
  list rich_list
  fragExec exprSim stmtSimReturn intCallResult valueCopy instIdxIndep
  stmtLowering exprLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv valueEncoding
  vyperState vyperTyping venomExecSemantics venomInst venomState

(* An internal function's memory return: an IntRet that intret_q accepts
   (its stack values are none, as intret_vals_match allows), where the
   caller's return buffer, at address buf, holds the returned value. *)
Definition intret_mem_q_def:
  intret_mem_q func cenv cx ret_tv (buf:bytes32) v
               (es : evaluation_state) r <=>
    intret_q func cenv cx ret_tv v es r /\
    ?ir s. r = IntRet ir s /\ val_in_memory ret_tv v (w2n buf) s.vs_memory
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

(* return e in an internal function with a memory return
   (ce_returns_count = 0), after e's fragment, whose operand val_op holds
   e's value v (expr_val_rel): compile_store_memory copies v into the
   caller's buffer at bw, and RET returns.  The state relation is the one
   the return hands on, at the source state without its scopes (stmt_exit),
   so no local's region constrains the copy.  type_memory_bytes, the size
   the copy uses, is the compile environment's account of the size of v's
   type (build_compile_env_type_memory_bytes).  Only a return of e's own
   type is covered: compile_internal_return_from_env passes e's type as
   both the return type and the source type. *)
Theorem compile_internal_return_memory_frag:
  !ctx func cenv cx es ty tv v val_op rpc elem_types buf_op sa sb bw.
    compile_internal_return cenv (SOME val_op) rpc 0 ty ty elem_types
      (SOME buf_op) sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
    w2n bw + type_memory_size tv + 64 < dimword (:256) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint off (type_memory_size itv) (w2n bw)
         (type_memory_size tv)) ==>
    frag_exec ctx sa sb
      (\s. stmt_state_rel func cenv cx (es with scopes := []) s /\
           expr_val_rel cx ty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q func cenv cx tv bw v (es with scopes := []))
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
      gvs[intret_mem_q_def, intret_q_def, result_rel_def,
          intret_vals_match_def, stmt_state_rel_def]) >>
  suspend "store"
QED

Resume compile_internal_return_memory_frag[store]:
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def, IS_PREFIX_APPEND] >>
  rpt strip_tac >> disj1_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  rename1 `eval_operand val_op s = SOME sw` >>
  `w2n bw + type_memory_size tv + 64 < dimword (:256)` by decide_tac >>
  drule_all compile_store_memory_run_capacity >> strip_tac >>
  rename1 `run_inst_seq _ s = OK t1` >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (es with scopes := []) s` by fs[stmt_state_rel_def, state_rel_def] >>
  `t1.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o AP_TERM ``\z. z.vs_data_section``) >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (es with scopes := []) t1` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >> qexists_tac `s` >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> simp[regions_disjoint_def] >> strip_tac >>
     first_x_assum irule >> simp[]) >>
  qexists_tac `t1` >> simp[stmt_state_rel_inst_idx, eval_op_inst_idx] >>
  conj_tac
  >- (irule result_state_memory_frame >> simp[] >> qexists_tac `s` >>
      simp[local_region_def, lookup_scopes_def] >>
      fs[venom_state_component_equality]) >>
  qexists_tac `pc` >>
  qspecl_then [`rpc`, `sa`, `s`, `t1`] mp_tac store_result_operand_frame >>
  simp[]
QED

Finalise compile_internal_return_memory_frag
