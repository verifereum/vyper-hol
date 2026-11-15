(* Calldata dynamic-allocation instruction shape and execution.
 * The prefix stops before DALLOCA, so its operand bound needs no FMP room.
 *)
Theory dallocaCalldata
Ancestors
  dallocaCreateCopy dallocaCreateBlueprint dallocaBlueprintArgs dallocaCreateGeometry
  builtinSystem context exprLoweringProps emitHelper emitHelperProps compileEnv
  loweringStateRelDefs
  venomExecSemantics venomInst venomState list rich_list words finite_map

(* The temporary allocation is deliberately described without fmp_room:
   its bumped pointer can wrap, while the copy uses natural offsets. *)
Theorem calldata_memory_insts:
  !sa ptr len sb. compile_msg_data_to_memory sa = ((ptr,len),sb) ==>
  ptr = Var ("%" ++ toString (sa.cs_next_var + 1)) /\
  len = Var ("%" ++ toString sa.cs_next_var) /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id CALLDATASIZE [] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) DALLOCA
       [Var ("%" ++ toString sa.cs_next_var)]
       ["%" ++ toString (sa.cs_next_var + 1)];
     mk_inst (sa.cs_next_id + 2) CALLDATACOPY
       [Var ("%" ++ toString (sa.cs_next_var + 1)); Lit 0w;
        Var ("%" ++ toString sa.cs_next_var)] []]
Proof
  simp[compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem calldata_memory_run:
  !sa ptr len sb s.
  compile_msg_data_to_memory sa = ((ptr,len),sb) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ptr t = SOME s.vs_fmp /\
    eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    t.vs_memory = (write_memory_with_expansion (w2n s.vs_fmp)
      s.vs_call_ctx.cc_calldata s).vs_memory /\
    t.vs_fmp = s.vs_fmp + n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t = s with <| vs_vars := t.vs_vars; vs_memory := t.vs_memory;
                  vs_fmp := t.vs_fmp |>
Proof
  rpt gen_tac >> strip_tac >> drule calldata_memory_insts >> strip_tac >>
  gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read0_def, eval_operand_def, bind_outputs_def,
       lookup_var_update_var] >>
  simp[update_var_def, lookup_var_def, not_fresh_at_def,
       wordsTheory.w2n_n2w, TAKE_APPEND1] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.w2n_n2w,
       TAKE_APPEND1, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem calldata_memory_prefix:
  !sa ptr len sb s.
    compile_msg_data_to_memory sa = ((ptr,len),sb) /\
    LENGTH s.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    ?t. run_inst_seq (TAKE 1 (emitted_insts sa sb)) s = OK t /\
      eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_fmp = s.vs_fmp /\
      w2n (n2w (LENGTH s.vs_call_ctx.cc_calldata) : bytes32) < 2 ** 64
Proof
  rpt gen_tac >> strip_tac >>
  drule calldata_memory_insts >> strip_tac >> gvs[] >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by
    (fs[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >> decide_tac) >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read0_def, bind_outputs_def, eval_operand_def,
       lookup_var_update_var, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.w2n_n2w]
QED
