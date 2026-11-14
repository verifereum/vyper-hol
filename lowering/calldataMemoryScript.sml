(* The actual calldata scratch allocation and copy, shared by lowering proofs. *)
Theory calldataMemory
Ancestors
  builtinSystem context emitHelper emitHelperProps compileEnv exprLoweringProps
  loweringStateRelDefs memoryReadProps
  venomExecSemantics venomExecProofs venomState venomInst venomMemProps venomLayout
  list rich_list finite_map words arithmetic ASCIInumbers

Theorem calldata_memory_insts[local]:
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

Theorem calldata_memory_readback:
  !sa ptr len sb s.
  compile_msg_data_to_memory sa = ((ptr,len),sb) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ptr t = SOME s.vs_fmp /\
    eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    read_memory (w2n s.vs_fmp) (LENGTH s.vs_call_ctx.cc_calldata) t =
      s.vs_call_ctx.cc_calldata /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\
    (!off n. off + n <= w2n s.vs_fmp ==>
      mem_bytes_at off n t.vs_memory = mem_bytes_at off n s.vs_memory)
Proof
  rpt strip_tac >> drule_all calldata_memory_run >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `t = s with <| vs_vars := _; vs_memory := _; vs_fmp := _ |>`
       SUBST1_TAC >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac
  >- (mp_tac (Q.SPECL [`w2n s.vs_fmp`, `s.vs_call_ctx.cc_calldata`, `s`]
               read_memory_write_self) >> simp[read_memory_def]) >>
  rpt strip_tac >>
  mp_tac (Q.SPECL [`off`, `n`, `w2n s.vs_fmp`,
                    `s.vs_call_ctx.cc_calldata`, `s`] read_memory_write_disjoint) >>
  simp[read_memory_eq_mem_bytes_at]
QED

(* The copy materializes all allocated bytes; rounding leaves at most 31
   unwritten bytes. No-wrap is an execution premise, not a compiler guard. *)
Theorem calldata_memory_covered_run:
  !sa ptr len sb s.
  compile_msg_data_to_memory sa = ((ptr,len),sb) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  w2n s.vs_fmp + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
    dimword (:256) /\
  w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
  w2n s.vs_fmp <= MAX (w2n s.vs_initial_fmp) (LENGTH s.vs_memory + 31) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ptr t = SOME s.vs_fmp /\
    eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    read_memory (w2n s.vs_fmp) (LENGTH s.vs_call_ctx.cc_calldata) t =
      s.vs_call_ctx.cc_calldata /\
    t.vs_initial_fmp = s.vs_initial_fmp /\
    w2n t.vs_fmp = w2n s.vs_fmp +
      venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) /\
    w2n t.vs_initial_fmp <= w2n t.vs_fmp /\
    w2n t.vs_fmp <= MAX (w2n t.vs_initial_fmp) (LENGTH t.vs_memory + 31) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t = s with <| vs_vars := t.vs_vars; vs_memory := t.vs_memory;
                  vs_fmp := t.vs_fmp |>
Proof
  rpt strip_tac >> drule_all calldata_memory_run >> strip_tac >>
  `t.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_x_assum `t = s with <| vs_vars := _; vs_memory := _; vs_fmp := _ |>`
       SUBST1_TAC >> simp[]) >>
  `venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) < dimword (:256)` by
    decide_tac >>
  `w2n t.vs_fmp = w2n s.vs_fmp +
    venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata)` by
    (mp_tac (Q.ISPECL [`s.vs_fmp`,
       `(n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))):bytes32`]
       (Q.GENL [`a`, `b`] w2n_add_2)) >> simp[]) >>
  `LENGTH t.vs_memory = MAX (LENGTH s.vs_memory)
    (w2n s.vs_fmp + LENGTH s.vs_call_ctx.cc_calldata)` by
    simp[LENGTH_write_memory_with_expansion] >>
  `venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <=
    LENGTH s.vs_call_ctx.cc_calldata + 31` by
    (rw[venomLayoutTheory.ceil32_def] >> decide_tac) >>
  `w2n t.vs_initial_fmp <= w2n t.vs_fmp /\
   w2n t.vs_fmp <= MAX (w2n t.vs_initial_fmp) (LENGTH t.vs_memory + 31) /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[MAX_DEF] >> decide_tac) >>
  qexists_tac `t` >> simp[] >>
  mp_tac (Q.SPECL [`w2n s.vs_fmp`, `s.vs_call_ctx.cc_calldata`, `s`]
             read_memory_write_self) >> simp[read_memory_def]
QED
