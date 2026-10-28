(*
 * Statement simulation: Raise and Assert with a string literal reason (#637)
 *
 * The reason is ABI-encoded into a buffer that the REVERT returns.  The
 * encoder's code only allocates, adds, loads, stores and copies memory, so
 * it runs to the REVERT from any state where its operands are defined
 * (reason_prefix, a definedness certificate for its instructions).
 *
 * TOP-LEVEL:
 *   compile_revert_reason_frag     — the encoder and the REVERT, an exit,
 *                                    for an operand reason_vv hands out
 *   compile_bytelike_revert_frag   — the same for a string literal
 *   compile_raise_reason_lit_frag  — raise with a string literal reason
 *   compile_assert_reason_lit_frag — assert with a string literal reason
 *
 * Helper: reason_known, reason_operand, reason_step, reason_prefix,
 *   reason_vv, unwrap_value_reason_vv, compile_revert_reason_certificate
 *)

Theory stmtSimReason
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim stmtSimIf loweringHalt
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperExprNoControl
  vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* Memory execution needs defined operands, not a memory-safety invariant.
   ALLOCA (including repeat executions and zero sizes) is total by
   loweringHaltTheory.step_alloca_frame. ADD, AND, MLOAD and MSTORE use
   step_ADD, step_AND, step_MLOAD and step_MSTORE; update_var's lookup
   equations give output definedness and the frame for the read steps.
   REVERT with defined operands is step_revert_behavior. *)
Theorem step_MCOPY_defined[local]:
  !dst src sz d a n id outs s.
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand sz s = SOME n ==>
    step_inst_base (mk_inst id MCOPY [dst; src; sz] outs) s =
      OK (mcopy (w2n d) (w2n a) (w2n n) s)
Proof
  simp[step_inst_base_def]
QED

Theorem lookup_var_mcopy[local,simp]:
  !x dst src sz s.
    lookup_var x (mcopy dst src sz s) = lookup_var x s
Proof
  simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def, LET_THM]
QED

Theorem byte_chunk_head_run[local]:
  !ptr off value sa dst sm sb s w.
    emit_op ADD [ptr; Lit off] sa = (dst, sm) /\
    emit_void MSTORE [dst; Lit value] sm = ((), sb) /\
    eval_operand ptr s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        t.vs_labels = s.vs_labels /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       run_inst_seq_def, step_inst_base_def, exec_pure2_def,
       exec_write2_def, eval_operand_def, bind_outputs_def,
       lookup_var_update_var] >>
  rpt strip_tac >> simp[lookup_var_mstore, lookup_var_update_var] >>
  gvs[not_fresh_at_def]
QED

Theorem compile_store_byte_chunks_run[local]:
  !ptr bs off sa sb s w.
    compile_store_byte_chunks ptr bs off sa = ((), sb) /\
    (!x. ptr = Var x ==> not_fresh_at sa x) /\
    eval_operand ptr s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        t.vs_labels = s.vs_labels /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def,
         emitted_insts_def, same_blocks_def, run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (h::bs) offset sa = ((), sb)` >>
  gvs[Once compile_store_byte_chunks_def, comp_bind_def,
      comp_ignore_bind_def, LET_THM, AllCaseEqs()] >>
  Cases_on `emit_op ADD [data_ptr; Lit (n2w offset)] sa` >>
  rename1 `emit_op ADD _ sa = (dst, sm)` >>
  Cases_on `emit_void MSTORE [dst; Lit (word_of_bytes T 0w
    (h::TAKE 31 (bs ++ REPLICATE 31 0w)))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >> gvs[] >>
  drule_all byte_chunk_head_run >> strip_tac >>
  `(!x. data_ptr = Var x ==> not_fresh_at sh x) /\
   eval_operand data_ptr t = SOME w` by
    (conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD] >>
     Cases_on `data_ptr` >> gvs[eval_operand_def]) >>
  first_x_assum drule >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `sb.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sb` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    metis_tac[emitted_insts_append] >>
  simp[] >> conj_tac >- metis_tac[same_blocks_def] >>
  qexists `t'` >> conj_tac
  >- (qpat_assum `run_inst_seq _ s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sh sb` mp_tac) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sh x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  simp[]
QED

Theorem byte_literal_head_run[local]:
  !size len sa buf sm sb s.
    compile_alloc_buffer size sa = (buf, sm) /\
    emit_void MSTORE [buf.buf_operand; Lit len] sm = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
          eval_operand buf.buf_operand t = SOME w /\ t.vs_labels = s.vs_labels /\
          (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
      emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1,
       not_fresh_at_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (simp[run_inst_seq_def, step_inst_base_def, venomInstTheory.mk_inst_def, exec_alloca_def,
           exec_write2_def, eval_operand_def, lookup_var_update_var] >>
      rpt strip_tac >> simp[lookup_var_def, update_var_def, mstore_def,
                           FLOOKUP_UPDATE] >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME alloc` >> PairCases_on `alloc` >>
  simp[run_inst_seq_def, step_inst_base_def, venomInstTheory.mk_inst_def, exec_alloca_def,
       exec_write2_def, eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> simp[lookup_var_mstore, lookup_var_update_var] >> metis_tac[]
QED

Theorem compile_bytelike_literal_run[local]:
  !bs max_len sa buf sb s.
    compile_bytelike_literal bs max_len sa = (buf, sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
          eval_operand buf.buf_operand t = SOME w /\ t.vs_labels = s.vs_labels /\
          (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  Cases_on `compile_alloc_buffer (32 + (max_len + 31) DIV 32 * 32) sa` >>
  rename1 `compile_alloc_buffer _ sa = (b, sm)` >>
  Cases_on `emit_void MSTORE [b.buf_operand; Lit (n2w (LENGTH bs))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >>
  Cases_on `compile_store_byte_chunks b.buf_operand bs 32 sh` >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (u, sf)` >>
  Cases_on `u` >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_all byte_literal_head_run >> disch_then (qspec_then `s` strip_assume_tac) >>
  drule_all compile_store_byte_chunks_run >> strip_tac >>
  `sb.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sb` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    metis_tac[emitted_insts_append] >>
  simp[] >> conj_tac >- metis_tac[same_blocks_def] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexistsl [`t'`, `w`] >> conj_tac
  >- (qpat_assum `run_inst_seq _ s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sh sb` mp_tac) >> simp[]) >>
  conj_tac >- (Cases_on `b.buf_operand` >> gvs[eval_operand_def]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sh x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  simp[]
QED

(* A focused definedness certificate for the reason encoder's memory code.
   Outputs may already be bound: the certificate tracks availability only. *)
Definition reason_known_def:
  reason_known ds s <=> !x. MEM x ds ==> ?w. lookup_var x s = SOME w
End

Definition reason_operand_def:
  reason_operand ds (Lit w) = T /\
  reason_operand ds (Var x) = MEM x ds /\
  reason_operand ds (Label l) = F
End

Definition reason_step_def:
  reason_step ds i <=>
    (?id sz out. i = mk_inst id ALLOCA [Lit sz] [out]) \/
    (?id opc a b out. (opc = ADD \/ opc = AND) /\
      i = mk_inst id opc [a; b] [out] /\
      reason_operand ds a /\ reason_operand ds b) \/
    (?id a out. i = mk_inst id MLOAD [a] [out] /\ reason_operand ds a) \/
    (?id a b. i = mk_inst id MSTORE [a; b] [] /\
      reason_operand ds a /\ reason_operand ds b) \/
    (?id a b c. i = mk_inst id MCOPY [a; b; c] [] /\
      reason_operand ds a /\ reason_operand ds b /\ reason_operand ds c)
End

Definition reason_prefix_def:
  reason_prefix ds [] es = (es = ds) /\
  reason_prefix ds (i::is) es =
    (reason_step ds i /\ reason_prefix (i.inst_outputs ++ ds) is es)
End

Theorem reason_operand_defined[local]:
  !ds op s. reason_operand ds op /\ reason_known ds s ==>
    ?w. eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[reason_operand_def, eval_operand_def, reason_known_def]
QED

Theorem reason_known_update[local]:
  !ds s out w. reason_known ds s ==>
    reason_known (out::ds) (update_var out w s)
Proof
  simp[reason_known_def, lookup_var_update_var] >> metis_tac[]
QED

Theorem reason_step_sound[local]:
  !ds i s. reason_step ds i /\ reason_known ds s ==>
    ?t. step_inst_base i s = OK t /\
        reason_known (i.inst_outputs ++ ds) t /\ t.vs_labels = s.vs_labels
Proof
  rw[reason_step_def]
  >- (qspecl_then [`id`, `sz`, `out`, `s`] strip_assume_tac step_alloca_frame >>
      qexists `s1` >> simp[venomInstTheory.mk_inst_def, reason_known_def] >>
      rpt strip_tac >> Cases_on `x = out` >> gvs[reason_known_def]) >>
  imp_res_tac reason_operand_defined >> gvs[]
  >~ [`step_inst_base (mk_inst _ ADD _ _) _`] >-
    (irule_at Any emitHelperPropsTheory.step_ADD >>
     simp[reason_known_update, update_var_def] >> metis_tac[])
  >~ [`step_inst_base (mk_inst _ AND _ _) _`] >-
    (irule_at Any emitHelperPropsTheory.step_AND >>
     simp[reason_known_update, update_var_def] >> metis_tac[])
  >~ [`step_inst_base (mk_inst _ MLOAD _ _) _`] >-
    (irule_at Any step_MLOAD >>
     simp[reason_known_update, update_var_def] >> metis_tac[])
  >~ [`step_inst_base (mk_inst _ MSTORE _ _) _`] >-
    (irule_at Any emitHelperPropsTheory.step_MSTORE >>
     gvs[reason_known_def]) >>
  irule_at Any step_MCOPY_defined >>
  gvs[reason_known_def, mcopy_def, write_memory_with_expansion_def] >> metis_tac[]
QED

Theorem reason_prefix_sound[local]:
  !is ds es s. reason_prefix ds is es /\ reason_known ds s ==>
    ?t. run_inst_seq is s = OK t /\ reason_known es t /\ t.vs_labels = s.vs_labels
Proof
  Induct >> simp[reason_prefix_def, run_inst_seq_def] >> rpt strip_tac >>
  drule_all reason_step_sound >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem reason_step_simple[local]:
  !ds i. reason_step ds i ==> i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode
Proof
  rw[reason_step_def] >> simp[venomInstTheory.mk_inst_def, is_terminator_def]
QED

Theorem reason_prefix_simple[local]:
  !is ds es. reason_prefix ds is es ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is
Proof
  Induct >> simp[reason_prefix_def] >> metis_tac[reason_step_simple]
QED

(* The operand a reason's value_vv hands to the encoder with no code of
   unwrap_value's own: a stack operand, or the pointer of a value in memory
   of a type that is not a word type (a string). *)
Definition reason_vv_def:
  reason_vv (StackValue t op) = SOME op /\
  reason_vv (LocatedValue t p) =
    if ~is_word_type t /\ p.ptr_location = LocMemory then SOME p.ptr_operand
    else NONE
End

Theorem unwrap_value_reason_vv:
  !cenv vv op st. reason_vv vv = SOME op ==> unwrap_value cenv vv st = (op, st)
Proof
  Cases_on `vv` >> rw[reason_vv_def, unwrap_value_def, comp_return_def]
QED

Theorem compile_revert_reason_certificate:
  !cenv msg_vv op msg_type msg_size sa sb ds.
    reason_vv msg_vv = SOME op /\ reason_operand ds op /\
    compile_revert_with_reason cenv msg_vv msg_type msg_size sa = ((), sb) ==>
    ?prefix es id off len.
      emitted_insts sa sb = prefix ++ [mk_inst id REVERT [off; len] []] /\
      reason_prefix ds prefix es /\ reason_operand es off /\
      reason_operand es len /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      same_blocks sa sb
Proof
  rpt gen_tac >> strip_tac >>
  drule unwrap_value_reason_vv >> strip_tac >>
  gvs[compile_revert_with_reason_def,
      contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  qmatch_goalsub_abbrev_tac `sa.cs_current_insts ++ code` >>
  simp[emitted_insts_def, DROP_APPEND1, same_blocks_def] >>
  qexists `TAKE 31 code` >>
  simp[Abbr `code`, TAKE_def] >>
  simp[reason_prefix_def, venomInstTheory.mk_inst_def] >>
  rpt conj_tac >>
  simp[reason_step_def, venomInstTheory.mk_inst_def, reason_operand_def] >>
  Cases_on `op` >> gvs[reason_operand_def]
QED

Theorem compile_revert_reason_buf_certificate[local]:
  !cenv msg_ty buf msg_type msg_size sa sb ds.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) ==>
    ?prefix es id off len.
      emitted_insts sa sb = prefix ++ [mk_inst id REVERT [off; len] []] /\
      reason_prefix ds prefix es /\ reason_operand es off /\
      reason_operand es len /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      same_blocks sa sb
Proof
  rpt strip_tac >> irule compile_revert_reason_certificate >>
  qexistsl [`cenv`, `msg_size`, `msg_type`,
            `LocatedValue msg_ty (base_ptr buf)`, `buf.buf_operand`] >>
  simp[reason_vv_def, contextTheory.base_ptr_def]
QED

Theorem reason_prefix_revert_run[local]:
  !is ds es s id off len.
    reason_prefix ds is es /\ reason_known ds s /\
    reason_operand es off /\ reason_operand es len ==>
    ?t. run_inst_seq (is ++ [mk_inst id REVERT [off; len] []]) s =
          Abort Revert_abort t /\ t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >> drule_all reason_prefix_sound >> strip_tac >>
  `?ow. eval_operand off t = SOME ow` by metis_tac[reason_operand_defined] >>
  `?lw. eval_operand len t = SOME lw` by metis_tac[reason_operand_defined] >>
  qpat_assum `run_inst_seq is s = OK t`
    (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `[mk_inst id REVERT [off; len] []]` mp_tac) >>
  simp[run_inst_seq_def] >>
  `step_inst_base (mk_inst id REVERT [off; len] []) t =
    Abort Revert_abort (revert_state (set_returndata
      (TAKE (w2n lw) (DROP (w2n ow) t.vs_memory ++ REPLICATE (w2n lw) 0w)) t))`
    by (simp[venomInstTheory.mk_inst_def] >> irule step_revert_behavior >> simp[]) >>
  simp[revert_state_def, set_returndata_def]
QED

Theorem compile_revert_reason_run[local]:
  !cenv msg_ty buf msg_type msg_size sa sb s ds.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    reason_known ds s /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
        t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  drule_all compile_revert_reason_buf_certificate >> strip_tac >> simp[] >>
  irule reason_prefix_revert_run >> metis_tac[]
QED

Theorem reason_prefix_revert_frag[local]:
  !ctx sa sb ds es is id off len R.
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      (is ++ [mk_inst id REVERT [off; len] []]) /\
    reason_prefix ds is es /\ reason_operand es off /\ reason_operand es len /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (reason_known ds) (\s. F) R
Proof
  rpt strip_tac >>
  qabbrev_tac `sm = sa with cs_current_insts := sa.cs_current_insts ++ is` >>
  irule frag_exec_seq >> qexists `reason_known es` >> qexists `sm` >>
  conj_tac >- (simp[cs_extends_def, Abbr `sm`] >> qexists `[]` >> simp[]) >>
  conj_tac >- (simp[cs_extends_def, Abbr `sm`] >> qexists `[]` >>
              fs[same_blocks_def]) >>
  conj_tac
  >- (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is`
        by metis_tac[reason_prefix_simple] >>
      irule frag_exec_run_inst_seq >>
      simp[Abbr `sm`, emitted_insts_def, DROP_APPEND1] >>
      rpt strip_tac >> disj1_tac >>
      drule_all reason_prefix_sound >> strip_tac >> qexists `t` >>
      fs[reason_known_def, lookup_var_def])
  >- (irule frag_exec_step_abort >>
      fs[Abbr `sm`, same_blocks_def] >>
      rpt strip_tac >>
      `?ow. eval_operand off s = SOME ow` by metis_tac[reason_operand_defined] >>
      `?lw. eval_operand len s = SOME lw` by metis_tac[reason_operand_defined] >>
      qexists `0` >> simp[step_inst_non_invoke, venomInstTheory.mk_inst_def] >>
      irule_at Any step_revert_behavior >> simp[])
QED
Theorem compile_revert_reason_buf_frag[local]:
  !ctx cenv msg_ty buf msg_type msg_size sa sb ds R.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (reason_known ds) (\s. F) R
Proof
  rpt strip_tac >> drule_all compile_revert_reason_buf_certificate >> strip_tac >>
  irule reason_prefix_revert_frag >> simp[] >> metis_tac[]
QED

(* The encoder and its REVERT, for a message operand that reason_vv hands
   out, from any state where the variables of ds are defined. *)
Theorem compile_revert_reason_frag:
  !ctx cenv msg_vv op msg_type msg_size sa sb ds R.
    reason_vv msg_vv = SOME op /\ reason_operand ds op /\
    compile_revert_with_reason cenv msg_vv msg_type msg_size sa = ((), sb) /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (reason_known ds) (\s. F) R /\ cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_revert_reason_certificate >> strip_tac >>
  conj_tac
  >- (irule reason_prefix_revert_frag >> simp[] >> metis_tac[]) >>
  simp[cs_extends_def] >> qexists `[]` >> gvs[same_blocks_def] >>
  metis_tac[IS_PREFIX_APPEND3, APPEND_ASSOC]
QED

Theorem compile_store_byte_chunks_simple[local]:
  !ptr bs off sa sb.
    compile_store_byte_chunks ptr bs off sa = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def, emitted_insts_def,
         same_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (h::bs) offset sa = ((), sb)` >>
  gvs[Once compile_store_byte_chunks_def, comp_bind_def,
      comp_ignore_bind_def, LET_THM, AllCaseEqs()] >>
  Cases_on `emit_op ADD [data_ptr; Lit (n2w offset)] sa` >>
  rename1 `emit_op ADD _ sa = (dst, sm)` >>
  Cases_on `emit_void MSTORE [dst; Lit (word_of_bytes T 0w
    (h::TAKE 31 (bs ++ REPLICATE 31 0w)))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
   same_blocks sa sh /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sh)` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
     simp[emitted_insts_def, DROP_APPEND1, same_blocks_def,
          venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb`
    by metis_tac[emitted_insts_append] >>
  simp[] >> metis_tac[same_blocks_def, APPEND_ASSOC]
QED

Theorem compile_bytelike_literal_simple[local]:
  !bs ml sa buf sb.
    compile_bytelike_literal bs ml sa = (buf, sb) ==>
    (?x. buf.buf_operand = Var x) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  Cases_on `compile_alloc_buffer (32 + (ml + 31) DIV 32 * 32) sa` >>
  rename1 `compile_alloc_buffer _ sa = (b, sm)` >>
  Cases_on `emit_void MSTORE [b.buf_operand; Lit (n2w (LENGTH bs))] sm` >>
  rename1 `emit_void MSTORE _ sm = (u, sh)` >> Cases_on `u` >>
  Cases_on `compile_store_byte_chunks b.buf_operand bs 32 sh` >>
  rename1 `compile_store_byte_chunks _ _ _ sh = (u, sf)` >>
  Cases_on `u` >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule compile_store_byte_chunks_simple >> strip_tac >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
   (?x. b.buf_operand = Var x) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sh)` by
    (gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def] >>
     simp[emitted_insts_def, DROP_APPEND1, venomInstTheory.mk_inst_def,
          is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb`
    by metis_tac[emitted_insts_append] >> simp[]
QED

Theorem compile_bytelike_revert_frag:
  !ctx cenv bs ml msg_ty msg_type msg_size sa sm buf sb R.
    compile_bytelike_literal bs ml sa = (buf, sm) /\
    ~is_word_type msg_ty /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sm = ((), sb) /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. T) (\s. F) R
Proof
  rpt strip_tac >> drule compile_bytelike_literal_simple >> strip_tac >>
  `reason_operand [x] buf.buf_operand` by simp[reason_operand_def] >>
  drule_all compile_revert_reason_buf_certificate >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   same_blocks sa sm` by
    (drule compile_bytelike_literal_run >>
     disch_then (qspec_then `ARB` strip_assume_tac) >> simp[]) >>
  irule frag_exec_seq >> qexists `reason_known [x]` >> qexists `sm` >>
  conj_tac >- (simp[cs_extends_def] >> qexists `[]` >> fs[same_blocks_def]) >>
  conj_tac >- (simp[cs_extends_def] >> qexists `[]` >> fs[same_blocks_def] >>
              metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  conj_tac
  >- (irule frag_exec_run_inst_seq >> fs[same_blocks_def] >>
      rpt strip_tac >> disj1_tac >>
      drule compile_bytelike_literal_run >>
      disch_then (qspec_then `s` strip_assume_tac) >> qexists `t` >>
      gvs[reason_known_def, eval_operand_def, lookup_var_def]) >>
  irule compile_revert_reason_buf_frag >> metis_tac[]
QED

(* raise and assert with a string literal as the reason: the literal's
   buffer and the Error(string) encoding of compile_revert_with_reason,
   straight-line code that ends in a REVERT, which every assertion
   allows.  A reason other than a literal is compiled with compile_expr
   and read back with unwrap_value after code of its own; those forms are
   not covered yet. *)
(* Why they hold.  The literal evaluates to StringV str, so the source
   raises AssertException str, which expr_exit takes as Revert_abort.  The
   reason code is one run of instructions in the open block, none a
   terminator before the REVERT: ALLOCAs with a literal size and one
   output, MSTOREs, ADD/AND, MLOAD, MCOPY, all total, each Var operand the
   output of an earlier one; unwrap_value of the literal's memory pointer
   emits nothing.  So it reaches the REVERT from any state.  The assert form
   is compile_assert_frag's shape with this run in place of the one
   aborting instruction of the fail block. *)
Theorem compile_raise_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty ml str es res es'.
    eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       compile_reason_message_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, vyperASTTheory.expr_type_def] >>
  Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) ml sa` >>
  rename1 `compile_bytelike_literal _ _ sa = (buf, sm)` >>
  Cases_on `compile_revert_with_reason cenv
    (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf))
    (BaseT (StringT ml)) (type_memory_bytes cenv (BaseT (StringT ml))) sm` >>
  rename1 `compile_revert_with_reason _ _ _ _ sm = (u, sf)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  `frag_exec ctx sa sb (\s. T) (\s. F) (stmt_exit RetQ es' res)` by
    (irule (INST_TYPE [alpha |-> ``:type``] compile_bytelike_revert_frag) >> conj_tac
     >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
         simp[Once evaluate_def, raise_def] >>
         simp[Once evaluate_def, evaluate_literal_def, bind_def, return_def,
              read_result_def, lift_option_type_def, dest_StringV_def,
              raise_def] >> strip_tac >> gvs[stmt_exit_def, expr_exit_def]) >>
     goal_assum (drule_at Any) >>
     qexistsl [`MAP (n2w o ORD) str`, `ml`] >>
     simp[is_word_type_def]) >>
  fs[frag_exec_def]
QED

Theorem bytelike_revert_extends[local]:
  !cenv bs ml msg_ty msg_type msg_size sa sm buf sb.
    compile_bytelike_literal bs ml sa = (buf, sm) /\
    ~is_word_type msg_ty /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sm = ((), sb) ==>
    cs_extends sa sb
Proof
  rpt strip_tac >>
  drule compile_bytelike_literal_simple >> strip_tac >>
  `reason_operand [x] buf.buf_operand` by simp[reason_operand_def] >>
  drule_all compile_revert_reason_buf_certificate >> strip_tac >>
  drule compile_bytelike_literal_run >>
  disch_then (qspec_then `ARB` strip_assume_tac) >>
  simp[cs_extends_def] >> qexists `[]` >>
  gvs[same_blocks_def] >> metis_tac[APPEND_ASSOC, IS_PREFIX_APPEND]
QED

Theorem compile_assert_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty e ml str es res es'.
    eval_stmt cx
      (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es res es'
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       compile_reason_message_def, vyperASTTheory.expr_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op, s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok, s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl, s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u4, s4)` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (x5, s5)` >> simp[] >>
  Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) ml s5` >>
  rename1 `compile_bytelike_literal _ _ s5 = (buf, sm)` >> simp[] >>
  Cases_on `compile_revert_with_reason cenv
    (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf))
    (BaseT (StringT ml)) (type_memory_bytes cenv (BaseT (StringT ml))) sm` >>
  rename1 `compile_revert_with_reason _ _ _ _ sm = (u, s6)` >>
  Cases_on `u` >> simp[] >>
  Cases_on `new_block ok s6` >> rename1 `new_block ok s6 = (x7, s7)` >>
  simp[] >> strip_tac >> gvs[] >> suspend "control"
QED

Resume compile_assert_reason_lit_frag[control]:
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  imp_res_tac emit_inst_extends >>
  `cs_extends s5 s6` by
    (irule (INST_TYPE [alpha |-> ``:type``] bytelike_revert_extends) >>
     goal_assum (drule_at Any) >>
     qexistsl [`MAP (n2w o ORD) str`, `ml`] >> simp[is_word_type_def]) >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s6 s7` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block,
              cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s4 s5 func /\
   fn_has_code s5 s6 func` by
    metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
              cs_extends_refl] >>
  `lookup_block s4.cs_current_bb func.fn_blocks =
     SOME <| bb_label := s4.cs_current_bb;
             bb_instructions := s4.cs_current_insts |>` by
    metis_tac[fn_has_code_new_block] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def, eval_expr_switch_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (r1,es1)` >> simp[] >>
  strip_tac >> suspend "condition"
QED

Resume compile_assert_reason_lit_frag[condition]:
  qpat_x_assum `_ = (res, es')` mp_tac >>
  simp[Once evaluate_def, evaluate_literal_def, bind_def, return_def,
       read_result_def, lift_option_type_def, dest_StringV_def, raise_def] >>
  strip_tac >>
  `expr_res_ok r1 /\ !v. r1 = INL v ==> ?b. v = BoolV b` by
    (Cases_on `r1` >> gvs[]
     >- (rename1 `INL plain` >>
         Cases_on `?b. plain = BoolV b` >> gvs[expr_res_ok_def] >>
         `plain <> BoolV T /\ plain <> BoolV F` by metis_tac[] >>
         gvs[raise_def, stmt_res_ok_def]) >>
     qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e es` >>
     rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     imp_res_tac read_result_no_control >>
     imp_res_tac (cj 1 eval_expr_no_control) >>
     gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  `s3.cs_current_bb = s1.cs_current_bb /\
   s3.cs_current_insts = s1.cs_current_insts` by metis_tac[] >>
  drule_all cond_jump_frag >> strip_tac
  >- (Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def]
      >- (disj1_tac >> rename1 `stmt_state_rel func cenv cx es' sv` >>
          qexists_tac `jump_to s7.cs_current_bb sv` >>
          gvs[stmt_lands_def, stmt_state_rel_jump_to, cenv_top_ext_refl,
              block_is_terminated_def] >>
          simp[jump_to_def, lookup_var_def] >> fs[lookup_var_def, jump_to_def]) >>
      suspend "abort") >>
  disj2_tac >> qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >>
  disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_reason_lit_frag[abort]:
  gvs[bind_def, return_def, read_result_def, dest_StringV_def, raise_def] >>
  disj2_tac >>
  `frag_exec ctx s5 s6 (\s. T) (\s. F)
     (stmt_exit RetQ es' (INR (AssertException str)))` by
    (irule (INST_TYPE [alpha |-> ``:type``] compile_bytelike_revert_frag) >>
     conj_tac >- simp[stmt_exit_def, expr_exit_def] >>
     goal_assum (drule_at Any) >>
     qexistsl [`MAP (n2w o ORD) str`, `ml`] >> simp[is_word_type_def]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >>
  disch_then (qspec_then `jump_to s5.cs_current_bb s` mp_tac) >>
  impl_tac >- simp[jump_to_def] >> strip_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func (jump_to _ s) <> Error e) ==> _`
    (qspec_then `fuel` mp_tac) >>
  impl_tac >- metis_tac[exit_result_not_error] >>
  disch_then (qx_choose_then `f0` strip_assume_tac) >>
  qexists_tac `f0` >> gvs[]
QED

Finalise compile_assert_reason_lit_frag

(* Integrity gate for preserved public reason certificates and execution. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "REASON_FORCE_AUDIT OK\n"
     else raise Fail "reason consumer inherited admission"
  end) [compile_store_byte_chunks_run, compile_bytelike_literal_run,
        compile_revert_reason_certificate, compile_revert_reason_run,
        compile_revert_reason_frag, compile_store_byte_chunks_simple,
        compile_bytelike_literal_simple, compile_bytelike_revert_frag,
        compile_raise_reason_lit_frag, compile_assert_reason_lit_frag];
