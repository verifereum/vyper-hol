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
 *   compile_revert_reason_path, compile_bytelike_revert_path
 *                                  — the same as counted paths: none of
 *                                    the encoder's code reads gas
 *   compile_raise_reason_lit_frag  — raise with a string literal reason
 *   compile_assert_reason_frag_general
 *                                  — assert with any reason, whose fail
 *                                    block is the raise's code
 *   compile_assert_reason_lit_frag — assert with a string literal reason
 *
 * Helper: reason_known, reason_operand, reason_step, reason_prefix,
 *   reason_vv, unwrap_value_reason_vv, compile_revert_reason_certificate,
 *   compile_revert_reason_split_certificate (the encoder's code split at
 *   its unwrap_value, for reasons that unwrap_value copies),
 *   reason_prefix_sound, reason_head_frag, reason_prefix_revert_frag,
 *   reason_operand_mono, reason_prefix_append, reason_prefix_append_known,
 *   reason_revert_path
 *)

Theory stmtSimReason
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs exprSimUnwrap
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice  stmtSimIfProps stmtSimAssertProps
  loweringHalt gasOutcome gasSummary gasSummaryCompose gasContext gasExemptCert
  gasCount fragGasPath fragGasMode fragGasSeq fragGasSeqAbort venomInstProofs
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
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def,
       exec_pure2_def, exec_write2_def, eval_operand_def, bind_outputs_def,
       lookup_var_update_var] >>
  simp[run_inst_seq_def] >>
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
  >- (simp[run_inst_seq_def, step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def, exec_alloca_def,
           exec_write2_def, eval_operand_def, lookup_var_update_var] >>
      rpt strip_tac >> simp[lookup_var_def, update_var_def, mstore_def,
                           FLOOKUP_UPDATE] >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME alloc` >> PairCases_on `alloc` >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def, exec_alloca_def,
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

Theorem reason_step_known_frame[local]:
  !ds i s t. reason_step ds i /\ reason_known ds s /\
    step_inst_base i s = OK t ==>
    !x. ~MEM x i.inst_outputs ==> lookup_var x t = lookup_var x s
Proof
  rw[reason_step_def]
  >- (qspecl_then [`id`, `sz`, `out`, `s`] strip_assume_tac step_alloca_frame >>
      gvs[venomInstTheory.mk_inst_def]) >>
  imp_res_tac reason_operand_defined >> gvs[]
  >~ [`step_inst_base (mk_inst _ ADD _ _) _`] >-
    (`?v. step_inst_base (mk_inst id ADD [a;b] [out]) s =
             OK (update_var out v s)` by
       (irule_at Any emitHelperPropsTheory.step_ADD >> simp[] >> metis_tac[]) >>
     gvs[venomInstTheory.mk_inst_def, lookup_var_update_var])
  >~ [`step_inst_base (mk_inst _ AND _ _) _`] >-
    (`?v. step_inst_base (mk_inst id AND [a;b] [out]) s =
             OK (update_var out v s)` by
       (irule_at Any emitHelperPropsTheory.step_AND >> simp[] >> metis_tac[]) >>
     gvs[venomInstTheory.mk_inst_def, lookup_var_update_var])
  >~ [`step_inst_base (mk_inst _ MLOAD _ _) _`] >-
    (drule_all step_MLOAD >>
     disch_then (qspecl_then [`id`, `out`] assume_tac) >>
     gvs[venomInstTheory.mk_inst_def, lookup_var_update_var])
  >~ [`step_inst_base (mk_inst _ MSTORE _ _) _`] >-
    (`?d v. step_inst_base (mk_inst id MSTORE [a;b] []) s =
               OK (mstore d v s)` by
       (irule_at Any emitHelperPropsTheory.step_MSTORE >> metis_tac[]) >>
     gvs[lookup_var_mstore]) >>
  `?d src n. step_inst_base (mk_inst id MCOPY [a;b;c] []) s =
               OK (mcopy d src n s)` by
    (irule_at Any step_MCOPY_defined >> metis_tac[]) >> gvs[]
QED

Theorem reason_prefix_sound:
  !is ds es s. reason_prefix ds is es /\ reason_known ds s ==>
    ?t. run_inst_seq is s = OK t /\ reason_known es t /\
        t.vs_labels = s.vs_labels /\
        (!x. ~MEM x (FLAT (MAP (\i. i.inst_outputs) is)) ==>
             lookup_var x t = lookup_var x s)
Proof
  Induct >> simp[reason_prefix_def, run_inst_seq_def] >> rpt strip_tac >>
  drule_all reason_step_sound >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >> simp[] >>
  metis_tac[reason_step_known_frame]
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

Theorem reason_head_frag:
  !ctx sa sm h hs sbase R.
    same_blocks sa sm /\
    sm.cs_current_insts = sa.cs_current_insts ++ h /\
    reason_prefix [] h hs /\
    EVERY (\i. EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) h ==>
    frag_exec ctx sa sm (\s. s = sbase)
      (\s. reason_known hs s /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  rpt strip_tac >> gvs[same_blocks_def] >>
  irule frag_exec_run_inst_seq >>
  simp[emitted_insts_def, DROP_APPEND1] >>
  reverse conj_tac >- metis_tac[reason_prefix_simple] >>
  rpt strip_tac >> disj1_tac >>
  `reason_known [] sbase` by simp[reason_known_def] >>
  drule_all reason_prefix_sound >> strip_tac >> qexists `t` >>
  conj_tac >- simp[] >>
  conj_tac >- gvs[reason_known_def, lookup_var_def] >>
  simp[lookup_var_def] >> rpt strip_tac >>
  `~MEM x (FLAT (MAP (\i. i.inst_outputs) h))` by
    (gvs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  metis_tac[lookup_var_def]
QED

Theorem reason_operand_mono:
  !ds es op. (!x. MEM x ds ==> MEM x es) /\ reason_operand ds op ==>
    reason_operand es op
Proof
  Cases_on `op` >> simp[reason_operand_def]
QED

Theorem reason_step_mono[local]:
  !ds es i. (!x. MEM x ds ==> MEM x es) /\ reason_step ds i ==>
    reason_step es i
Proof
  rpt strip_tac >> gvs[reason_step_def] >>
  metis_tac[reason_operand_mono]
QED

Theorem reason_prefix_append_known:
  !is ds es extra. reason_prefix ds is es ==>
    reason_prefix (ds ++ extra) is (es ++ extra)
Proof
  Induct >> simp[reason_prefix_def] >> rpt strip_tac >>
  irule reason_step_mono >> qexists_tac `ds` >> simp[]
QED

Theorem reason_prefix_append:
  !is js ds es fs.
    reason_prefix ds is es /\ reason_prefix es js fs ==>
    reason_prefix ds (is ++ js) fs
Proof
  Induct >> simp[reason_prefix_def] >> metis_tac[]
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

Theorem compile_revert_reason_split_certificate:
  !cenv vv mt ms sa sb.
    compile_revert_with_reason cenv vv mt ms sa = ((),sb) ==>
    ?sm sn op h hs k id off len.
      unwrap_value cenv vv sm = (op,sn) /\
      same_blocks sa sm /\ sm.cs_current_insts = sa.cs_current_insts ++ h /\
      reason_prefix [] h hs /\ EVERY (not_fresh_at sm) hs /\
      EVERY (\i. EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) h /\
      sa.cs_next_var <= sm.cs_next_var /\
      cs_extends sa sm /\ cs_extends sn sb /\
      same_blocks sn sb /\
      sb.cs_current_insts = sn.cs_current_insts ++
        (k ++ [mk_inst id REVERT [off;len] []]) /\
      (!ds. (!x. MEM x hs ==> MEM x ds) /\ reason_operand ds op ==>
        ?es. reason_prefix ds k es /\ reason_operand es off /\ reason_operand es len)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_revert_with_reason _ _ _ _ _ = _` mp_tac >>
  simp[compile_revert_with_reason_def, contextTheory.compile_alloc_buffer_def,
       emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  qmatch_goalsub_abbrev_tac `unwrap_value cenv vv sm` >>
  pairarg_tac >> rename1 `unwrap_value cenv vv sm = (op,sn)` >>
  simp[] >> rewrite_tac[GSYM APPEND_ASSOC] >>
  qmatch_goalsub_abbrev_tac `sn.cs_current_insts ++ tail` >> strip_tac >>
  qexistsl_tac [`sm`, `sn`, `op`, `emitted_insts sa sm`,
    `[STRING #"%" (toString (sa.cs_next_var + 2));
      STRING #"%" (toString (sa.cs_next_var + 1));
      STRING #"%" (toString sa.cs_next_var)]`, `TAKE 27 tail`,
    `sn.cs_next_id + 27`, `Var (STRING #"%" (toString (sn.cs_next_var + 19)))`,
    `Var (STRING #"%" (toString (sn.cs_next_var + 20)))`] >>
  asm_rewrite_tac[] >>
  simp[same_blocks_def, Abbr `sm`, emitted_insts_def, DROP_APPEND1,
       reason_prefix_def, venomInstTheory.mk_inst_def, not_fresh_at_def] >>
  gvs[] >> simp[reason_step_def, venomInstTheory.mk_inst_def, reason_operand_def] >>
  conj_tac
  >- (simp[cs_extends_def] >> rewrite_tac[GSYM APPEND_ASSOC] >> simp[]) >>
  conj_tac >- simp[cs_extends_def] >>
  conj_tac >- simp[Abbr `tail`, TAKE_def, venomInstTheory.mk_inst_def] >>
  rpt strip_tac >>
  simp[Abbr `tail`, TAKE_def, reason_prefix_def, venomInstTheory.mk_inst_def] >>
  rpt conj_tac >>
  simp[reason_step_def, venomInstTheory.mk_inst_def, reason_operand_def] >>
  Cases_on `op` >> gvs[reason_operand_def]
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
  drule compile_revert_reason_split_certificate >> strip_tac >>
  rename1 `unwrap_value cenv msg_vv sm = (mop,sn)` >>
  `mop = op /\ sn = sm` by metis_tac[unwrap_value_reason_vv, pairTheory.PAIR_EQ] >>
  gvs[] >> rename1 `reason_vv msg_vv = SOME op` >>
  rename1 `reason_prefix [] h hs` >>
  `reason_prefix ds h (hs ++ ds)` by
    metis_tac[reason_prefix_append_known, APPEND] >>
  `reason_operand (hs ++ ds) op` by
    (irule reason_operand_mono >> qexists_tac `ds` >> simp[]) >>
  first_x_assum (qspec_then `hs ++ ds` mp_tac) >> simp[] >> strip_tac >>
  rename1 `reason_prefix (hs ++ ds) k es` >>
  qexistsl_tac [`h ++ k`, `es`, `id`, `off`, `len`] >>
  conj_tac >- simp[emitted_insts_def, DROP_APPEND1, APPEND_ASSOC] >>
  conj_tac >- metis_tac[reason_prefix_append] >>
  simp[emitted_insts_def, DROP_APPEND1, APPEND_ASSOC] >>
  gvs[same_blocks_def]
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

Theorem reason_prefix_revert_frag:
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
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode)
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
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode)
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
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode)
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
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode)
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
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sm)` by fs[EVERY_MEM] >>
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

(* ===== Counted paths: the encoder reads no gas ===== *)

(* The encoder's instructions and the literal's are ALLOCA, ADD, AND,
   MLOAD, MSTORE and MCOPY: none reads gas, so their path counts zero. *)
Theorem reason_prefix_counted:
  !is ds es. reason_prefix ds is es ==>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) is
Proof
  Induct >> simp[reason_prefix_def] >> rpt gen_tac >> strip_tac >>
  reverse conj_tac >- metis_tac[] >>
  gvs[reason_step_def] >> simp[venomInstTheory.mk_inst_def, is_terminator_def]
QED

Theorem prefix_drop_length[local]:
  !a b (l:'a list). isPREFIX (a ++ b) l ==> isPREFIX b (DROP (LENGTH a) l)
Proof
  simp[IS_PREFIX_APPEND] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]
QED

Theorem prefix_drop_append[local]:
  !a b k (l:'a list). isPREFIX (a ++ b) (DROP k l) ==>
    isPREFIX a (DROP k l) /\ isPREFIX b (DROP (k + LENGTH a) l)
Proof
  rpt strip_tac
  >- (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  `DROP (k + LENGTH a) l = DROP (LENGTH a) (DROP k l)` by
    (rewrite_tac[DROP_DROP_T] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  pop_assum SUBST1_TAC >> irule prefix_drop_length >> simp[]
QED

(* Straight-line code pre that reaches a state where the encoder's inputs
   ds are defined, then the encoder's own prefix and its REVERT, at the
   cursor of s: a path with no GAS read to the REVERT's abort. *)
Theorem reason_revert_path:
  !ctx func pre ds es is id off len s t bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (pre ++ is ++ [mk_inst id REVERT [off; len] []])
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) pre /\
    run_inst_seq pre s = OK t /\ reason_known ds t /\
    reason_prefix ds is es /\
    reason_operand es off /\ reason_operand es len ==>
    ?u. gas_path ctx func s 0 (Abort Revert_abort u)
Proof
  rpt strip_tac >>
  drule_all reason_prefix_sound >> strip_tac >>
  rename1 `run_inst_seq is t = OK t2` >>
  drule reason_prefix_counted >> strip_tac >>
  qabbrev_tac `code = pre ++ is` >>
  `run_inst_seq code s = OK t2` by
    (simp[Abbr `code`] >>
     qpat_x_assum `run_inst_seq pre s = OK t` mp_tac >>
     disch_then (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
     simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    fs[EVERY_MEM, FILTER_EQ_NIL] >>
  drule prefix_drop_append >> strip_tac >>
  qspecl_then [`code`, `s`, `t2`, `ctx`, `func`, `bb`] mp_tac
    tuple_run_inst_seq_gas_path >>
  impl_tac >- simp[] >> asm_rewrite_tac[LENGTH] >> strip_tac >>
  qabbrev_tac `v = t2 with vs_inst_idx := s.vs_inst_idx + LENGTH code` >>
  `~v.vs_halted` by metis_tac[gas_path_normal] >>
  `v.vs_current_bb = s.vs_current_bb` by
    (simp[Abbr `v`] >>
     irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb`
                        run_inst_seq_preserves_field)) >>
     qexists_tac `code` >> simp[] >> rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  `get_instruction bb v.vs_inst_idx = SOME (mk_inst id REVERT [off; len] [])` by
    (drule instruction_prefix_cursor >> simp[Abbr `v`]) >>
  `reason_known es v` by fs[Abbr `v`, reason_known_def, lookup_var_def] >>
  `?ow. eval_operand off v = SOME ow` by metis_tac[reason_operand_defined] >>
  `?lw. eval_operand len v = SOME lw` by metis_tac[reason_operand_defined] >>
  `?w. step_inst_base (mk_inst id REVERT [off; len] []) v = Abort Revert_abort w` by
    (simp[venomInstTheory.mk_inst_def] >>
     irule_at Any step_revert_behavior >> simp[]) >>
  `gas_path_edge ctx func v 0 (Abort Revert_abort w)` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, venomInstTheory.mk_inst_def,
          gas_count_step_def, exit_result_def] >> metis_tac[]) >>
  `gas_path ctx func v 0 (Abort Revert_abort w)` by
    metis_tac[gas_path_rules, exit_result_def] >>
  qexists_tac `w` >> drule_all gas_path_then >> simp[]
QED

Theorem compile_revert_reason_path:
  !ctx func cenv msg_vv op msg_type msg_size sa sb ds s.
    reason_vv msg_vv = SOME op /\ reason_operand ds op /\
    compile_revert_with_reason cenv msg_vv msg_type msg_size sa = ((), sb) /\
    fn_has_code sa sb func /\ reason_known ds s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path ctx func s 0 (Abort Revert_abort t)
Proof
  rpt strip_tac >>
  drule_all compile_revert_reason_certificate >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (prefix ++ [mk_inst id REVERT [off; len] []])
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def] >>
     irule prefix_drop_length >> fs[]) >>
  qspecl_then [`ctx`, `func`, `[]`, `ds`, `es`, `prefix`, `id`, `off`, `len`,
               `s`, `s`, `bb`] mp_tac reason_revert_path >>
  gvs[run_inst_seq_def]
QED

Theorem compile_bytelike_revert_path:
  !ctx func cenv bs ml msg_ty msg_type msg_size sa sm buf sb s.
    compile_bytelike_literal bs ml sa = (buf, sm) /\
    ~is_word_type msg_ty /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sm = ((), sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path ctx func s 0 (Abort Revert_abort t)
Proof
  rpt strip_tac >> drule compile_bytelike_literal_simple >> strip_tac >>
  `reason_operand [x] buf.buf_operand` by simp[reason_operand_def] >>
  drule_all compile_revert_reason_buf_certificate >> strip_tac >>
  drule compile_bytelike_literal_run >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `reason_known [x] t` by gvs[reason_known_def, eval_operand_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sm ++ prefix ++ [mk_inst id REVERT [off; len] []])
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def] >>
     irule prefix_drop_length >> fs[]) >>
  qspecl_then [`ctx`, `func`, `emitted_insts sa sm`, `[x]`, `es`, `prefix`,
               `id`, `off`, `len`, `s`, `t`, `bb`] mp_tac reason_revert_path >>
  gvs[]
QED

(* raise with a string literal reason raises the literal, whatever the
   readings. *)
Theorem eval_raise_reason_lit[local]:
  !cx ml str st.
    eval_stmt cx
      (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) st =
    (INR (AssertException str), st)
Proof
  rpt gen_tac >> simp[Once evaluate_def, raise_def] >>
  simp[Once evaluate_def, evaluate_literal_def, bind_def, return_def,
       read_result_def, lift_option_type_def, dest_StringV_def, raise_def]
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
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
      (eval_stmt cx
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))) es
Proof
  rpt gen_tac >> simp[stmt_frag_def, stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
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
  `?t. gas_path ctx func s0 0 (Abort Revert_abort t)` by
    (irule (INST_TYPE [alpha |-> ``:type``] compile_bytelike_revert_path) >>
     simp[] >>
     qexistsl_tac [`MAP (n2w o ORD) str`, `buf`, `cenv`, `ml`,
                   `type_memory_bytes cenv (BaseT (StringT ml))`,
                   `BaseT (StringT (STRLEN str))`, `BaseT (StringT ml)`,
                   `sa`, `sb`, `sm`] >>
     simp[is_word_type_def]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def,
       eval_raise_reason_lit, gas_explicit_def] >>
  qexistsl_tac [`INR (AssertException str)`, `es`, `Abort Revert_abort t`] >>
  simp[exit_result_def, stmt_exit_def, expr_exit_def]
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

Theorem eval_assert_reason_bind[local]:
  eval_stmt cx (Assert e (AssertReason r)) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. if v = BoolV T then return ()
           else if v = BoolV F then eval_stmt cx (Raise (RaiseReason r))
           else raise (Error (TypeError "not BoolV")))
Proof
  simp[FUN_EQ_THM, Once evaluate_def, eval_expr_switch_forced] >>
  gen_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx v st` >>
  Cases_on `read_result cx v st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[Once evaluate_def, bind_def]
QED

Theorem assert_reason_expr_admissible[local]:
  gas_admissible (eval_stmt cx (Assert e (AssertReason r)))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> pure_rewrite_tac[gas_admissible_def] >>
  rpt gen_tac >> disch_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `_ = (INR ex,ee)` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >>
     metis_tac[read_result_no_control, cj 1 eval_expr_no_control]) >>
  `eval_stmt cx (Assert e (AssertReason r)) (es with gas_obs := gs) =
    (INR ex,ee)` by simp[eval_assert_reason_bind, bind_def] >>
  drule_all gas_admissible_result >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem assert_reason_raise_admissible[local]:
  gas_admissible (eval_stmt cx (Assert e (AssertReason r)))
    (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV F),mid with gas_obs := tail)) ==>
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) (mid with gas_obs := [])
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `xs ++ gs` mp_tac) >>
  simp[eval_assert_reason_bind, bind_def] >> metis_tac[]
QED

Theorem eval_raise_reason_non_normal[local]:
  eval_stmt cx (Raise (RaiseReason r)) es = (res,ee) ==>
  res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException
Proof
  simp[Once evaluate_def, bind_def, lift_option_type_def,
       lift_option_def, raise_def, return_def] >>
  Cases_on `eval_expr cx r es` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw`
  >- (simp[] >> rename1 `read_result cx v st` >>
      Cases_on `read_result cx v st` >> rename1 `_ = (forced,sf)` >>
      Cases_on `forced`
      >- (simp[] >> rename1 `dest_StringV sv` >> Cases_on `dest_StringV sv` >>
          simp[raise_def, return_def] >> rpt strip_tac >> gvs[]) >>
      simp[] >> strip_tac >> gvs[] >>
      drule read_result_no_control >> simp[no_control_exc_def] >>
      rpt strip_tac >> gvs[]) >>
  simp[] >> strip_tac >> gvs[] >>
  drule (cj 1 eval_expr_no_control) >> simp[no_control_exc_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem assert_reason_expr_exempt[local]:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (Assert e (AssertReason r))) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> pure_rewrite_tac[eval_assert_reason_bind, ignore_bind_def] >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem compile_assert_reason_parts[local]:
  stmt_env cenv lctx ty (Assert e (AssertReason r)) sa = (cenv',sb) ==>
  ?op s1 ok s2 fl s3 s4 entry last.
    cenv' = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,entry) /\
    stmt_env cenv lctx ty (Raise (RaiseReason r)) entry = (cenv,last) /\
    new_block ok last = (last.cs_current_bb,sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op,s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok,s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl,s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u,s4)` >> Cases_on `u` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (v,entry)` >> simp[] >>
  Cases_on `compile_reason_message cenv r entry` >>
  rename1 `_ = (msg,sm)` >> simp[] >>
  Cases_on `compile_revert_with_reason cenv msg (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm` >>
  rename1 `_ = (u,last)` >> Cases_on `u` >> simp[] >>
  Cases_on `new_block ok last` >> rename1 `_ = (x,sb1)` >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac new_block_props >> gvs[]
QED

Theorem compile_raise_reason_extends[local]:
  stmt_env cenv lctx ty (Raise (RaiseReason r)) sa = (cenv',sb) ==>
  cs_extends sa sb
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_reason_message cenv r sa` >>
  rename1 `_ = (msg,sm)` >> simp[] >>
  Cases_on `compile_revert_with_reason cenv msg (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm` >>
  rename1 `_ = (u,last)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `?ml str. r = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[compile_reason_message_def, comp_bind_def, comp_return_def] >>
      Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) ml sa` >>
      rename1 `_ = (buf,s1)` >> gvs[] >>
      irule (INST_TYPE [alpha |-> ``:type``] bytelike_revert_extends) >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`cenv`,
        `type_memory_bytes cenv (expr_type (Literal (BaseT (StringT ml)) (StringL str)))`,
        `BaseT (StringT (LENGTH str))`,
        `expr_type (Literal (BaseT (StringT ml)) (StringL str))`] >>
      simp[is_word_type_def]) >>
  `compile_reason_message cenv r = compile_expr cenv (expr_type r) r` by
    (Cases_on `r` >> simp[compile_reason_message_def] >>
     rename1 `Literal t l` >> Cases_on `l` >> simp[compile_reason_message_def] >>
     Cases_on `t` >> gvs[compile_reason_message_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[compile_reason_message_def]) >>
  gvs[] >> drule compile_expr_extends >> strip_tac >>
  drule compile_revert_reason_split_certificate >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >> metis_tac[cs_extends_trans]
QED

Theorem assert_reason_compiler_code[local]:
  lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
  fresh_label "assert_ok" s1 = (ok,s2) /\
  fresh_label "assert_fail" s2 = (fl,s3) /\
  emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
  new_block fl s4 = (x5,entry) /\
  stmt_env cenv lctx ty (Raise (RaiseReason r)) entry = (cenv,last) /\
  new_block ok last = (x7,sb) /\ fn_has_code sa sb func ==>
  fn_has_code sa s1 func /\ fn_has_code s3 s4 func /\
  fn_has_code entry last func /\
  s3.cs_current_bb = s1.cs_current_bb /\
  s3.cs_current_insts = s1.cs_current_insts /\
  entry.cs_current_bb = fl /\ entry.cs_current_insts = [] /\
  sb.cs_current_bb = ok /\ sb.cs_current_insts = [] /\
  sa.cs_next_var <= entry.cs_next_var
Proof
  strip_tac >> drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_raise_reason_extends >> strip_tac >>
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  `cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s4 /\
   cs_extends s4 entry /\ cs_extends last sb` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block,
              cs_appends_emit_helpers, cs_appends_def] >>
  `s3.cs_next_var = s4.cs_next_var` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  simp[] >>
  metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
            cs_extends_refl]
QED

Theorem assert_reason_false_outcome_prefix[local]:
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL (BoolV F)) mid (OK t) /\
  gas_path ctx func t 0 (OK (jump_to fl t)) /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Raise (RaiseReason r)))
    (mid with gas_obs := [],jump_to fl t)
    (stmt_post ctx func cx lctx cenv cenv entry last (jump_to fl t))
    (\res ee rr. !tail. stmt_exit RetQ (ee with gas_obs := tail) res rr) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assert e (AssertReason r))) (es,s0) Q
    (\res ee rr. !tail. stmt_exit RetQ (ee with gas_obs := tail) res rr)
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL (BoolV F)) mid (OK (jump_to fl t))` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     strip_tac >> simp[] >> drule_all gas_path_then >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "normal"
  >- suspend "exit"
  >> suspend "cert"
QED

Resume assert_reason_false_outcome_prefix[normal]:
  gvs[gas_marked_exec_def] >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
  strip_tac >> drule eval_raise_reason_non_normal >> strip_tac >>
  gvs[stmt_post_def, stmt_lands_def, AllCaseEqs()]
QED
Resume assert_reason_false_outcome_prefix[exit]:
  rename1 `exit_result rr` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end`, `rr`] >> simp[] >>
  rewrite_tac[eval_assert_reason_bind] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl_tac [`mid`, `jump_to fl t`, `BoolV F`] >> simp[]
QED
Resume assert_reason_false_outcome_prefix[cert]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_assert_reason_bind] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`mid`, `jump_to fl t`, `BoolV F`] >>
  simp[GSYM ignore_bind_def]
QED
Finalise assert_reason_false_outcome_prefix

(* assert e, r: the condition and a JNZ to the ok block, where the code
   ends, and a fail block whose code is exactly raise r's.  So the fail
   branch is raise r's own judgment, at the source state the condition
   leaves when it reads false, at whatever readings the run selects. *)
Theorem compile_assert_reason_frag_general:
  !ctx func cx lctx RetQ cenv ty e r es.
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1.
       (do raw <- eval_expr cx e; read_result cx raw od)
         (es with gas_obs := gs) = (INL (BoolV F), es1) ==>
       stmt_frag ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ty (Raise (RaiseReason r)))
         (eval_stmt cx (Raise (RaiseReason r))) es1) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_reason_parts >>
  strip_tac >> gvs[] >>
  drule_all assert_reason_compiler_code >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule assert_reason_expr_admissible >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res es_end rr. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assert_reason_expr_exempt >> simp[]
QED

Resume compile_assert_reason_frag_general[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  rename1 `expr_exit (INR ex) rr` >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR ex`, `es_end`, `rr`] >> conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
      gen_tac >> simp[eval_assert_reason_bind, Once bind_def]) >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED
Resume compile_assert_reason_frag_general[normal]:
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,es_end with gas_obs := tail)` by
    gvs[gas_marked_exec_def] >>
  `?b. v = BoolV b` by
    (spose_not_then assume_tac >>
     qpat_x_assum `gas_admissible (eval_stmt _ _) _ _` mp_tac >>
     pure_rewrite_tac[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
     gvs[eval_assert_reason_bind, bind_def, raise_def, stmt_res_ok_def]) >>
  `~t.vs_halted` by
    (gvs[gas_marked_exec_def, gas_marked_path_def] >>
     drule gas_path_normal >> simp[]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `gas_path ctx func t 0
    (OK (jump_to (if b then sb.cs_current_bb else entry.cs_current_bb) t))` by
    (imp_res_tac emit_inst_extends >> irule assert_jnz_zero_path >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  Cases_on `b` >- suspend "true" >> suspend "false"
QED
Resume compile_assert_reason_frag_general[true]:
  gvs[] >> qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL ()`, `es_end`, `OK (jump_to sb.cs_current_bb t)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def] >> conj_tac
      >- simp[eval_assert_reason_bind, Once bind_def, return_def] >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
      drule_all gas_path_then >> simp[]) >>
  disj1_tac >> simp[] >> irule assert_success_post >>
  simp[] >> qexistsl_tac [`e`, `es`, `op`, `s1`] >> simp[]
QED
Resume compile_assert_reason_frag_general[false]:
  gvs[] >>
  `gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (irule assert_reason_raise_admissible >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseReason r)))
    (eval_stmt cx (Raise (RaiseReason r))) (es_end with gas_obs := [])` by
    (qpat_x_assum `!gs es1. _` irule >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `local_ptrs_reserved cenv entry` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok cenv entry (jump_to entry.cs_current_bb t)` by
    (simp[ret_pc_ok_jump_to] >> irule ret_pc_ok_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >>
     gvs[expr_post_def]) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then drule >> simp[block_is_terminated_def] >>
  disch_then (qspec_then `jump_to entry.cs_current_bb t` mp_tac) >>
  (impl_tac >- gvs[stmt_state_rel_jump_to, jump_to_def, expr_post_def]) >>
  strip_tac >>
  drule_all assert_reason_false_outcome_prefix >>
  disch_then (qspec_then `stmt_post ctx func cx lctx cenv cenv sa sb s0` mp_tac) >>
  simp[gas_outcome_def, gas_summary_at_def]
QED
Finalise compile_assert_reason_frag_general

(* assert with a string literal reason: its fail block is the literal
   raise's code. *)
Theorem compile_assert_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty e ml str es res es'.
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
      (eval_stmt cx
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))) es
Proof
  rpt strip_tac >> irule compile_assert_reason_frag_general >>
  simp[compile_raise_reason_lit_frag]
QED


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
        compile_raise_reason_lit_frag, compile_bytelike_revert_path,
        compile_assert_reason_frag_general, compile_assert_reason_lit_frag];
