Theory bodyAbiDecodeGuardedLoopSourceFrameMods
Ancestors
  bodyFullAbiDecodeLoopSourceExact bodyFullAbiDecodeLeafCases decoderArraySetupPtr calldataDynOwned
  bodyPtrBopScalarOutcome bodyPtrBopScalarSeq stateFrame
  allocaFootprint emitHelperProps exprLoweringProps freshWrites
  compileEnv emitHelper venomInst venomExecSemantics venomState
  abiDecoderIndexedAddress abiDecoderReentry loweringStateRelDefs
  words list rich_list finite_map
  bodyFullAbiDecodeRelativeLoadExact[qualified]

(* The shared owned-state quotation; this introduces no HOL constant. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==> b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

(* The source packet is retained at the raw ADD/MUL/ADD endpoint.  The scalar-prefix frame supplies the three non-memory taint equalities. *)
local
  val old = concl
    bodyFullAbiDecodeLoopSourceExactTheory.abi_decode_loop_source_joint_exact
  val (pre, post) = dest_imp old
  val (ws, body) = strip_exists post
  val fields = ``tnu.t_stor = tn.t_stor /\
    tnu.t_trans = tn.t_trans /\ tnu.t_imm = tn.t_imm``
  val tm = mk_imp (pre, list_mk_exists (ws, mk_conj (body, fields)))
in
  val abi_decode_loop_source_frame_statement =
    list_mk_forall (free_vars tm, tm)
end

Theorem abi_decode_loop_source_frame_exact:
  ^abi_decode_loop_source_frame_statement
Proof
  rpt gen_tac >> strip_tac >>
  `abi_decode_indexed_address src idx asz sa = (head,sb)` by
    simp[abi_decode_indexed_address_def, comp_bind_def] >>
  drule_all calldataDynOwnedTheory.calldata_indexed_address_repeat >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. idx = Var x ==> not_fresh_at sa x)` by
    (conj_tac >> rpt strip_tac >> gvs[abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def]) >>
  drule_all clean_scaled_source_prefix_endpoint_ptr_origin_core_exact_frame >>
  disch_then (qspecl_then [`ARB`, `cx`, `ctx`, `PG`, `ARB`] strip_assume_tac) >>
  `!i. MEM i (emitted_insts sa sb) ==> MEM i.inst_opcode [ADD;MUL]` by
    (qpat_x_assum `emit_op ADD [src;Lit 32w] sa = _` mp_tac >>
     qpat_x_assum `emit_op MUL _ s1 = _` mp_tac >>
     qpat_x_assum `emit_op ADD [data;offset] s2 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, comp_ignore_bind_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `MEM i _` mp_tac >>
     pure_rewrite_tac [emitted_insts_def, compile_state_accfupds,
       compile_state_accessors, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND,
       combinTheory.K_THM, MEM, mk_inst_def, instruction_accessors] >>
     rpt strip_tac >> gvs[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (mp_tac (Q.SPECL [`emitted_insts sa sb`, `\x:string. F`, `s`, `t`]
      run_inst_seq_protected_frame) >>
     impl_tac >- (conj_tac >- (rpt gen_tac >> strip_tac >>
       `MEM i.inst_opcode [ADD;MUL]` by metis_tac[] >>
       `MEM i.inst_opcode
         [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
          EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
          SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN; ASSERT; ASSERT_UNREACHABLE]`
         by (fs[MEM] >> metis_tac[]) >>
       drule_all bop_scalar_inst_protected_frame >> simp[]) >> simp[]) >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_assum `emit_op ADD [src;Lit 32w] sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MUL _ s1 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD [data;offset] s2 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[] >>
     qpat_x_assum `emit_op ADD [src;Lit 32w] sa = _` mp_tac >>
     qpat_x_assum `emit_op MUL _ s1 = _` mp_tac >>
     qpat_x_assum `emit_op ADD [data;offset] s2 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, comp_ignore_bind_def] >>
     rpt strip_tac >> gvs[]) >>
  qabbrev_tac `r = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame r = state_frame (s with vs_inst_idx := r.vs_inst_idx)` by
    (simp[Abbr `r`] >>
     qpat_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  `alloca_history fn r` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sb`] >>
     fs[Abbr `r`, inst_extends_def, IS_PREFIX_APPEND, EVERY_MEM, MEM] >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` drule >> strip_tac >> simp[]) >>
  `(^owned_decoder_state) sb r HG u` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
     asm_rewrite_tac[] >> simp[Abbr `r`, lookup_var_def] >>
     metis_tac[lookup_var_def]) >>
  qexistsl_tac [`r`, `HG`, `u`] >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- (qexists_tac `t` >> simp[Abbr `r`]) >>
  conj_tac >- (gen_tac >> first_assum irule >> simp[]) >>
  asm_rewrite_tac[] >>
  simp[Abbr `r`, eval_operand_def, lookup_var_def, word_add_n2w] >>
  conj_tac >- metis_tac[GSYM word_add_n2w, GSYM word_mul_n2w,
    arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM,
    arithmeticTheory.MULT_COMM] >>
  conj_tac >- (qpat_assum `!x. data = Var x ==> not_fresh_at sb x` mp_tac >>
    Cases_on `data` >>
    simp[NoAsms, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
         not_fresh_at_def]) >>
  metis_tac[lookup_var_def]
QED
