(* Finite traversal of arbitrary input with allocation-backed child resources. *)
Theory abiMalformedTraversal
Ancestors
  abiMalformedRecursiveInterface abiMalformedNavigation abiMalformedPrefix contractABI abiDecoderLoopEmit
  abiDecoderLoop abiDecoderLoopCode abiDecoderLoopRegisters abiDecoderExecution abiDecoderReentry
  abiDecoderPrimitiveLoopEntry
  abiMalformedPruneState abiDecoderReentryAddress abiDecoderArrayBackedge abiDecoderContract
  exprSimAlloc localPtrsProps venomMemProps venomMemDefs valueEncodingProps
  exprLoweringProps emitHelperProps abiEncoder emitHelper venomInst
  abiDecoderLoopSetup abiDecoderIndexedAddress
  abiDecoderStaticLoopSetup abiDecoderDynamicLoopSetup
  abiDecoderReentryPointer abiDecoderAbortReentry abiDecoderVarExtend
  abiDecoderVarSequence fragExec compileEnv loweringStateRelDefs
  venomState venomExecSemantics finite_map pred_set words list arithmetic

(* The generated header changes registers only. In particular it retains the
   state relation needed by a nested child's literal ALLOCA, even on reentry. *)
Theorem abi_malformed_header_resource:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
  st.cs_next_var <= first /\
  first + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  abi_malformed_resource_post ctx func cenv cx es first sites dstid s
    (jump_to lbl (abi_decode_position_header_state base_op first B p j n s)) /\
  fresh_vars_wrt limit_st
    (jump_to lbl (abi_decode_position_header_state base_op first B p j n s))
Proof
  strip_tac >> drule_all abi_decoder_position_header_registers >>
  disch_then (qspecl_then [`p`, `n`, `j`, `B`] strip_assume_tac) >>
  qabbrev_tac `h = abi_decode_position_header_state base_op first B p j n s` >>
  `h = s with vs_vars := h.vs_vars` by
    (Cases_on `base_op = Lit 0w` >>
     simp[Abbr `h`, abi_decode_position_header_state_def, update_var_def]) >>
  `stmt_state_rel ctx func cenv cx es h` by
    (qpat_assum `h = s with vs_vars := _` SUBST1_TAC >>
     irule abi_malformed_reserved_vars_state >> simp[] >> qexists_tac `st` >> simp[] >>
     rpt strip_tac >>
     `abi_decoder_operand_live first (Var x)` by
       (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
        metis_tac[LESS_EQ_TRANS]) >>
     qpat_x_assum `!op. _ ==> _` drule >> simp[eval_operand_def, lookup_var_def]) >>
  simp[abi_malformed_resource_post_def, stmt_state_rel_jump_to] >>
  Cases_on `base_op = Lit 0w` >>
  fs[Abbr `h`, abi_decode_position_header_state_def, update_var_def, jump_to_def,
     eval_operand_def, lookup_var_def]
QED


(* Unlike continuation-only iteration, this rule retains a child's actual
   abort. The invariant is generalized at every iteration, so a nested child
   may reuse its own ALLOCA sites and visit arbitrarily many basic blocks. *)
Theorem abi_malformed_finite_outcome:
  !n j inv s.
    j <= n /\ inv j s /\
    (!k u. k < n /\ inv k u /\ ~u.vs_halted /\
       u.vs_current_bb = header.cs_current_bb /\
       u.vs_inst_idx = LENGTH header.cs_current_insts ==>
       frag_outcome ctx func u header (inv (SUC k))
         (\r. ?v. r = Abort Revert_abort v)) /\
    (!u. inv n u /\ ~u.vs_halted /\
       u.vs_current_bb = header.cs_current_bb /\
       u.vs_inst_idx = LENGTH header.cs_current_insts ==>
       frag_outcome ctx func u en Q (\r. ?v. r = Abort Revert_abort v)) /\
    ~s.vs_halted /\ s.vs_current_bb = header.cs_current_bb /\
    s.vs_inst_idx = LENGTH header.cs_current_insts ==>
    frag_outcome ctx func s en Q (\r. ?v. r = Abort Revert_abort v)
Proof
  completeInduct_on `n-j` >> rpt strip_tac >>
  rename1 `loop_inv j s` >>
  Cases_on `j = n` >- metis_tac[] >>
  `j < n` by decide_tac >>
  `frag_outcome ctx func s header (loop_inv (SUC j))
      (\r. ?v. r = Abort Revert_abort v)` by metis_tac[] >>
  irule frag_outcome_compose >> qexistsl_tac [`loop_inv (SUC j)`, `header`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!m. m < _ ==> _` (qspec_then `n-SUC j` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`n`, `SUC j`] mp_tac) >> simp[] >>
  disch_then irule >> simp[] >> qexists_tac `loop_inv` >> simp[]
QED

(* The index write is authorized by its own ALLOCA, independently of result
   storage. All other incoming allocations are preserved, without imposing
   any order on their physical addresses. *)
Theorem abi_malformed_index_store_resource:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\
  inst.inst_id IN sites ==>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s (mstore slot w s)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore slot w s)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`slot`, `inst`, `32`] >> simp[] >> rpt strip_tac >>
     `loweringStateRelDefs$regions_disjoint slot 32 lb lsz` by
       (fs[stmt_state_rel_def, state_rel_def] >>
        drule_all local_ptrs_rel_alloca_disjoint >> simp[]) >>
     gvs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  simp[abi_malformed_resource_post_def, mstore_def, write_memory_with_expansion_def] >>
  rpt strip_tac >>
  `aid <> inst.inst_id` by metis_tac[] >>
  `allocas_non_overlapping s` by gvs[stmt_state_rel_def, alloca_inv_def] >>
  `slot + 32 <= B \/ B + cap <= slot` by
    (fs[allocas_non_overlapping_def] >> first_x_assum drule_all >> decide_tac) >>
  mp_tac (Q.SPECL [`B`, `L`, `slot`, `w`, `s`] mstore_mem_bytes_at_disjoint) >>
  simp[mstore_def, write_memory_with_expansion_def] >> decide_tac
QED

Theorem abi_malformed_resource_jump[simp]:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s (jump_to lbl t) <=>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t
Proof
  simp[abi_malformed_resource_post_def, stmt_state_rel_jump_to, jump_to_def]
QED

Theorem abi_malformed_backedge_resource:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ st.cs_next_var <= first /\ first <= next /\
  next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\ inst.inst_id IN sites ==>
  abi_malformed_resource_post ctx func cenv cx es first sites dstid s
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s))) /\
  fresh_vars_wrt limit_st
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s)))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var (STRING #"%" (toString next)) w s` >>
  `stmt_state_rel ctx func cenv cx es u` by
    (simp_tac bool_ss [Abbr `u`, update_var_def] >>
     irule abi_malformed_reserved_vars_state >> simp[] >> qexists_tac `st` >>
     simp[lookup_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `abi_malformed_resource_post ctx func cenv cx es first sites dstid s u` by
    (simp[abi_malformed_resource_post_def, Abbr `u`, update_var_def] >>
     rpt strip_tac >>
     `abi_decoder_operand_live next op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >>
     drule abi_decoder_generated_update_operand >>
     simp[update_var_def]) >>
  `abi_malformed_resource_post ctx func cenv cx es first sites dstid u (mstore slot w u)` by
    (irule abi_malformed_index_store_resource >> simp[] >>
     qexistsl_tac [`inst`, `q`] >> simp[Abbr `u`, update_var_def]) >>
  drule_all abi_malformed_resource_trans >> strip_tac >>
  conj_tac
  >- simp[] >>
  simp[Abbr `u`, fresh_vars_wrt_def, jump_to_def, mstore_def,
       write_memory_with_expansion_def, update_var_def] >>
  drule_all abi_decoder_generated_update_fresh >>
  simp[fresh_vars_wrt_def, update_var_def]
QED

Theorem abi_malformed_outcome_sim:
  abi_decode_sim ctx func s t /\ frag_outcome ctx func t en Q R ==>
  frag_outcome ctx func s en Q R
Proof
  rw[abi_decode_sim_def, frag_outcome_def]
  >- (disj1_tac >> qexists_tac `t'` >> simp[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[exit_result_not_error]
QED

(* An arbitrary multi-block child can either reject, or run the actual
   increment/store/jump backedge. No operational pruning is inserted. *)
Theorem abi_malformed_child_backedge:
  frag_exec ctx child child_end P C (\r. ?v. r = Abort Revert_abort v) /\
  fn_has_code child child_end func /\ P s /\
  ~s.vs_halted /\ s.vs_current_bb = child.cs_current_bb /\
  s.vs_inst_idx = LENGTH child.cs_current_insts /\
  lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = child_end.cs_current_insts ++
    abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  header.cs_current_bb = hdr /\ header.cs_current_insts = [] /\
  ip <> Var nv /\ j < n /\ n < dimword (:256) /\
  (!u. C u ==> eval_operand (Var iv) u = SOME (n2w j) /\
    eval_operand ip u = SOME p /\
    Q (jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) u)))) ==>
  frag_outcome ctx func s header Q (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >> drule_all frag_outcome_apply >> strip_tac >>
  irule frag_outcome_compose >> qexistsl_tac [`C`, `child_end`] >> simp[] >>
  rpt strip_tac >>
  `eval_operand (Var iv) t = SOME (n2w j) /\ eval_operand ip t = SOME p /\
   Q (jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) t)))` by metis_tac[] >>
  irule abi_malformed_outcome_sim >>
  qexists_tac `jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) t))` >>
  conj_tac
  >- (irule abi_decode_backedge_sim >> simp[] >>
      conj_tac >- (qexists_tac `n` >> simp[]) >>
      qexistsl_tac [`id`, `ip`, `iv`, `child_end.cs_current_insts`] >> simp[]) >>
  irule frag_outcome_refl >> simp[jump_to_def, mstore_def, update_var_def,
    write_memory_with_expansion_def]
QED

(* Complete framing for the read-only setup instruction set. *)
Theorem abi_malformed_setup_step_frame:
  MEM inst.inst_opcode [MLOAD; ADD; MUL; SUB; LT; GT; EQ; ISZERO; AND; ASSERT] /\
  step_inst_base inst s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  !x. ~MEM x inst.inst_outputs ==>
    FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> Cases_on `inst.inst_opcode = MLOAD`
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      strip_tac >> gvs[exec_read1_def, AllCaseEqs()] >>
      simp[update_var_def, FLOOKUP_UPDATE, venom_state_component_equality]) >>
  irule step_pure_opcode_frame >> simp[] >>
  fs[]
QED

Theorem abi_malformed_setup_sequence_frame:
  EVERY (\inst. MEM inst.inst_opcode
    [MLOAD; ADD; MUL; SUB; LT; GT; EQ; ISZERO; AND; ASSERT] /\
    EVERY (\x. ~P x) inst.inst_outputs) insts /\
  run_inst_seq insts s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  !x. P x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> irule run_inst_seq_protected_frame >>
  qexists_tac `insts` >> simp[] >> rpt strip_tac >>
  `MEM i.inst_opcode [MLOAD; ADD; MUL; SUB; LT; GT; EQ; ISZERO; AND; ASSERT] /\
   EVERY (\x. ~P x) i.inst_outputs` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_malformed_setup_step_frame >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_malformed_setup_instructions:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,en) ==>
  EVERY (\inst. MEM inst.inst_opcode
    [MLOAD; ADD; MUL; SUB; LT; GT; EQ; ISZERO; AND; ASSERT] /\
    EVERY (\x. ~not_fresh_at st x) inst.inst_outputs) (emitted_insts st en)
Proof
  Cases_on `dec_info_needs_offset di` >>
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  asm_simp_tac bool_ss [abi_decode_array_element_setup_def,
    abi_decode_indexed_address_def, compile_abi_dec_addr_def,
    compile_abi_decode_dyn_elem_ptr_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND,
    mk_inst_def, not_fresh_at_def] >>
  rpt conj_tac >> irule_at Any EQ_REFL >> simp[]
QED

Theorem abi_malformed_setup_frame:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  !x. not_fresh_at st x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> irule abi_malformed_setup_sequence_frame >>
  qexists_tac `emitted_insts st en` >>
  asm_rewrite_tac[] >> drule abi_malformed_setup_instructions >> simp[]
QED

(* Concrete setup now crosses the executable resource boundary in one step. *)
Theorem abi_malformed_setup_resource:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >> drule_all abi_malformed_setup_frame >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
     irule abi_malformed_reserved_vars_state >> simp[lookup_var_def] >>
     qexists_tac `st` >> simp[]) >>
  qpat_x_assum `t = s with vs_vars := _` SUBST_ALL_TAC >>
  simp[abi_malformed_resource_post_def] >> rpt strip_tac >>
  Cases_on `op` >>
  fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

(* Static elements need no offset guard; this supplies the actual prepared
   child state, including the resource relation absent from address_frame. *)
Theorem abi_malformed_static_setup_entry:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,en) /\
  ~dec_info_needs_offset di /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME ipw /\ mload (w2n ipw) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var ip /\
  p + 32 + j * abi_sz < dimword (:256) /\
  d + 32 + j * mem_sz + childsz <= d + outsz /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_entry ctx func cenv cx es en sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
      (p + 32 + j * abi_sz) (d + 32 + j * mem_sz) childsz t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand ip t = SOME ipw /\ fresh_vars_wrt limit_st t
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
   abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by fs[abi_malformed_entry_def] >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  `st.cs_next_var <= en.cs_next_var` by
    (drule_all abi_decode_static_element_setup_operands >> simp[]) >>
  `local_ptrs_reserved cenv en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def]) >>
  `stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st` by
    fs[abi_malformed_entry_def] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t` by
    (drule_all abi_malformed_setup_resource >> simp[]) >>
  `d + 32 + j * mem_sz + childsz < dimword (:256)` by
    (fs[abi_malformed_entry_def] >> decide_tac) >>
  `abi_decoder_operand_live en.cs_next_var base_op /\
   abi_decoder_operand_live en.cs_next_var hi` by
    (fs[abi_malformed_entry_def] >> conj_tac >>
     irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  irule abi_malformed_child_entry >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

(* Total pointer checking tolerates old loop registers; pruning is only a
   simulation device and both alternatives are restored to actual execution. *)
Theorem abi_malformed_array_pointer_total_reentry:
  compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data hi sz st = (child_op,en) /\
  hi <> Lit 0w /\ abi_decode_source_opcode opc /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand elem_src s = SOME (n2w pos) /\
  eval_operand src_data s = SOME (n2w data_base) /\ eval_operand hi s = SOME h /\
  abi_decode_load opc (n2w (B + pos):bytes32) s = n2w child_off /\
  child_off < dimword (:256) /\ data_base < dimword (:256) /\
  sz < dimword (:256) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;elem_src;src_data;hi] /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (data_base + child_off + sz <= w2n h /\
   ?t. run_inst_seq (emitted_insts st en) s = OK t /\
     eval_operand child_op t = SOME (n2w (data_base + child_off)) /\
     fresh_vars_wrt limit_st t /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
       eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  strip_tac >>
  `eval_operand base_op (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w B) /\
   eval_operand elem_src (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w pos) /\
   eval_operand src_data (abi_decoder_prune_vars st.cs_next_var s) = SOME (n2w data_base) /\
   eval_operand hi (abi_decoder_prune_vars st.cs_next_var s) = SOME h` by
    fs[abi_decoder_prune_eval] >>
  `abi_decode_load opc (n2w (B + pos):bytes32)
     (abi_decoder_prune_vars st.cs_next_var s) = n2w child_off` by
    fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var s)` by
    irule abi_decoder_prune_fresh >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st en)` by
    (drule_all abi_decoder_array_pointer_code >> simp[EVERY_CONJ]) >>
  drule_all abi_dynamic_array_pointer_total >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  disj2_tac >> simp[] >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_vars_extend_eval >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[abi_decoder_prune_vars_def]
QED

Theorem abi_malformed_array_pointer_extends[local]:
  compile_abi_decode_dyn_elem_ptr opc base_op head data_op hi sz st = (out,en) ==>
  inst_extends st en
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_malformed_dynamic_setup_entry:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,en) /\
  dec_info_needs_offset di /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME ipw /\ mload (w2n ipw) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var ip /\
  p + 32 + j * abi_sz + 32 <= L /\ abi_sz < dimword (:256) /\
  d + 32 + j * mem_sz + childsz <= d + outsz /\
  off = abi_head_word (DROP (p + 32 + j * abi_sz) xs) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_entry ctx func cenv cx es en sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
      (p + 32 + off) (d + 32 + j * mem_sz) childsz t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand ip t = SOME ipw /\ fresh_vars_wrt limit_st t)
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
   eval_operand base_op s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w L) /\
   hi <> Lit 0w /\ B + L < dimword (:256) /\
   mem_bytes_at B L (abi_decode_source MLOAD s) = xs /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;hi;src;dst]` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def, abi_decode_source_def] >>
  `abi_decode_load MLOAD (n2w (B + (p + 32 + j * abi_sz)):bytes32) s = n2w off /\
   off < dimword (:256)` by
    (asm_rewrite_tac[] >> irule abi_checked_offset_load >>
     qexists_tac `L` >> simp[]) >>
  drule_all abi_decode_dynamic_element_setup_split >> strip_tac >>
  drule abi_decode_array_source_setup_split >> strip_tac >>
  drule_all abi_decode_array_head_setup_counters >> strip_tac >>
  drule_all abi_decode_array_source_setup_counters >> strip_tac >>
  drule_all abi_decode_dynamic_element_setup_counters >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var /\
   c1'.cs_next_var <= limit_st.cs_next_var` by
    (Cases_on `base_op = Lit 0w` >> gvs[] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src` by fs[] >>
  drule_all abi_decode_array_head_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1') s = OK s1` >>
  `EVERY (abi_decoder_operand_live c1'.cs_next_var)
     [base_op;SND (SND head_ops);FST (SND head_ops);hi]` by
    (simp[] >> conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> fs[]) >>
  `eval_operand base_op s1 = SOME (n2w B) /\
   eval_operand hi s1 = SOME (n2w L) /\
   abi_decode_load MLOAD (n2w (B + (p + 32 + j * abi_sz)):bytes32) s1 = n2w off` by
    (drule abi_decoder_address_frame_load >> strip_tac >>
     conj_tac >- (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
     conj_tac >- (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
     asm_rewrite_tac[]) >>
  `p + 32 < dimword (:256)` by decide_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `inst_extends c1' c1` by (drule abi_malformed_array_pointer_extends >> simp[]) >>
  `inst_extends c1 en` by
    (qpat_x_assum `abi_decode_indexed_address _ _ _ _ = _` mp_tac >>
     simp[abi_decode_indexed_address_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[comp_return_def] >>
     imp_res_tac inst_extends_emit_op >> metis_tac[inst_extends_trans]) >>
  drule_all abi_malformed_array_pointer_total_reentry >> strip_tac
  >- (disj1_tac >>
      `run_inst_seq (emitted_insts st c1) s = Abort Revert_abort t` by
        (drule_all run_inst_seq_emit_extend >> simp[]) >>
      `inst_extends st c1` by metis_tac[inst_extends_trans] >>
      `!u. run_inst_seq (emitted_insts st c1) s <> OK u` by simp[] >>
      drule_all run_inst_seq_emit_extend_err >> metis_tac[]) >>
  `L < dimword (:256)` by decide_tac >>
  `p + 32 + off + abi_sz <= L` by fs[w2n_n2w] >>
  `abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi /\
   abi_decoder_operand_live st.cs_next_var base_op` by fs[] >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
     p + 32 + off + abi_sz <= hb /\ hb < dimword (:256)`` assume_tac
  >- (disj2_tac >> qexists_tac `L` >> simp[]) >>
  drule_all abi_decode_dynamic_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) s = OK u` >>
  `st.cs_next_var <= en.cs_next_var` by
    (Cases_on `base_op = Lit 0w` >> gvs[] >> decide_tac) >>
  `local_ptrs_reserved cenv en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[abi_malformed_entry_def]) >>
  `stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st` by
    fs[abi_malformed_entry_def] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s u` by
    (drule_all abi_malformed_setup_resource >> simp[]) >>
  `p + 32 + off < dimword (:256) /\
   d + 32 + j * mem_sz + childsz < dimword (:256)` by
    (fs[abi_malformed_entry_def] >> decide_tac) >>
  `abi_decoder_operand_live en.cs_next_var base_op /\
   abi_decoder_operand_live en.cs_next_var hi` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand ip u = SOME ipw` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `u` >> simp[] >>
  irule abi_malformed_child_entry >> gvs[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

(* Both layouts enter the same arbitrary state-quantified child interface.
   Dynamic setup retains its actual malformed-pointer abort alternative. *)
Theorem abi_malformed_setup_child:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz st = (ops,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME ipw /\ mload (w2n ipw) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var ip /\
  (if dec_info_needs_offset di then
     p + 32 + j * abi_sz + 32 <= L /\ abi_sz < dimword (:256)
   else p + 32 + j * abi_sz < dimword (:256)) /\
  d + 32 + j * mem_sz + childsz <= d + outsz /\
  off = (if dec_info_needs_offset di then
    abi_head_word (DROP (p + 32 + j * abi_sz) xs) else j * abi_sz) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st en func /\ fn_has_code en child_end func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  frag_exec ctx en child_end
    (\u. abi_malformed_entry ctx func cenv cx es en sites dstid live
       base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
       (p + 32 + off) (d + 32 + j * mem_sz) childsz u /\
     abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s u /\
     eval_operand (FST ops) u = SOME (n2w j) /\
     eval_operand ip u = SOME ipw /\ fresh_vars_wrt limit_st u)
    Q (\r. ?v. r = Abort Revert_abort v) ==>
  frag_outcome ctx func s child_end Q (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `en.cs_blocks = st.cs_blocks /\ en.cs_current_bb = st.cs_current_bb /\
   isPREFIX st.cs_current_insts en.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by
    (Cases_on `dec_info_needs_offset di` >>
     metis_tac[abi_decode_dynamic_element_setup_shape,
               abi_decode_static_element_setup_shape]) >>
  qmatch_asmsub_abbrev_tac `frag_exec ctx en child_end P Q` >>
  `(?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
   (?t. run_inst_seq (emitted_insts st en) s = OK t /\ P t)` by
    (Cases_on `dec_info_needs_offset di` >> full_simp_tac bool_ss []
     >- (drule_all abi_malformed_dynamic_setup_entry >> strip_tac
         >- (disj1_tac >> metis_tac[]) >>
         disj2_tac >> goal_assum (drule_at Any) >> gvs[Abbr `P`]) >>
     disj2_tac >> drule_all abi_malformed_static_setup_entry >> strip_tac >>
     goal_assum (drule_at Any) >> gvs[Abbr `P`]) >>
  `frag_exec ctx st en (\v. v = s) P (\r. ?v. r = Abort Revert_abort v)` by
    (irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
     simp_tac bool_ss [Abbr `P`, abi_malformed_entry_def, abi_malformed_allocated_window_def,
        abi_malformed_destination_def, abi_malformed_resource_post_def,
        stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def, fresh_vars_wrt_def] >>
     fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
        abi_malformed_destination_def, abi_malformed_resource_post_def,
        eval_operand_def, lookup_var_def, fresh_vars_wrt_def] >> metis_tac[]) >>
  `frag_outcome ctx func s en P (\r. ?v. r = Abort Revert_abort v)` by
    (irule frag_outcome_apply >> simp[] >> qexistsl_tac [`(\v. v = s)`, `st`] >> simp[]) >>
  irule frag_outcome_compose >> qexistsl_tac [`P`, `en`] >> simp[] >>
  rpt strip_tac >> irule frag_outcome_apply >> simp[] >>
  qexistsl_tac [`P`, `en`] >> simp[]
QED

(* Only the selected non-error continuation needs a PHI-free target. *)
Theorem abi_malformed_position_header_sim:
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts id ip src opc base_op first body_lbl exit_lbl|> /\
  abi_decode_position_loop_ready hdr ip src opc base_op B p iw n j s /\
  abi_decode_source_opcode opc /\
  src <> Var (STRING #"%" (toString first)) /\
  base_op <> Var (STRING #"%" (toString first)) /\
  n < dimword (:256) ==>
  abi_decode_sim ctx func s
    (jump_to (if j < n then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op first B p j n s))
Proof
  strip_tac >>
  `!fuel. exec_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts id ip src opc base_op first body_lbl exit_lbl|> s =
    OK (jump_to (if j < n then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op first B p j n s))` by
    (gen_tac >> irule abi_decode_position_header_control >>
     fs[abi_decode_position_loop_ready_def] >> metis_tac[]) >>
  qabbrev_tac `h = abi_decode_position_header_state base_op first B p j n s` >>
  `~h.vs_halted` by
    (Cases_on `base_op = Lit 0w` >>
     fs[Abbr `h`, abi_decode_position_header_state_def, update_var_def,
        abi_decode_position_loop_ready_def]) >>
  rw[abi_decode_sim_def] >>
  `?bb. lookup_block (if j < n then body_lbl else exit_lbl) func.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0` by
    (irule run_from_jump_target >> simp[] >> metis_tac[]) >>
  qexists_tac `SUC fuel` >>
  fs[abi_decode_position_loop_ready_def] >>
  simp[Once run_from_def, jump_to_def] >>
  qmatch_goalsub_abbrev_tac `run_blocks (SUC fuel) ctx func u` >>
  `u with vs_inst_idx := 0 = u` by simp[Abbr `u`] >>
  `?target. lookup_block u.vs_current_bb func.fn_blocks = SOME target /\
            phi_prefix_length target.bb_instructions = 0` by
    (simp[Abbr `u`] >> metis_tac[]) >>
  drule_all run_blocks_run_from_no_phi >> simp[]
QED

Theorem abi_malformed_array_header:
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts id ip src MLOAD base_op first body_lbl exit_lbl|> /\
  abi_malformed_allocated_window live B L xs s /\ p + 32 <= L /\
  eval_operand ip s = SOME (n2w slot) /\ mload slot s = n2w j /\
  eval_operand src s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w B) /\
  n = abi_head_word (DROP p xs) /\ j <= n /\ slot < dimword (:256) /\
  abi_decoder_operand_live first src /\ abi_decoder_operand_live first base_op /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
  st.cs_next_var <= first /\
  first + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?h. abi_decode_sim ctx func s h /\
    h.vs_current_bb = (if j < n then body_lbl else exit_lbl) /\
    h.vs_inst_idx = 0 /\ ~h.vs_halted /\
    abi_malformed_resource_post ctx func cenv cx es first sites dstid s h /\
    fresh_vars_wrt limit_st h /\ mload slot h = n2w j /\
    abi_malformed_allocated_window live B L xs h
Proof
  strip_tac >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) s = n2w n /\ n < dimword (:256)` by
    (asm_rewrite_tac[] >> irule abi_checked_offset_load >> qexists_tac `L` >>
     fs[abi_malformed_allocated_window_def, abi_decode_source_def]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `src <> Var (STRING #"%" (toString first)) /\
   base_op <> Var (STRING #"%" (toString first))` by
    (conj_tac >> irule abi_decoder_live_excludes_output >> qexists_tac `first` >> simp[]) >>
  `abi_decode_position_loop_ready hdr ip src MLOAD base_op B p (n2w slot) n j s` by
    simp[abi_decode_position_loop_ready_def, w2n_n2w] >>
  drule_all abi_malformed_position_header_sim >> strip_tac >>
  qabbrev_tac `h = jump_to (if j < n then body_lbl else exit_lbl)
    (abi_decode_position_header_state base_op first B p j n s)` >>
  `abi_malformed_resource_post ctx func cenv cx es first sites dstid s h /\
   fresh_vars_wrt limit_st h` by
    (simp_tac bool_ss [Abbr `h`] >> irule abi_malformed_header_resource >>
     simp[] >> qexists_tac `st` >> simp[]) >>
  qexists_tac `h` >> simp[] >>
  Cases_on `base_op = Lit 0w` >>
  fs[Abbr `h`, abi_decode_position_header_state_def, jump_to_def, update_var_def,
     mload_def, abi_malformed_allocated_window_def]
QED

(* Prefixes are over the payload after the count, while child positions are
   offsets into the whole input. Static children retain their fixed width. *)
Theorem abi_malformed_traversal_child_bytes:
  LENGTH xs = L /\ p + 32 + n * abi_sz <= L /\ j < n /\
  abi_sz = (if is_dynamic a then 32 else static_length a) ==>
  abi_reflected_head_ok a (DROP (p+32) xs) j /\
  abi_reflected_child a (DROP (p+32) xs) j =
    (if is_dynamic a then
       DROP (p+32+abi_head_word (DROP (p+32+j*32) xs)) xs
     else TAKE abi_sz (DROP (p+32+j*abi_sz) xs))
Proof
  strip_tac >>
  `j * abi_sz + abi_sz <= n * abi_sz` by
    (`SUC j * abi_sz <= n * abi_sz` by
       (irule LESS_MONO_MULT >> decide_tac) >>
     qpat_x_assum `SUC j * abi_sz <= _` mp_tac >>
     simp_tac bool_ss [MULT_CLAUSES, ADD_COMM]) >>
  Cases_on `is_dynamic a` >> gvs[] >> conj_tac
  >- (simp[abi_reflected_head_ok_def, LENGTH_DROP, dec_number_def,
           is_num_value_def] >> decide_tac)
  >- (asm_simp_tac bool_ss [abi_reflected_child_def,
          rich_listTheory.DROP_DROP_T] >>
      AP_THM_TAC >> AP_TERM_TAC >> decide_tac)
  >- (simp[abi_reflected_head_ok_def, LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_reflected_child_def,
       rich_listTheory.DROP_DROP_T] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

(* The finite traversal invariant records only the processed source prefix.
   The index has its own real allocation, not a contiguous scratch envelope. *)
Definition abi_malformed_traversal_inv_def:
  abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin j u <=>
    j <= n /\
    abi_malformed_entry ctx func cenv cx es start sites dstid live
      base_op hi src dst B L xs p d outsz u /\
    eval_operand ip u = SOME (n2w slot) /\ mload slot u = n2w j /\
    slot < dimword (:256) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (slot,32) /\
    inst.inst_id IN sites /\ inst.inst_id <> live /\ inst.inst_id <> dstid /\
    fresh_vars_wrt limit_st u /\
    abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid origin u /\
    ?avs. abi_reflected_prefix env ty (DROP (p+32) xs) j avs
End

(* The final actual header transfers the post without inspecting the exit's
   continuation, so even this endpoint does not assume a PHI-free exit. *)
Theorem abi_malformed_traversal_done:
  abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
    sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin n s /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts id ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl|> /\
  p + 32 <= L /\ n = abi_head_word (DROP p xs) /\
  start.cs_next_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  final.cs_current_bb = exit_lbl /\ final.cs_current_insts = [] ==>
  frag_outcome ctx func s final
    (\u. (?avs. abi_reflected_prefix env ty (DROP (p+32) xs) n avs) /\
      abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid origin u /\
      fresh_vars_wrt limit_st u)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  fs[abi_malformed_traversal_inv_def] >>
  `abi_malformed_allocated_window live B L xs s /\
   eval_operand src s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w B) /\
   abi_decoder_operand_live start.cs_next_var src /\
   abi_decoder_operand_live start.cs_next_var base_op /\
   stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv start` by
    fs[abi_malformed_entry_def] >>
  `start.cs_next_var <= start.cs_next_var /\
   abi_head_word (DROP p xs) <= abi_head_word (DROP p xs) /\
   start.cs_next_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var` by
    decide_tac >>
  `?h. abi_decode_sim ctx func s h /\
    h.vs_current_bb = exit_lbl /\ h.vs_inst_idx = 0 /\ ~h.vs_halted /\
    abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s h /\
    fresh_vars_wrt limit_st h /\ mload slot h = n2w (abi_head_word (DROP p xs)) /\
    abi_malformed_allocated_window live B L xs h` by
    (qsuff_tac `?h. abi_decode_sim ctx func s h /\
       h.vs_current_bb = (if abi_head_word (DROP p xs) < abi_head_word (DROP p xs)
                          then body_lbl else exit_lbl) /\
       h.vs_inst_idx = 0 /\ ~h.vs_halted /\
       abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s h /\
       fresh_vars_wrt limit_st h /\ mload slot h = n2w (abi_head_word (DROP p xs)) /\
       abi_malformed_allocated_window live B L xs h`
     >- simp[] >>
     irule abi_malformed_array_header >> simp[] >>
     reverse conj_tac >- (qexists_tac `start` >> simp[]) >>
     qexistsl_tac [`base_op`, `id`, `ip`] >>
     qexistsl_tac [`p`, `src`] >> simp[]) >>
  irule abi_malformed_outcome_sim >> goal_assum (drule_at Any) >>
  irule frag_outcome_refl >> simp[] >>
  conj_tac >- (qexists_tac `avs` >> simp[]) >>
  metis_tac[abi_malformed_resource_trans]
QED

(* The initial JMP is executed; no pruning step is part of the traversal. *)
Theorem abi_malformed_traversal_initial:
  abi_malformed_entry ctx func cenv cx es start sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME (n2w slot) /\ mload slot s = 0w /\
  slot < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\
  inst.inst_id IN sites /\ inst.inst_id <> live /\ inst.inst_id <> dstid /\
  fresh_vars_wrt limit_st s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  ?h. abi_decode_sim ctx func s h /\
    abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n s 0 h /\
    h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\ ~h.vs_halted
Proof
  strip_tac >>
  `abi_decode_sim ctx func s (jump_to hdr s)` by
    (irule abi_decoder_loop_entry_sim >> metis_tac[]) >>
  qexists_tac `jump_to hdr s` >> simp[] >>
  simp[abi_malformed_traversal_inv_def, jump_to_def,
       abi_malformed_entry_def, abi_malformed_allocated_window_def,
       abi_malformed_destination_def, eval_operand_def, lookup_var_def,
       mload_def, fresh_vars_wrt_def, abi_malformed_resource_post_def,
       stmt_state_rel_jump_to, abi_reflected_prefix_empty] >>
  fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
     abi_malformed_destination_def, mload_def] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `[]` >> simp[abi_reflected_prefix_empty]
QED

(* A successful child extends just the processed prefix, then the generated
   backedge writes the next count into the allocation-backed index slot. *)
Theorem abi_malformed_traversal_advance:
  abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
    sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin j s /\
  abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s u /\
  abi_reflected_head_ok (vyper_to_abi_type env ty) (DROP (p+32) xs) j /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j) /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty)
    (abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j)) /\
  fn_inst_ids_distinct func /\ j < n /\
  abi_decoder_operand_live start.cs_next_var ip /\
  start.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  fresh_vars_wrt limit_st u ==>
  abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
    sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin (SUC j)
    (jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString next)) (n2w (SUC j)) u)))
Proof
  strip_tac >> fs[abi_malformed_traversal_inv_def] >>
  `stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv start /\
   FLOOKUP u.vs_allocas inst.inst_id = SOME (slot,32)` by
    (fs[abi_malformed_entry_def, abi_malformed_resource_post_def] >> metis_tac[]) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid u
      (jump_to hdr (mstore slot (n2w (SUC j))
        (update_var (STRING #"%" (toString next)) (n2w (SUC j)) u))) /\
   fresh_vars_wrt limit_st
      (jump_to hdr (mstore slot (n2w (SUC j))
        (update_var (STRING #"%" (toString next)) (n2w (SUC j)) u)))` by
    (irule abi_malformed_backedge_resource >> simp[] >>
     conj_tac >- (qexists_tac `start` >> simp[]) >>
     qexistsl_tac [`inst`, `q`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `abi_malformed_resource_post ctx func cenv cx es
    start.cs_next_var sites dstid u v` >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s v` by
    metis_tac[abi_malformed_resource_trans] >>
  `abi_malformed_entry ctx func cenv cx es start sites dstid live
     base_op hi src dst B L xs p d outsz v` by
    (fs[abi_malformed_entry_def] >>
     drule_all abi_malformed_resource_window >> strip_tac >>
     drule_all abi_malformed_resource_destination >> strip_tac >>
     simp[abi_malformed_entry_def] >>
     fs[abi_malformed_resource_post_def]) >>
  `eval_operand ip v = SOME (n2w slot)` by
    (fs[abi_malformed_resource_post_def] >> metis_tac[]) >>
  `mload slot v = n2w (SUC j)` by
    simp[Abbr `v`, abi_decode_mload_jump, mload_mstore_same] >>
  `FLOOKUP v.vs_allocas inst.inst_id = SOME (slot,32)` by
    fs[abi_malformed_resource_post_def] >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid origin v` by
    metis_tac[abi_malformed_resource_trans] >>
  fs[Abbr `v`, abi_malformed_traversal_inv_def] >>
  irule_at Any abi_reflected_prefix_append >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_malformed_traversal_child_backedge:
  abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
    sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin j s /\
  abi_reflected_head_ok (vyper_to_abi_type env ty) (DROP (p+32) xs) j /\
  fn_inst_ids_distinct func /\ j < n /\ n < dimword (:256) /\
  abi_decoder_operand_live start.cs_next_var ip /\
  start.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  frag_exec ctx child child_end P
    (\u. abi_malformed_reflected_post env ty
        (abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j)
        ctx func cenv cx es start.cs_next_var sites dstid s u /\
      eval_operand (Var iv) u = SOME (n2w j) /\ fresh_vars_wrt limit_st u)
    (\r. ?v. r = Abort Revert_abort v) /\
  fn_has_code child child_end func /\ P t /\ ~t.vs_halted /\
  t.vs_current_bb = child.cs_current_bb /\
  t.vs_inst_idx = LENGTH child.cs_current_insts /\
  lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = child_end.cs_current_insts ++
    abi_decode_backedge_insts id iv (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  header.cs_current_bb = hdr /\ header.cs_current_insts = [] ==>
  frag_outcome ctx func t header
    (abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin (SUC j))
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `ip <> Var (STRING #"%" (toString next))` by
    (irule abi_decoder_live_excludes_output >>
     qexists_tac `start.cs_next_var` >> simp[]) >>
  irule abi_malformed_child_backedge >> simp[] >>
  goal_assum (drule_at (Pat `frag_exec _ _ _ _ _ _`)) >> simp[] >>
  simp[abi_decode_backedge_insts_def, mk_inst_def] >>
  qexistsl_tac [`j`, `n`, `n2w slot`] >> simp[] >>
  gen_tac >> strip_tac >>
  fs[abi_malformed_reflected_post_def] >>
  conj_tac
  >- (fs[abi_malformed_traversal_inv_def, abi_malformed_resource_post_def] >> metis_tac[]) >>
  `slot < dimword (:256)` by fs[abi_malformed_traversal_inv_def] >>
  simp[w2n_n2w] >> irule abi_malformed_traversal_advance >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* One complete guarded iteration, with a recursive contract covering every
   incoming child state rather than a preselected successful execution. *)
Theorem abi_malformed_traversal_iteration:
  abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
    sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin j s /\
  j < n /\ n = abi_head_word (DROP p xs) /\ p+32 <= L /\
  p+32+n*abi_sz <= L /\
  abi_sz = (if is_dynamic (vyper_to_abi_type env ty) then 32
            else static_length (vyper_to_abi_type env ty)) /\
  dec_info_needs_offset di = is_dynamic (vyper_to_abi_type env ty) /\
  abi_sz < dimword (:256) /\
  d+32+j*mem_sz+childsz <= d+outsz /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl|> /\
  phi_prefix_length (abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl) = 0 /\
  header.cs_current_bb = hdr /\ header.cs_current_insts = [] /\
  setup.cs_current_bb = body_lbl /\ setup.cs_current_insts = [] /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz setup = (ops,child) /\
  FST ops = Var iv /\
  fn_has_code setup child func /\ fn_has_code child child_end func /\
  lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = child_end.cs_current_insts ++
    abi_decode_backedge_insts bid iv (STRING #"%" (toString next)) ip hdr /\
  fn_inst_ids_distinct func /\ child_sites SUBSET sites /\
  start.cs_next_var <= setup.cs_next_var /\ setup.cs_next_var <= child.cs_next_var /\
  child.cs_next_var <= child_end.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
  start.cs_next_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  abi_decoder_operand_live start.cs_next_var ip /\
  abi_decoder_operand_live child.cs_next_var (Var iv) /\
  start.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  (!cp cd ceiling incoming.
    child_end.cs_next_var <= ceiling.cs_next_var ==>
    frag_exec ctx child child_end
      (\v. v = incoming /\
        abi_malformed_entry ctx func cenv cx es child child_sites dstid live
          base_op hi (FST (SND ops)) (SND (SND ops)) B L xs cp cd childsz v /\
        fresh_vars_wrt ceiling v)
      (\u. abi_malformed_reflected_post env ty
        (if is_dynamic (vyper_to_abi_type env ty) then DROP cp xs else TAKE abi_sz (DROP cp xs))
        ctx func cenv cx es child.cs_next_var child_sites dstid incoming u /\
        fresh_vars_wrt ceiling u)
      (\r. ?v. r = Abort Revert_abort v)) ==>
  frag_outcome ctx func s header
    (abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n origin (SUC j))
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `abi_malformed_entry ctx func cenv cx es start sites dstid live
      base_op hi src dst B L xs p d outsz s /\
   eval_operand ip s = SOME (n2w slot) /\ mload slot s = n2w j /\
   slot < dimword (:256) /\ fresh_vars_wrt limit_st s` by
    fs[abi_malformed_traversal_inv_def] >>
  `abi_malformed_allocated_window live B L xs s /\
   eval_operand src s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w B) /\
   abi_decoder_operand_live start.cs_next_var src /\
   abi_decoder_operand_live start.cs_next_var base_op /\
   stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv start` by
    fs[abi_malformed_entry_def] >>
  `?h. abi_decode_sim ctx func s h /\ h.vs_current_bb = body_lbl /\
    h.vs_inst_idx = 0 /\ ~h.vs_halted /\
    abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s h /\
    fresh_vars_wrt limit_st h /\ mload slot h = n2w j /\
    abi_malformed_allocated_window live B L xs h` by
    (qsuff_tac `?h. abi_decode_sim ctx func s h /\
       h.vs_current_bb = (if j < n then body_lbl else exit_lbl) /\
       h.vs_inst_idx = 0 /\ ~h.vs_halted /\
       abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s h /\
       fresh_vars_wrt limit_st h /\ mload slot h = n2w j /\
       abi_malformed_allocated_window live B L xs h`
     >- simp[] >>
     irule abi_malformed_array_header >> simp[] >>
     reverse conj_tac >- (qexists_tac `start` >> simp[]) >>
     qexistsl_tac [`base_op`, `hid`, `ip`] >>
     qexistsl_tac [`p`, `src`] >> simp[]) >>
  `local_ptrs_reserved cenv setup /\ local_ptrs_reserved cenv child` by
    (conj_tac >> irule local_ptrs_reserved_next_var >>
     qexists_tac `start` >> simp[] >> decide_tac) >>
  `abi_malformed_entry ctx func cenv cx es setup sites dstid live
      base_op hi src dst B L xs p d outsz h /\
   eval_operand ip h = SOME (n2w slot)` by
    (`live NOTIN sites /\ live <> dstid /\
      abi_malformed_destination func cenv es.scopes dstid d outsz s` by
        fs[abi_malformed_entry_def] >>
     drule_all abi_malformed_resource_window >> strip_tac >>
     drule_all abi_malformed_resource_destination >> strip_tac >>
     qpat_x_assum `!cp cd ceiling incoming. _` kall_tac >>
     qhdtm_x_assum `abi_malformed_traversal_inv` kall_tac >>
     fs[abi_malformed_entry_def, abi_malformed_resource_post_def] >>
     `EVERY (abi_decoder_operand_live setup.cs_next_var) [base_op;hi;src;dst]` by
       (fs[EVERY_DEF] >> rpt conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `start.cs_next_var` >> simp[]) >>
     fs[EVERY_DEF]) >>
  qabbrev_tac `off = if dec_info_needs_offset di then
    abi_head_word (DROP (p+32+j*abi_sz) xs) else j*abi_sz` >>
  qabbrev_tac `P = \u. abi_malformed_entry ctx func cenv cx es child sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
      (p+32+off) (d+32+j*mem_sz) childsz u /\
    abi_malformed_resource_post ctx func cenv cx es setup.cs_next_var sites dstid h u /\
    eval_operand (FST ops) u = SOME (n2w j) /\
    eval_operand ip u = SOME (n2w slot) /\ fresh_vars_wrt limit_st u` >>
  `abi_decoder_operand_live setup.cs_next_var ip` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  `(if dec_info_needs_offset di then
      p+32+j*abi_sz+32 <= L /\ abi_sz < dimword (:256)
    else p+32+j*abi_sz < dimword (:256))` by
    (`j*abi_sz+abi_sz <= n*abi_sz` by
       (`SUC j * abi_sz <= n * abi_sz` by
          (irule LESS_MONO_MULT >> decide_tac) >>
        qpat_x_assum `SUC j * abi_sz <= _` mp_tac >>
        simp_tac bool_ss [MULT_CLAUSES, ADD_COMM]) >>
     `B+L < dimword (:256)` by fs[abi_malformed_allocated_window_def] >>
     Cases_on `dec_info_needs_offset di`
     >- (`abi_sz = 32` by metis_tac[] >>
         qpat_x_assum `abi_sz = 32` SUBST_ALL_TAC >>
         simp[] >> decide_tac) >>
     qpat_x_assum `~dec_info_needs_offset di` (fn th => rewrite_tac[th]) >>
     decide_tac) >>
  `frag_outcome ctx func h child P (\r. ?v. r = Abort Revert_abort v)` by
    (qpat_x_assum `!cp cd ceiling incoming. _` kall_tac >>
     qhdtm_x_assum `abi_malformed_traversal_inv` kall_tac >>
     irule abi_malformed_setup_child >> simp_tac bool_ss [] >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
     qexistsl_tac [`childsz`, `j`, `limit_st`] >>
     simp[w2n_n2w] >>
     conj_tac >- fs[fn_has_code_def, emitted_blocks_def] >>
     simp[Abbr `P`] >>
     irule frag_exec_refl >> simp[]) >>
  `LENGTH xs = L` by
    (qhdtm_assum `abi_malformed_allocated_window` mp_tac >>
     simp_tac bool_ss [abi_malformed_allocated_window_def] >> strip_tac >>
     qpat_x_assum `mem_bytes_at B L _.vs_memory = xs` mp_tac >>
     disch_then (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
     simp[valueEncodingDefsTheory.mem_bytes_at_def, LENGTH_TAKE, LENGTH_APPEND]) >>
  `abi_reflected_head_ok (vyper_to_abi_type env ty) (DROP (p+32) xs) j /\
   abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j =
     (if is_dynamic (vyper_to_abi_type env ty) then DROP (p+32+off) xs
      else TAKE abi_sz (DROP (p+32+off) xs))` by
    (drule_all abi_malformed_traversal_child_bytes >>
     Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     fs[Abbr `off`]) >>
  `n < dimword (:256)` by
    (fs[vyperABITheory.abi_head_word_def, dec_number_def,
         dest_NumV_def, w2n_lt]) >>
  irule abi_malformed_outcome_sim >> qexists_tac `h` >> simp[] >>
  irule frag_outcome_compose >> qexistsl_tac [`P`, `child`] >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  `abi_malformed_entry ctx func cenv cx es child child_sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
      (p+32+off) (d+32+j*mem_sz) childsz t /\
   fresh_vars_wrt limit_st t` by
    (fs[Abbr `P`, abi_malformed_entry_def, SUBSET_DEF] >> metis_tac[]) >>
  qpat_x_assum `!cp cd ceiling incoming. _`
    (qspecl_then [`p+32+off`, `d+32+j*mem_sz`, `limit_st`, `t`] mp_tac) >>
  simp_tac bool_ss [] >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `n = _` SUBST_ALL_TAC >>
  irule abi_malformed_traversal_child_backedge >>
  simp[] >>
  qexists_tac `\v. v = t` >> simp[] >>
  goal_assum (drule_at (Pat `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q (abi_head_word (DROP p xs)) origin j s`)) >>
  goal_assum (drule_at (Pat `bb.bb_instructions = _`)) >> simp[] >>
  qexists_tac `child` >> simp[] >>
  irule frag_exec_conseq >>
  goal_assum (drule_at (Pat `frag_exec _ _ _ _ _ _`)) >>
  simp[] >>
  conj_tac >- fs[] >>
  qx_gen_tac `u` >> strip_tac >>
  `eval_operand (Var iv) t = SOME (n2w j)` by
    (qpat_assum `P t` mp_tac >> simp_tac bool_ss [Abbr `P`] >>
     strip_tac >> metis_tac[]) >>
  `eval_operand (Var iv) u = SOME (n2w j)` by
    (fs[abi_malformed_reflected_post_def, abi_malformed_resource_post_def] >>
     metis_tac[]) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid t u` by
    (fs[abi_malformed_reflected_post_def] >>
     irule abi_malformed_resource_weaken >>
     goal_assum (drule_at (Pat `abi_malformed_resource_post _ _ _ _ _ _ _ _ t u`)) >>
     simp[] >> decide_tac) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid h t` by
    (irule abi_malformed_resource_weaken >>
     fs[Abbr `P`] >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s u` by
    metis_tac[abi_malformed_resource_trans] >>
  fs[abi_malformed_reflected_post_def]
QED

(* Complete actual traversal, including the initial jump and empty traversal. *)
Theorem abi_malformed_traversal:
  abi_malformed_entry ctx func cenv cx es start sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME (n2w slot) /\ mload slot s = 0w /\
  slot < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\
  inst.inst_id IN sites /\ inst.inst_id <> live /\ inst.inst_id <> dstid /\
  fresh_vars_wrt limit_st s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME entry_bb /\
  entry_bb.bb_instructions = prefix ++ [mk_inst entry_id JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl|> /\
  phi_prefix_length (abi_decode_position_header_insts hid ip src MLOAD base_op start.cs_next_var body_lbl exit_lbl) = 0 /\
  header.cs_current_bb = hdr /\ header.cs_current_insts = [] /\
  final.cs_current_bb = exit_lbl /\ final.cs_current_insts = [] /\
  setup.cs_current_bb = body_lbl /\ setup.cs_current_insts = [] /\
  n = abi_head_word (DROP p xs) /\ p+32 <= L /\ p+32+n*abi_sz <= L /\
  abi_sz = (if is_dynamic (vyper_to_abi_type env ty) then 32
            else static_length (vyper_to_abi_type env ty)) /\
  dec_info_needs_offset di = is_dynamic (vyper_to_abi_type env ty) /\
  abi_sz < dimword (:256) /\
  (!j. j<n ==> d+32+j*mem_sz+childsz <= d+outsz) /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz setup = (ops,child) /\
  FST ops = Var iv /\
  fn_has_code setup child func /\ fn_has_code child child_end func /\
  lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = child_end.cs_current_insts ++
    abi_decode_backedge_insts bid iv (STRING #"%" (toString next)) ip hdr /\
  fn_inst_ids_distinct func /\ child_sites SUBSET sites /\
  start.cs_next_var <= setup.cs_next_var /\ setup.cs_next_var <= child.cs_next_var /\
  child.cs_next_var <= child_end.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
  start.cs_next_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  abi_decoder_operand_live start.cs_next_var ip /\
  abi_decoder_operand_live child.cs_next_var (Var iv) /\
  start.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  (!cp cd ceiling incoming.
    child_end.cs_next_var <= ceiling.cs_next_var ==>
    frag_exec ctx child child_end
      (\v. v = incoming /\
        abi_malformed_entry ctx func cenv cx es child child_sites dstid live
          base_op hi (FST (SND ops)) (SND (SND ops)) B L xs cp cd childsz v /\
        fresh_vars_wrt ceiling v)
      (\u. abi_malformed_reflected_post env ty
        (if is_dynamic (vyper_to_abi_type env ty) then DROP cp xs else TAKE abi_sz (DROP cp xs))
        ctx func cenv cx es child.cs_next_var child_sites dstid incoming u /\
        fresh_vars_wrt ceiling u)
      (\r. ?v. r = Abort Revert_abort v)) ==>
  frag_outcome ctx func s final
    (\u. (?avs. abi_reflected_prefix env ty (DROP (p+32) xs) n avs) /\
      abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s u /\
      fresh_vars_wrt limit_st u)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `?h. abi_decode_sim ctx func s h /\
    abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n s 0 h /\
    h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\ ~h.vs_halted` by
    (irule abi_malformed_traversal_initial >> simp[] >>
     qexists_tac `entry_id` >> simp[]) >>
  irule abi_malformed_outcome_sim >> qexists_tac `h` >> simp[] >>
  irule abi_malformed_finite_outcome >> conj_tac >- simp[] >>
  qexistsl_tac [`header`,
    `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st
      sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q n s`,
    `0`, `n`] >>
  simp[] >>
  qpat_x_assum `n = _` SUBST_ALL_TAC >>
  qpat_x_assum `abi_sz = _` SUBST_ALL_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule abi_malformed_traversal_iteration >>
      goal_assum (drule_at (Pat `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q (abi_head_word (DROP p xs)) s k u`)) >>
      simp[] >>
      goal_assum (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `bb.bb_instructions = _`)) >>
      simp[] >> qexistsl_tac [`child_sites`, `childsz`, `exit_lbl`, `hid`] >>
      simp[] >> conj_tac >- (map_every qx_gen_tac [`pos`, `dest`, `ceil`, `initial`] >> strip_tac >>
        qpat_x_assum `!cp cd ceiling incoming. _`
          (qspecl_then [`pos`, `dest`, `ceil`, `initial`] mp_tac) >> simp[]) >>
      qpat_x_assum `!j. j < _ ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  qx_gen_tac `last` >> strip_tac >>
  irule abi_malformed_traversal_done >> simp[] >>
  goal_assum (drule_at (Pat `abi_malformed_traversal_inv ctx func cenv cx es env ty start limit_st sites dstid live base_op hi src dst B L xs p d outsz ip slot inst q (abi_head_word (DROP p xs)) s (abi_head_word (DROP p xs)) last`)) >>
  simp[] >> qexistsl_tac [`body_lbl`, `hid`] >> simp[]
QED
