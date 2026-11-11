(* Actual heterogeneous-member setup preserves allocation-backed resources. *)
Theory abiMalformedMemberSetup
Ancestors
  abiMalformedMembers abiMalformedTraversal abiDecoderMemberSetup
  abiMalformedPruneState abiMalformedRecursiveInterface abiDecoderContract abiDecoderReentry
  abiDecoderNavigationTotal abiMalformedNavigation abiDecoderReentryPointer
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  venomExecSemantics venomState venomInst valueEncoding finite_map
  words list rich_list arithmetic abiDecodeRanges contractABI vyperValue vyperABI
  abiDecoderMemberCode instIdxIndep fragExec

Theorem abi_malformed_member_setup_instructions:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,en) ==>
  EVERY (\inst. MEM inst.inst_opcode
    [MLOAD; ADD; MUL; SUB; LT; GT; EQ; ISZERO; AND; ASSERT] /\
    EVERY (\x. ~not_fresh_at st x) inst.inst_outputs) (emitted_insts st en)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  asm_simp_tac bool_ss [abi_decode_member_setup_def, compile_getelemptr_abi_def,
    compile_abi_dec_addr_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  rpt conj_tac >> irule_at Any EQ_REFL >> simp[]
QED

Theorem abi_malformed_member_setup_resource:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st ==>
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars /\
   !x. not_fresh_at st x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x` by
    (irule abi_malformed_setup_sequence_frame >>
     qexists_tac `emitted_insts st en` >> simp[] >>
     drule abi_malformed_member_setup_instructions >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
     irule abi_malformed_reserved_vars_state >> simp[lookup_var_def] >>
     qexists_tac `st` >> simp[]) >>
  qpat_x_assum `t = s with vs_vars := _` SUBST_ALL_TAC >>
  simp[abi_malformed_resource_post_def] >> rpt strip_tac >>
  Cases_on `op` >>
  fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
     not_fresh_at_def, eval_operand_def, lookup_var_def] >> metis_tac[]
QED

(* A malformed dynamic offset can wrap. Execute that guard before asking for
   a child entry; a successful guard supplies exactly the nonoverflow fact. *)
Theorem abi_malformed_member_setup_total:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,en) /\
  hi <> Lit 0w /\
  eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand base_op s = SOME (n2w B) /\
  (dyn ==> abi_decode_load MLOAD (n2w (B + (p + ao)):bytes32) s = n2w off) /\
  p < dimword (:256) /\ off < dimword (:256) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op] /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (p + (if dyn then off else ao) < dimword (:256) \/ ~dyn) /\
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    eval_operand (FST ops) t = SOME (n2w (p + if dyn then off else ao)) /\
    eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
    fresh_vars_wrt ceiling t /\ abi_decoder_address_frame st.cs_next_var s t
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `(?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
   (dyn ==> p + off < dimword (:256))` suffices_by
    (strip_tac >- (disj1_tac >> metis_tac[]) >>
     disj2_tac >> conj_tac >- (Cases_on `dyn` >> fs[ADD_COMM]) >>
     fs[EVERY_DEF] >>
     drule abi_decode_member_setup_reentry >>
     disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
     disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
     disch_then (qspecl_then [`off`, `ceiling`, `B`] mp_tac) >>
     impl_tac >- (Cases_on `dyn` >> fs[AC ADD_ASSOC ADD_COMM]) >>
     strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `dyn` >> simp[] >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T ao MLOAD base_op hi st = (child,middle)` >>
  `middle.cs_next_var <= ceiling.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `abi_decode_load MLOAD (n2w (B + (p + ao)):bytes32) s = n2w off` by
    simp[AC ADD_ASSOC ADD_COMM] >>
  drule_all abi_decode_dynamic_member_total_reentry >>
  strip_tac
  >- (disj1_tac >>
      `inst_extends st middle` by
        (qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
         Cases_on `base_op = Lit 0w` >>
         asm_simp_tac bool_ss [compile_getelemptr_abi_def, compile_abi_dec_addr_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def,
           emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def, LET_THM] >>
         rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[inst_extends_def] >>
         simp_tac (srw_ss()) [emitted_insts_def] >>
         pure_rewrite_tac [GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]) >>
      `!u. run_inst_seq (emitted_insts st middle) s <> OK u` by simp[] >>
      drule inst_extends_emit_op >> strip_tac >>
      drule_all run_inst_seq_emit_extend_err >> metis_tac[]) >>
  simp[]
QED

Theorem abi_malformed_member_setup_entry:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  eval_operand (FST ops) t = SOME (n2w child_pos) /\
  eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
  child_pos < dimword (:256) /\ vo + childsz <= outsz ==>
  abi_malformed_entry ctx func cenv cx es en sites dstid live
    base_op hi (FST ops) (SND ops) B L xs child_pos (d + vo) childsz t /\
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st` by
    fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_member_setup_resource >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `st.cs_next_var <= en.cs_next_var` by
    (Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
     Cases_on `base_op = Lit 0w` >> gvs[]) >>
  `local_ptrs_reserved cenv en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  reverse conj_tac >- simp[] >>
  drule abi_malformed_child_entry >> disch_then irule >>
  simp[] >>
  `d + outsz < dimword (:256) /\
   abi_decoder_operand_live st.cs_next_var base_op /\
   abi_decoder_operand_live st.cs_next_var hi` by
    fs[abi_malformed_entry_def] >>
  rpt conj_tac >- decide_tac >>
  irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

(* The allocated byte observation discharges navigation's load premise; no
   decoded value or well-formedness of the selected payload is assumed. *)
Theorem abi_malformed_member_setup_observed:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  p + ao + (if dyn then 32 else 0) <= L /\ vo + childsz <= outsz /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_entry ctx func cenv cx es en sites dstid live
      base_op hi (FST ops) (SND ops) B L xs
      (p + if dyn then abi_head_word (DROP (p+ao) xs) else ao)
      (d+vo) childsz t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt ceiling t
Proof
  strip_tac >>
  `hi <> Lit 0w /\ p < dimword (:256) /\ B+L < dimword (:256) /\
   mem_bytes_at B L (abi_decode_source MLOAD s) = xs /\
   eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
   eval_operand base_op s = SOME (n2w B) /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [src;dst;base_op]` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
       abi_decode_source_def] >>
  `dyn ==> abi_decode_load MLOAD (n2w (B+(p+ao)):bytes32) s =
       n2w (abi_head_word (DROP (p+ao) xs)) /\
       abi_head_word (DROP (p+ao) xs) < dimword (:256)` by
    (strip_tac >> irule abi_checked_offset_load >> qexists_tac `L` >> simp[] >> fs[]) >>
  `abi_head_word (DROP (p+ao) xs) < dimword (:256)` by
    simp[abi_head_word_def, dec_number_def, dest_NumV_def, w2n_lt] >>
  `dyn ==> abi_decode_load MLOAD (n2w (B+(p+ao)):bytes32) s =
     n2w (abi_head_word (DROP (p+ao) xs))` by metis_tac[] >>
  drule_all abi_malformed_member_setup_total >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> goal_assum (drule_at Any) >> simp[] >>
  drule abi_malformed_member_setup_entry >>
  disch_then (drule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then irule >> simp[] >>
  Cases_on `dyn` >> fs[] >> decide_tac
QED

Theorem abi_malformed_entry_inst_idx:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz (t with vs_inst_idx := n) <=>
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz t
Proof
  simp[abi_malformed_entry_def, abi_malformed_allocated_window_def,
    abi_malformed_destination_def, stmt_state_rel_inst_idx,
    eval_operand_def, lookup_var_def]
QED

Theorem abi_malformed_resource_post_inst_idx:
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s
    (t with vs_inst_idx := n) <=>
  abi_malformed_resource_post ctx func cenv cx es next sites dstid s t
Proof
  simp[abi_malformed_resource_post_def, stmt_state_rel_inst_idx,
    eval_operand_def, lookup_var_def]
QED

Theorem abi_malformed_member_setup_fragment:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,en) /\
  p + ao + (if dyn then 32 else 0) <= L /\ vo + childsz <= outsz /\
  en.cs_next_var <= ceiling.cs_next_var ==>
  frag_exec ctx st en
    (\v. v = incoming /\
      abi_malformed_entry ctx func cenv cx es st sites dstid live
        base_op hi src dst B L xs p d outsz v /\ fresh_vars_wrt ceiling v)
    (\u. abi_malformed_entry ctx func cenv cx es en sites dstid live
      base_op hi (FST ops) (SND ops) B L xs
      (p + if dyn then abi_head_word (DROP (p+ao) xs) else ao)
      (d+vo) childsz u /\
      abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
        sites dstid incoming u /\ fresh_vars_wrt ceiling u)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en)` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all (SRULE [AC ADD_ASSOC ADD_COMM] abi_malformed_member_setup_observed) >> strip_tac
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  fs[abi_malformed_entry_inst_idx, abi_malformed_resource_post_inst_idx,
     fresh_vars_wrt_def]
QED

(* A completed child returns to the aggregate's original operands, not the
   temporary child pointers. The allocation authority remains unchanged. *)
Theorem abi_malformed_aggregate_reentry:
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
  st.cs_next_var <= en.cs_next_var /\ local_ptrs_reserved cenv en /\
  tail_sites SUBSET sites ==>
  abi_malformed_entry ctx func cenv cx es en tail_sites dstid live
    base_op hi src dst B L xs p d outsz t
Proof
  strip_tac >>
  drule abi_malformed_child_entry >> disch_then irule >> simp[] >>
  `p < dimword (:256) /\ d+outsz < dimword (:256) /\
   eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;hi;src;dst]` by
    fs[abi_malformed_entry_def] >>
  `eval_operand src t = SOME (n2w p) /\ eval_operand dst t = SOME (n2w d)` by
    (fs[abi_malformed_resource_post_def, EVERY_DEF] >> metis_tac[]) >>
  simp[] >> fs[EVERY_DEF] >> rpt conj_tac >>
  irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED
