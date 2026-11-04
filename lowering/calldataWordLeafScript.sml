(* Operational calldata primitive-word decoding companions. *)
Theory calldataWordLeaf
Ancestors
  safeSequence entryDecodeProps abiDecoderClampedWord abiDecoderReservation
  abiDecoderGuards moduleLoweringProps
  abiDecoderAllocation abiDecoderContract abiEncoder emitHelperProps
  exprLoweringProps compileEnv emitHelper valueEncoding valueEncodingProps
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_frame_bytes:
  abi_decode_frame d n s t /\ (q + k <= d \/ d + n <= q) ==>
  mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory
Proof
  simp[abi_decode_frame_def] >> metis_tac[]
QED

Theorem abi_decoder_budget_allocation_eq:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (abi_decoder_budget first last b cap t = abi_decoder_budget first last b cap s)
Proof
  simp[abi_decoder_budget_def, abi_decoder_missing_def]
QED

Theorem calldata_word_accepted_sequence:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ fresh_vars_wrt st s /\
  abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (val_op,c1)` >>
  rename1 `compile_abi_clamp_basetype val_op clamp c1 = ((),c2)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all decode_clamp_frame >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d) /\
   eval_operand val_op s2 = SOME (abi_decode_load CALLDATALOAD p s)` by metis_tac[] >>
  drule_all emit_void_MSTORE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule compile_abi_clamp_structure >> strip_tac >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `s2.vs_memory = s.vs_memory /\ s2.vs_call_ctx = s.vs_call_ctx /\
   s2.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `vars_pc_only s1 s2` mp_tac >>
     simp[vars_pc_only_def, venom_state_component_equality]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     qexists_tac `emitted_insts st st'` >> simp[] >>
     `compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
        (DecPrimWord clamp) st = ((),st')` by
       simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
            comp_bind_def, comp_ignore_bind_def] >>
     drule_all abi_decoder_clamped_word_shape >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  gvs[w2n_n2w, mstore_mem_word_at_same] >>
  simp[abi_decode_frame_def] >> rpt strip_tac >>
  qpat_x_assum `s2.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem calldata_word_rejected_sequence:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  eval_operand src s = SOME p /\ fresh_vars_wrt st s /\
  ~abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (val_op,c1)` >>
  rename1 `compile_abi_clamp_basetype val_op clamp c1 = ((),c2)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all decode_clamp_frame >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = Abort Revert_abort t` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule compile_abi_clamp_structure >> strip_tac >>
  `run_inst_seq (emitted_insts c1 st') s1 = Abort Revert_abort t` by
    (irule run_inst_seq_abort_extends >> qexists_tac `c2` >> simp[]) >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

Theorem calldata_clamp_instruction_safe:
  !cl op st st'. compile_abi_clamp_basetype op cl st = ((),st') ==>
  EVERY (\i. !s. inst_mem_below_frontier i s) (emitted_insts st st')
Proof
  Cases >> rpt gen_tac >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]
QED

Theorem calldata_prefix_safe_append:
  (!pre i post u. xs = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u) /\
  (!t. run_inst_seq xs s = OK t ==>
    !pre i post u. ys = pre ++ i::post /\ run_inst_seq pre t = OK u ==>
      inst_mem_below_frontier i u) ==>
  !pre i post u. xs ++ ys = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u
Proof
  rpt strip_tac >>
  `(?l. xs = pre ++ [i] ++ l /\ post = l ++ ys) \/
   (?l. pre = xs ++ l /\ ys = l ++ [i] ++ post)` by
    metis_tac[APPEND_EQ_APPEND_MID, APPEND, APPEND_ASSOC] >> gvs[]
  >- (qpat_x_assum `!pre' i' post' u'. pre ++ [i] ++ l = _ /\ _ ==> _` irule >>
      qexistsl_tac [`l`, `pre`] >> simp[]) >>
  Cases_on `run_inst_seq xs s`
  >- (drule run_inst_seq_append >> disch_then (qspec_then `l` assume_tac) >>
      fs[] >>
      qpat_x_assum `!pre' i' post' u'. l ++ [i] ++ post = _ /\ _ ==> _` irule >>
      qexistsl_tac [`post`, `l`] >> gvs[])
  >> `!t. run_inst_seq xs s <> OK t` by simp[] >>
  drule run_inst_seq_append_err >> disch_then (qspec_then `l` assume_tac) >> gvs[]
QED

Theorem calldata_prefix_safe_every:
  EVERY (\i. !s. inst_mem_below_frontier i s) xs ==>
  !pre i post u. xs = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    inst_mem_below_frontier i u
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem calldata_mstore_prefix_safe:
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  d + 32 <= s.vs_alloca_next ==>
  !pre i post u. [mk_inst id MSTORE [dst; value] []] = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  rpt strip_tac >> Cases_on `pre` >> gvs[run_inst_seq_def] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, mk_inst_def, w2n_n2w] >>
  Cases_on `eval_operand value s` >> simp[]
QED

Theorem calldata_clamp_store_prefix_safe:
  compile_abi_clamp_basetype value clamp st = ((),st') /\
  eval_operand value s = SOME w /\ fresh_vars_wrt st s /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  d + 32 <= s.vs_alloca_next ==>
  !pre i post u.
    emitted_insts st st' ++ [mk_inst id MSTORE [dst; value] []] = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >> ho_match_mp_tac calldata_prefix_safe_append >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_clamp_instruction_safe >> simp[]) >>
  gen_tac >> strip_tac >> drule_all decode_clamp_frame >>
  Cases_on `abi_clamp_ok clamp w` >> simp[] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_mstore_prefix_safe) >>
  qexists_tac `d` >> simp[] >>
  qpat_x_assum `vars_pc_only s t` mp_tac >>
  simp[vars_pc_only_def, venom_state_component_equality]
QED

Theorem calldata_word_prefix_safe:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ d + 32 <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule compile_abi_clamp_structure >> strip_tac >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st' /\
   emitted_insts c1 st' = emitted_insts c1 c2 ++ emitted_insts c2 st'` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. !u. inst_mem_below_frontier i u) (emitted_insts st c1)` by
    (drule emitted_insts_emit_op >> simp[] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (`EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
        (emitted_insts st c1)` by
       (drule emitted_insts_emit_op >> simp[mk_inst_def,
          is_terminator_def, is_alloca_op_def]) >>
     drule_all abi_decode_sequence_allocation_frame >> simp[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s1` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >> simp[]) >>
  drule emitted_insts_emit_void >> simp[] >> strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_clamp_store_prefix_safe) >>
  qexistsl_tac [`abi_decode_load CALLDATALOAD p s`, `d`, `clamp`] >>
  simp[] >> metis_tac[]
QED

Theorem calldata_word_accepted_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  d < dimword (:256) /\ d + 32 <= initial.vs_alloca_next /\
  fresh_vars_wrt st initial /\
  abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p initial) ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p initial) /\
         mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
         abi_decode_frame d 32 initial t /\ fresh_vars_wrt st' t /\
         (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
         t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by (fs[EVERY_MEM] >> metis_tac[]) >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_word_prefix_safe) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all calldata_word_accepted_sequence >> strip_tac >>
  qexists_tac `t` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def,
      instIdxIndepTheory.eval_op_inst_idx] >> metis_tac[]
QED

Theorem calldata_word_rejected_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  d < dimword (:256) /\ d + 32 <= initial.vs_alloca_next /\
  fresh_vars_wrt st initial /\
  ~abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p initial) ==>
  frag_exec_mem ctx st st' (\s. s = initial) (K F)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by (fs[EVERY_MEM] >> metis_tac[]) >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_word_prefix_safe) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all calldata_word_rejected_sequence >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

(* Operational totality: arbitrary calldata either passes the actual clamp or
   exits through the generated assertion. No source-encoding premise is used. *)
Theorem calldata_word_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord clamp) st = ((),st') /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  d < dimword (:256) /\ d + 32 <= initial.vs_alloca_next /\
  fresh_vars_wrt st initial ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p initial) /\
         mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
         abi_decode_frame d 32 initial t /\ fresh_vars_wrt st' t /\
         (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
         t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >> Cases_on `abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p initial)`
  >- (drule_all calldata_word_accepted_frag_mem >> strip_tac >>
      first_x_assum (qspec_then `ctx` assume_tac) >>
      irule fragExecMemTheory.frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all calldata_word_rejected_frag_mem >> strip_tac >>
  first_x_assum (qspec_then `ctx` assume_tac) >>
      irule fragExecMemTheory.frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[]
QED
