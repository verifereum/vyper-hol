(*
 * Memory safety of abi_encode's tuple staging stores: every slot of
 * compile_store_abi_tuple writes below the frontier, given the buffer and
 * the nonword sources lie below it.
 *
 * TOP-LEVEL:
 *   abi_tuple_store_mem_ok
 *)
Theory bodyMemTbAbiEncodeStore
Ancestors
  fragExecMem instMemFrontier memSafeRun abiTupleProps abiTupleEncodePrepare
  abiTupleEncodeSlot emitHelperProps exprLoweringProps allocationPathGrowth
  allocationGrowth stmtReasonMemory loweringStateRelDefs context venomState
  venomExecSemantics venomInst compileEnv exprLowering abiBuiltinAllocation allocaFootprint finite_map words list arithmetic

Theorem abi_tuple_write_mem_ok[local]:
  (if is_word_type ty then emit_void MSTORE [dst;op]
   else compile_copy_memory dst op (type_memory_bytes ce ty)) st1 = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\
  d + type_memory_bytes ce ty <= s.vs_alloca_next /\
  d < dimword (:256) /\ type_memory_bytes ce ty < dimword (:256) /\
  (is_word_type ty ==> 32 <= type_memory_bytes ce ty) /\
  (~is_word_type ty /\ 0 < type_memory_bytes ce ty ==>
     ?w. eval_operand op s = SOME w /\
       w2n w + type_memory_bytes ce ty <= s.vs_alloca_next) ==>
  final.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 final /\
  final.cs_next_var = st1.cs_next_var /\
  run_inst_seq_mem_ok (emitted_insts st1 final) s /\
  !s'. run_inst_seq (emitted_insts st1 final) s = OK s' ==>
    s'.vs_vars = s.vs_vars /\ s'.vs_labels = s.vs_labels
Proof
  Cases_on `is_word_type ty` >> asm_simp_tac bool_ss [] >> strip_tac
  >- (drule emitted_insts_emit_void >> strip_tac >>
      asm_simp_tac bool_ss [run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
      conj_tac >- simp[w2n_n2w] >>
      simp[run_inst_seq_def, step_mstore_eq, AllCaseEqs()] >>
      rpt strip_tac >> gvs[mstore_def]) >>
  Cases_on `type_memory_bytes ce ty` >> gvs[]
  >- gvs[compile_copy_memory_def, comp_return_def, emitted_insts_def,
         run_inst_seq_mem_ok_def, run_inst_seq_def] >>
  gvs[compile_copy_memory_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  asm_simp_tac bool_ss [run_inst_seq_mem_ok_last, below_frontier_MCOPY] >>
  conj_tac >- simp[eval_operand_def, w2n_n2w] >>
  simp[run_inst_seq_def, step_mcopy_eq, AllCaseEqs()] >>
  rpt strip_tac >> gvs[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_tuple_slot_mem_ok[local]:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) /\
  eval_operand buf t = SOME (n2w baddr) /\ fresh_vars_wrt st t /\
  baddr+off+type_memory_bytes ce ty <= t.vs_alloca_next /\
  baddr+off+type_memory_bytes ce ty < dimword (:256) /\
  (is_word_type ty ==> 32 <= type_memory_bytes ce ty) /\
  (~is_word_type ty /\ 0 < type_memory_bytes ce ty ==>
     ?w. eval_operand op t = SOME w /\
       w2n w + type_memory_bytes ce ty <= t.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st final) t /\
  !t'. run_inst_seq (emitted_insts st final) t = OK t' ==>
    fresh_vars_wrt final t' /\
    !a w. eval_operand a t = SOME w ==> eval_operand a t' = SOME w
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_tuple_slot_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD _ st = (dst,st1)` >>
  `eval_operand (Lit (n2w off)) t = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `eval_operand dst ss' = SOME (n2w (baddr+off))` by
    (qpat_x_assum `eval_operand dst ss' = _` mp_tac >> simp[word_add_n2w]) >>
  `t.vs_alloca_next <= ss'.vs_alloca_next` by
    (drule run_inst_seq_allocation_growth >> simp[allocation_growth_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st st1) t` by
    (drule emitted_insts_emit_op >> strip_tac >> asm_rewrite_tac[] >>
     simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges,
          inst_dload_in_section_def, mk_inst_def]) >>
  mp_tac (Q.INST [`s` |-> `ss'`, `d` |-> `baddr+off`] abi_tuple_write_mem_ok) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- decide_tac >>
      conj_tac >- decide_tac >>
      conj_tac >- decide_tac >>
      conj_tac >- first_assum ACCEPT_TAC >>
      strip_tac >>
      qpat_x_assum `~is_word_type ty /\ _ ==> _` (drule_all_then strip_assume_tac) >>
      qexists_tac `w` >> conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
      decide_tac) >>
  strip_tac >>
  `emitted_insts st final = emitted_insts st st1 ++ emitted_insts st1 final` by
    (irule emitted_insts_append >> conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum SUBST1_TAC >>
  conj_tac
  >- (match_mp_tac run_inst_seq_mem_ok_append >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts st st1) t = OK s'` mp_tac >>
      qpat_assum `run_inst_seq (emitted_insts st st1) t = OK ss'`
        (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [] >> disch_then (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `run_inst_seq (emitted_insts st st1) t = OK ss'`
    (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
  gen_tac >> strip_tac >>
  `t'.vs_vars = ss'.vs_vars /\ t'.vs_labels = ss'.vs_labels` by
    (qpat_x_assum `!s'. run_inst_seq (emitted_insts st1 final) ss' = OK s' ==> _`
       drule >> simp[]) >>
  conj_tac >- fs[fresh_vars_wrt_def] >>
  rpt strip_tac >>
  `eval_operand a ss' = SOME w` by (first_assum irule >> first_assum ACCEPT_TAC) >>
  Cases_on `a` >> fs[eval_operand_def, lookup_var_def]
QED

Theorem abi_tuple_store_mem_ok:
  !xs ce buf off st final t baddr.
    compile_store_abi_tuple ce buf off xs st = ((),final) /\
    eval_operand buf t = SOME (n2w baddr) /\ fresh_vars_wrt st t /\
    baddr+off+abi_tuple_bytes ce xs <= t.vs_alloca_next /\
    baddr+off+abi_tuple_bytes ce xs < dimword (:256) /\
    EVERY (\x. is_word_type (SND x) ==> 32 <= type_memory_bytes ce (SND x)) xs /\
    EVERY (\x. ~is_word_type (SND x) /\ 0 < type_memory_bytes ce (SND x) ==>
      ?w. eval_operand (FST x) t = SOME w /\
        w2n w + type_memory_bytes ce (SND x) <= t.vs_alloca_next) xs ==>
    run_inst_seq_mem_ok (emitted_insts st final) t
Proof
  Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def] >> rpt strip_tac >>
      gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac bool_ss [EVERY_DEF] >> strip_tac >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = (u,middle)` >>
  Cases_on `u` >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [pairTheory.UNCURRY_DEF]) >>
  `abi_tuple_bytes ce ((h0,h1)::xs) = type_memory_bytes ce h1 + abi_tuple_bytes ce xs` by
    simp[abi_tuple_bytes_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  RULE_ASSUM_TAC (BETA_RULE o PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  mp_tac (Q.INST [`op` |-> `h0`, `ty` |-> `h1`, `final` |-> `middle`] abi_tuple_slot_mem_ok) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- decide_tac >>
      conj_tac >- decide_tac >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  qpat_assum `compile_store_abi_tuple _ _ _ _ middle = _`
    (strip_assume_tac o MATCH_MP abi_tuple_encode_store_shape) >>
  `emitted_insts st final = emitted_insts st middle ++ emitted_insts middle final` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  pop_assum SUBST1_TAC >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!t'. run_inst_seq (emitted_insts st middle) t = OK t' ==> _`
    (drule_then strip_assume_tac) >>
  `t.vs_alloca_next <= s'.vs_alloca_next` by
    (drule run_inst_seq_allocation_growth >> simp[allocation_growth_def]) >>
  first_x_assum (qspecl_then [`ce`, `buf`, `off + type_memory_bytes ce h1`, `middle`,
    `final`, `s'`, `baddr`] mp_tac) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- decide_tac >>
      conj_tac >- decide_tac >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `EVERY _ xs` mp_tac >> qpat_x_assum `EVERY _ xs` mp_tac >>
      simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
      qpat_x_assum `!e. MEM e xs ==> ~is_word_type _ /\ _ ==> _`
        (drule_all_then strip_assume_tac) >>
      qexists_tac `w` >> conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
      decide_tac) >>
  simp_tac bool_ss []
QED

Theorem abi_tuple_staging_mem_ok:
  compile_alloc_buffer (abi_tuple_bytes ce (xs:(operand # type) list)) st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fresh_vars_wrt st s /\ alloca_next_valid s /\
  FLOOKUP (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) s).vs_allocas
    st.cs_next_id = SOME (p,abi_tuple_bytes ce xs) /\
  p + abi_tuple_bytes ce xs < dimword (:256) /\
  EVERY (\x. is_word_type (SND x) ==> 32 <= type_memory_bytes ce (SND x)) xs /\
  EVERY (\x. ~is_word_type (SND x) /\ 0 < type_memory_bytes ce (SND x) ==>
    ?w. eval_operand (FST x) s = SOME w /\
      w2n w + type_memory_bytes ce (SND x) <= s.vs_alloca_next) xs ==>
  run_inst_seq_mem_ok (emitted_insts st staged) s
Proof
  strip_tac >>
  `abi_tuple_bytes ce (xs:(operand # type) list) < dimword (:256)` by decide_tac >>
  drule_all compile_alloc_buffer_mem_ok >> strip_tac >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  qpat_assum `compile_store_abi_tuple _ _ _ _ allocated = _`
    (strip_assume_tac o MATCH_MP abi_tuple_encode_store_shape) >>
  `emitted_insts st staged = emitted_insts st allocated ++ emitted_insts allocated staged` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  pop_assum SUBST1_TAC >>
  `s.vs_alloca_next <=
     (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce (xs:(operand # type) list)) s).vs_alloca_next /\
   (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce (xs:(operand # type) list)) s).vs_vars = s.vs_vars` by
    rw[abi_builtin_allocate_state_def] >>
  `STRING #"%" (toString st.cs_next_var) NOTIN FDOM s.vs_vars` by fs[fresh_vars_wrt_def] >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts st allocated) s = OK s'` mp_tac >>
  qpat_assum `emitted_insts st allocated = _` (fn th => rewrite_tac[th, run_inst_seq_def]) >>
  qpat_assum `step_inst_base _ s = OK _` (fn th => rewrite_tac[th]) >>
  simp_tac (srw_ss()) [run_inst_seq_def] >> disch_then (SUBST_ALL_TAC o SYM) >>
  mp_tac (Q.SPECL [`xs`, `ce`, `buf.buf_operand`, `0`, `allocated`, `staged`,
    `update_var (STRING #"%" (toString st.cs_next_var)) (n2w p)
       (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce (xs:(operand # type) list)) s)`, `p`]
    abi_tuple_store_mem_ok) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qpat_assum `buf.buf_operand = _` SUBST1_TAC >>
        simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qpat_x_assum `p + _ <= _` mp_tac >> simp[update_var_def]) >>
      conj_tac >- simp[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `EVERY (\x. ~_ /\ _ ==> _) xs` mp_tac >>
      rewrite_tac[EVERY_MEM] >> BETA_TAC >> rpt strip_tac >>
      qpat_x_assum `!x. MEM x xs ==> _` (drule_all_then strip_assume_tac) >>
      qexists_tac `w` >>
      conj_tac
      >- (qmatch_goalsub_rename_tac `eval_operand (FST xx) _` >> Cases_on `FST xx` >>
          fs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
          IF_CASES_TAC >> gvs[FLOOKUP_DEF]) >>
      simp[update_var_def] >> decide_tac) >>
  simp_tac bool_ss []
QED
