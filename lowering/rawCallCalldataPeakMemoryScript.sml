Theory rawCallCalldataPeakMemory
Ancestors
  vfmCalldataBound vfmExecution vfmExecutionProp vfmState vfmContext
  vfmConstants vfmBuffer
  dallocaBounds exprLoweringProps fmpAlignment fmpLowerSequenceExec
  dallocaCalldata rawCallCalldataDalloca
  compileEnv exprSimProps localPtrsProps loweringSlice loweringStateRelDefs stateRelProj
  valueEncodingProps
  venomExecSemantics venomLayout venomMemProps venomState
  arithmetic list words

Theorem raw_call_msg_data_peak_memory_oog_bridge:
  !ctx func (cp_fmp:num) (fmp:bytes32) (lo:num) (endpoint:num)
   (es:execution_state) (c:context) rb rest (s:venom_state).
    (wf_state es /\ calldata_bounded es /\
     es.contexts = (c, rb) :: rest /\
     s.vs_call_ctx.cc_calldata = vfmBuffer$buffer_to_list c.msgParams.data ==>
     LENGTH s.vs_call_ctx.cc_calldata < 2 ** 64 /\
     c.msgParams.gasLimit < 2 ** 64 /\
     buffer_length c.memory < 2 ** 64 /\
     (2 ** 64 <= endpoint ==>
      c.msgParams.gasLimit < memory_cost endpoint /\
      c.msgParams.gasLimit - c.gasUsed <
        memory_expansion_cost (buffer_length c.memory)
          (word_size endpoint * 32))) /\
    (LENGTH s.vs_call_ctx.cc_calldata < 2 ** 64 /\
     s.vs_initial_fmp = fmp /\
     fmp_room ctx func s /\
     (ctx_has_dalloca ctx \/
      EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)) /\
     (w2n s.vs_fmp <= w2n fmp + 2 ** 64 * 2 ** 64 \/
      w2n s.vs_fmp +
        venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
        dimword (:256)) ==>
     w2n s.vs_fmp +
       venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
       dimword (:256) /\
     fmp_room ctx func
       ((write_memory_with_expansion (w2n s.vs_fmp)
           s.vs_call_ctx.cc_calldata s) with
        vs_fmp :=
          s.vs_fmp +
          n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))) /\
     (fmp_frontier_rel cp_fmp (w2n fmp) lo s.vs_fmp ==>
      lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
        dimword (:256) /\
      fmp_frontier_rel cp_fmp (w2n fmp)
        (lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))
        (s.vs_fmp +
         n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata)))))
Proof
  rpt gen_tac >> conj_tac
  >- (strip_tac >>
      `buffer_length c.msgParams.data < 2 ** 64 /\
       c.msgParams.gasLimit < 2 ** 64` by
        (drule calldata_bounded_top >> simp[]) >>
      `buffer_length c.memory < 2 ** 64` by
        (irule calldata_bounded_memory >> qexists_tac `es` >> simp[]) >>
      conj_tac >- metis_tac[LENGTH_buffer_to_list] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      strip_tac >>
      `c.gasUsed <= c.msgParams.gasLimit` by fs[wf_state_def, wf_context_def] >>
      `memory_cost (buffer_length c.memory) <= c.gasUsed` by
        fs[calldata_bounded_def, memory_paid_def, frames_paid_def] >>
      `word_size endpoint * 32 = venomLayout$ceil32 endpoint` by
        simp[word_size_def, ceil32_div_mul] >>
      `endpoint <= venomLayout$ceil32 endpoint` by simp[ceil32_ge] >>
      `2 ** 64 < memory_cost endpoint` by
        simp[memory_cost_ge_2_64] >>
      `2 ** 64 < memory_cost (venomLayout$ceil32 endpoint)` by
        (irule memory_cost_ge_2_64 >> decide_tac) >>
      `buffer_length c.memory <= venomLayout$ceil32 endpoint` by
        decide_tac >>
      simp[memory_expansion_cost_def, MAX_DEF] >> decide_tac) >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_assum `fmp_room ctx func s` (mp_tac o REWRITE_RULE [fmp_room_def]) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `s.vs_initial_fmp = fmp` (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `n = LENGTH s.vs_call_ctx.cc_calldata` >>
  qabbrev_tac `rounded = venomLayout$ceil32 n` >>
  `rounded <= 2 ** 64` by
    (unabbrev_all_tac >> irule dalloca_calldata_size_bound >> simp[]) >>
  `w2n s.vs_fmp + rounded < dimword (:256)` by
    (fs[dimword_def, dimindex_256] >> decide_tac) >>
  asm_simp_tac std_ss [] >> conj_tac
  >- (`rounded <= n + 31` by
        (simp[Abbr `rounded`, ceil32_def] >>
         `n MOD 32 < 32` by simp[] >> decide_tac) >>
      `w2n (s.vs_fmp + n2w rounded) = w2n s.vs_fmp + rounded` by
        simp[w2n_add_2] >>
      qabbrev_tac `written =
        write_memory_with_expansion (w2n s.vs_fmp)
          s.vs_call_ctx.cc_calldata s` >>
      `w2n s.vs_fmp + rounded <= LENGTH written.vs_memory + 31` by
        (simp[Abbr `written`, LENGTH_write_memory_with_expansion, MAX_DEF] >>
         fs[Abbr `n`] >> decide_tac) >>
      `written.vs_alloca_next = s.vs_alloca_next /\
       written.vs_allocas = s.vs_allocas /\
       written.vs_initial_fmp = s.vs_initial_fmp` by
        simp[Abbr `written`, write_memory_with_expansion_def] >>
      simp[fmp_room_def, pending_alloca_size_def, MAX_DEF] >>
      fs[pending_alloca_size_def] >> decide_tac) >>
  strip_tac >> drule_all fmp_frontier_rel_dalloca >> simp[]
QED

(* The copy starts at or above every live local and constructor immutable.
   This frame keeps the register file, so the reserved-name check can be
   applied separately to the gadget's two result registers. *)
Theorem calldata_copy_stmt_frame[local]:
  stmt_state_rel H ctx func cenv cx vy s /\
  s.vs_alloca_next <= w2n s.vs_fmp /\
  fmp_room ctx func
    ((write_memory_with_expansion (w2n s.vs_fmp) bytes s) with vs_fmp := fmp) ==>
  stmt_state_rel H ctx func cenv cx vy
    ((write_memory_with_expansion (w2n s.vs_fmp) bytes s) with vs_fmp := fmp)
Proof
  strip_tac >>
  qabbrev_tac `t =
    (write_memory_with_expansion (w2n s.vs_fmp) bytes s) with vs_fmp := fmp` >>
  drule stmt_state_rel_state_rel >> strip_tac >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   (!x. lookup_var x t = lookup_var x s)` by
    simp[Abbr `t`, write_memory_with_expansion_def, lookup_var_def] >>
  `local_ptrs_rel func cenv vy.scopes t` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     rpt conj_tac >~ [`mem_bytes_at _ _ _ = mem_bytes_at _ _ _`]
     >- (rpt strip_tac >>
         `regions_disjoint b sz (w2n s.vs_fmp) (LENGTH bytes)` by
           (irule local_ptrs_rel_above_frontier >>
            qexistsl_tac [`cenv`, `func`, `name`, `vy.scopes`, `s`] >> simp[]) >>
         simp[Abbr `t`] >> sym_tac >>
         irule write_memory_mem_bytes_at_disjoint >> fs[regions_disjoint_def]) >>
     rpt strip_tac >> gvs[]) >>
  `!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
         immutables_rel cenv cx.txn.target src cenv.ce_is_ctor vy t` by
    (gen_tac >> disch_tac >>
     `immutable_alloca_sep func (cenv with ce_module := src) cx vy s` by
       (Cases_on `src = cenv.ce_module` >>
        fs[stmt_state_rel_def, optionTheory.IS_SOME_EXISTS,
           compile_env_component_equality] >> metis_tac[]) >>
     irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor vy s` by
       (fs[state_rel_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
     simp[Abbr `t`, write_memory_with_expansion_nondecreasing] >>
     conj_tac >- simp[write_memory_with_expansion_def] >>
     rpt strip_tac >> irule write_memory_mem_bytes_at_disjoint >> disj1_tac >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def]) >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >> strip_tac >>
     qpat_x_assum `!name tv v off. _ ==> _` drule_all >> strip_tac >> decide_tac) >>
  `!ce. immutable_alloca_sep func ce cx vy s ==>
        immutable_alloca_sep func ce cx vy t` by
    (rpt strip_tac >> irule immutable_alloca_sep_fields >>
     qexistsl_tac [`s`, `vy`] >> simp[] >> rpt strip_tac >>
     qexists_tac `id` >> fs[local_region_def] >> metis_tac[]) >>
  match_mp_tac stmt_state_rel_intro >> conj_tac
  >- (irule state_rel_frame >> simp[] >> qexistsl_tac [`vy`, `s`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp[Abbr `t`, write_memory_with_expansion_def]) >>
  conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac >- (irule alloca_room_fields >> qexists_tac `s` >>
               simp[] >> metis_tac[stmt_state_rel_alloca_room]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (first_x_assum irule >> fs[stmt_state_rel_def]) >>
  conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
      simp[Abbr `t`, write_memory_with_expansion_def] >>
      metis_tac[stmt_state_rel_immutable_base_zero]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  drule stmt_state_rel_alloca_size >> simp[]
QED

val raw_bridge = SIMP_RULE bool_ss []
  (Q.INST [`fmp` |-> `s.vs_initial_fmp`]
    (CONJUNCT2 (SPEC_ALL raw_call_msg_data_peak_memory_oog_bridge)));

Theorem compile_msg_data_to_memory_peak_memory_consumer:
  !H ctx func cenv cx vy
   (sa:compile_state) (ptr:operand) (len:operand) (sb:compile_state)
   (s:venom_state).
    compile_msg_data_to_memory sa = ((ptr, len), sb) /\
    fn_has_code sa sb func /\
    stmt_state_rel H ctx func cenv cx vy s /\
    local_ptrs_reserved cenv sa /\
    LENGTH s.vs_call_ctx.cc_calldata < 2 ** 64 /\
    (w2n s.vs_fmp <= w2n s.vs_initial_fmp + 2 ** 64 * 2 ** 64 \/
     w2n s.vs_fmp +
       venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
       dimword (:256)) ==>
    ?t.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel H ctx func cenv cx vy t /\
      eval_operand ptr t = SOME s.vs_fmp /\
      eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
      w2n s.vs_fmp +
        venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
        dimword (:256) /\
      t.vs_fmp =
        s.vs_fmp +
        n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata)) /\
      t.vs_memory =
        (write_memory_with_expansion (w2n s.vs_fmp)
          s.vs_call_ctx.cc_calldata s).vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!(cp_fmp:num) (lo:num).
         fmp_frontier_rel cp_fmp (w2n s.vs_initial_fmp) lo s.vs_fmp ==>
         lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
           dimword (:256) /\
         fmp_frontier_rel cp_fmp (w2n s.vs_initial_fmp)
           (lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))
           t.vs_fmp)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)` by
    (drule msg_data_to_memory_dalloca >> strip_tac >>
     simp[EXISTS_MEM] >> qexists_tac `i` >> simp[] >>
     qspecl_then [`sa`, `sm`, `sb`, `func`, `i`] mp_tac
       fn_has_code_current_inst >> simp[]) >>
  `fmp_room ctx func s` by fs[stmt_state_rel_def] >>
  `s.vs_alloca_next <= w2n s.vs_fmp` by
    (qpat_assum `fmp_room ctx func s` (mp_tac o REWRITE_RULE [fmp_room_def]) >>
     impl_tac >- (disj2_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >> decide_tac) >>
  `w2n s.vs_fmp + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
     dimword (:256) /\
   fmp_room ctx func
     ((write_memory_with_expansion (w2n s.vs_fmp)
        s.vs_call_ctx.cc_calldata s) with
      vs_fmp := s.vs_fmp +
        n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))) /\
   (!cp_fmp lo.
     fmp_frontier_rel cp_fmp (w2n s.vs_initial_fmp) lo s.vs_fmp ==>
     lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) <
       dimword (:256) /\
     fmp_frontier_rel cp_fmp (w2n s.vs_initial_fmp)
       (lo + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))
       (s.vs_fmp + n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))))` by
    (conj_tac >- (mp_tac raw_bridge >> simp[]) >>
     conj_tac >- (mp_tac raw_bridge >> simp[]) >>
     rpt gen_tac >> mp_tac raw_bridge >> simp[]) >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by
    (fs[dimword_def, dimindex_256] >> decide_tac) >>
  drule_all calldata_memory_run >> strip_tac >> qexists_tac `t` >>
  asm_simp_tac std_ss [] >> conj_tac
  >- (qabbrev_tac `copied =
        (write_memory_with_expansion (w2n s.vs_fmp)
           s.vs_call_ctx.cc_calldata s) with
        vs_fmp := s.vs_fmp +
          n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))` >>
      `stmt_state_rel H ctx func cenv cx vy copied` by
        (simp[Abbr `copied`] >> irule calldata_copy_stmt_frame >> simp[]) >>
      `t = copied with vs_vars := t.vs_vars` by
        (qpat_assum `t = s with <|vs_vars := _; vs_memory := _; vs_fmp := _|>` (fn th => simp[Once th]) >>
         simp[venom_state_component_equality, Abbr `copied`,
              write_memory_with_expansion_def]) >>
      qpat_assum `t = copied with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      irule stmt_state_rel_vars_frame >> simp[] >>
      `!x. not_fresh_at sa x ==>
        lookup_var x (copied with vs_vars := t.vs_vars) = lookup_var x copied` by
        (gen_tac >> disch_tac >>
         qpat_assum `t = copied with vs_vars := _` (fn th => rewrite_tac[Once (GSYM th)]) >>
         simp[Abbr `copied`, lookup_var_def, write_memory_with_expansion_def] >>
         fs[lookup_var_def]) >>
      fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!cp lo. fmp_frontier_rel _ _ _ _ ==> _` drule >> simp[]
QED
