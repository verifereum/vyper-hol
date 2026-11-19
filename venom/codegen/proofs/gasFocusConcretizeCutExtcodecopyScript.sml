Theory gasFocusConcretizeCutExtcodecopy
Ancestors concretizePtrExtcodecopyFamily[qualified]
  gasFocusConcretizeTaggedSupport concretizePtrPrefixWriteAttach
  concretizePtrRequestHistory concretizePtrReturnTransport
  concretizePtrValueTransport concretizePtrOrdinaryNext concretizePtrOpaqueRetpc
  venomExecSemantics venomExecProofs venomInst venomState vfmState words list
  concretizePtrTaggedSupport concretizePtrTaintContent
  concretizePtrBufferCopyContent
  concretizePtrLedgerProbe concretizePtrParamSupport
  ptrDiscipline pointerConfinedDefs memLocDefs finite_map
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrDeletedGapHistory
  concretizePtrComparisonTransport concretizePtrPrefixLedger concretizePtrBytes
  concretizePtrActivationChronology concretizeStepStructure concretizePtrSourceOwnership
  cfgWf venomWf codegenRel contextCodegenRel unitLabelMapIdentity option arithmetic

Theorem ptr_focus_extcodecopy_execute[local]:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [a;d;r;n] /\
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  EVERY (ptr_nonopaque_operand f) [a;d;r;n] /\
  EVERY (\op. op_prov TG op = NONE /\ op_taint tn op = {}) [a;r;n] /\
  step_inst fuel Ct inst t = OK postt ==>
  ?dst dt sz bytes post.
    eval_operand d s = SOME dst /\ eval_operand d t = SOME dt /\
    eval_operand n s = SOME sz /\ eval_operand n t = SOME sz /\
    (?addr. eval_operand a s = SOME addr /\ eval_operand a t = SOME addr) /\
    (?src. eval_operand r s = SOME src /\ eval_operand r t = SOME src) /\
    LENGTH bytes = w2n sz /\
    step_inst 0 C inst s = OK post /\
    post = write_memory_with_expansion (w2n dst) bytes s /\
    postt = write_memory_with_expansion (w2n dt) bytes t /\
    (!i. i < w2n sz ==>
      read_byte (w2n dst + i) post.vs_memory =
      read_byte (w2n dt + i) postt.vs_memory)
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `eval_operands [a;r;n] s = eval_operands [a;r;n] t` by
    (irule ptr_mixed_scalar_operands_equal >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all concretizePtrExtcodecopyFamilyTheory.ptr_extcodecopy_success >> strip_tac >>
  qpat_x_assum `step_inst fuel Ct inst t = OK postt` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG d) (op_taint tn d)
    (eval_operand d s) (eval_operand d t)` by
    (irule ptr_mixed_vars_eval >>
     rpt (goal_assum (drule_at Any)) >> fs[]) >>
  gvs[ptr_lookup_transport_some_right, eval_operands_def, AllCaseEqs()] >>
  qexists_tac `TAKE (w2n sz) (DROP (w2n src)
      (lookup_account (w2w addr) t.vs_accounts).code ++ REPLICATE (w2n sz) 0w)` >>
  simp[LENGTH_TAKE] >>
  `!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code` by
    metis_tac[concretizePtrExtcodecopyFamilyTheory.ptr_extcodecopy_account_code] >>
  simp[] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >> simp[LENGTH_TAKE]
QED

Theorem ptr_focus_extcodecopy_operands[local]:
  fn_ptr_ok P f /\ ptr_static_support P f TG /\ opaque_use_ok f /\
  MEM inst (fn_insts f) /\ taint_ok f tn inst s /\
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [a;d;r;n] ==>
  EVERY (ptr_nonopaque_operand f) [a;d;r;n] /\
  EVERY (\op. op_prov TG op = NONE /\ op_taint tn op = {}) [a;r;n]
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand f) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `EVERY (\op. op_taint tn op = {}) inst.inst_operands` by
    (fs[taint_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `!v. MEM (Var v) [a;r;n] ==> v NOTIN fn_pv P f` by
    (`ptr_use_ok P (fn_pv P f) inst` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
     strip_tac >> gen_tac >> disch_tac >> disch_tac >>
     first_x_assum (qspec_then `v` mp_tac) >>
     Cases_on `a = Var v` >> Cases_on `d = Var v` >>
     Cases_on `r = Var v` >> Cases_on `n = Var v` >> fs[]) >>
  `EVERY (\op. op_prov TG op = NONE) [a;r;n]` by
    (pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
     Cases_on `op` >> simp[op_prov_def] >>
     Cases_on `FLOOKUP TG s'` >> simp[] >>
     metis_tac[ptr_static_support_def]) >>
  gvs[]
QED

Theorem ptr_focus_extcodecopy_post[local]:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_outputs = [] /\
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t ==>
  ptr_mixed_vars births positions TG
    (step_taint inst s (write_memory_with_expansion dst bytes s) tn) f g
    (write_memory_with_expansion dst bytes s with vs_inst_idx := k)
    (write_memory_with_expansion dt bytes t with vs_inst_idx := kt) /\
  ptr_history_content
    (step_taint inst s (write_memory_with_expansion dst bytes s) tn)
    (write_memory_with_expansion dst bytes s with vs_inst_idx := k)
    (write_memory_with_expansion dt bytes t with vs_inst_idx := kt)
Proof
  strip_tac >> reverse conj_tac
  >- (simp[write_memory_with_expansion_def] >>
      irule ptr_history_content_masks >> qexists `tn` >>
      simp[step_taint_def, set_var_taint_def, adopt_reset_def,
           store_taint_def, imm_taint_def]) >>
  irule ptr_mixed_vars_fields >>
  rpt (goal_assum (drule_at Any)) >>
  simp[write_memory_with_expansion_def, step_taint_def, set_var_taint_def,
       finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem ptr_focus_extcodecopy_edge[local]:
  ptr_chrono_step C' at zt /\ at.po_inst.inst_opcode = EXTCODECOPY ==>
  ?fuel postt. step_inst fuel C' at.po_inst at.po_state = OK postt /\
    zt.po_state = (postt with vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
    zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
    zt.po_params = at.po_params /\ active_inst zt.po_fn zt.po_inst zt.po_state
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac >> gvs[]
  >- metis_tac[] >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
QED

Theorem ptr_focus_extcodecopy_certificate[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_chrono_step C a b /\ ptr_chrono_step C' at zt /\
  a.po_inst.inst_opcode = EXTCODECOPY /\ at.po_inst = a.po_inst /\
  (!x. x IN range_bytes (step_writes a.po_inst a.po_state b.po_state) <=>
    w2n (dst:256 word) <= x /\ x < w2n dst + w2n (sz:256 word)) /\
  (!x. x IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
    w2n (dt:256 word) <= x /\ x < w2n dt + w2n sz) /\
  (!i. i < w2n sz ==> read_byte (w2n dst+i) b.po_state.vs_memory =
    read_byte (w2n dt+i) zt.po_state.vs_memory) /\
  range_bytes (step_writes a.po_inst a.po_state b.po_state) <> {} /\
  (dst = dt /\ (w2n dst + w2n sz <= lo \/ dyn_floor C a.po_state <= w2n dst) \/
   (?token bid db sb pb. MEM token tokens /\
     FLOOKUP births (token,bid) = SOME (db,sb) /\
     FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\
     db <= w2n dst /\ w2n dst + w2n sz <= db + sb /\
     w2n dt = pb + (w2n dst - db))) ==>
  ?rho. ptr_paired_write lo positions C C' (h ++ [b]) (ht ++ [zt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
    (LENGTH h - 1,LENGTH done,rho)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  `0 < LENGTH h /\ LAST h = a /\ LAST ht = at /\
   LENGTH ht = SUC (LENGTH done) /\ LENGTH H = LENGTH h` by
    (drule_all ptr_chrono_history_end >> strip_tac >>
     imp_res_tac ptr_chrono_history_end >>
     fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def]) >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH done) ht = at` by
    (`h <> [] /\ ht <> []` by (Cases_on `h` >> Cases_on `ht` >> gvs[]) >>
     fs[LAST_EL, PRE_SUB1]) >>
  `LENGTH h - 1 < LENGTH h /\ LENGTH done < LENGTH ht /\
   SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  qpat_x_assum `_ \/ (?token bid db sb pb. _)`
    (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC)
       STRIP_ASSUME_TAC)
  >- (qexists `\x:num. x` >>
      simp[ptr_paired_write_def, EL_APPEND_EQN, ptr_ledger_write_pair_def,
           ptr_paired_write_owner_def, is_terminator_def, ptr_bytes_agree_def] >>
      conj_tac >- (rpt strip_tac >>
                   `x - w2n dst < w2n sz /\ w2n dst + (x-w2n dst) = x` by decide_tac >>
                   metis_tac[]) >>
      rpt strip_tac >>
      `x < lo \/ dyn_floor C a.po_state <= x` by decide_tac >> simp[]) >>
  qexists `\x:num. pb + (x-db)` >>
  simp[ptr_paired_write_def, EL_APPEND_EQN, ptr_ledger_write_pair_def,
       ptr_paired_write_owner_def, is_terminator_def, ptr_bytes_agree_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (gvs[] >> decide_tac)
  >- (`x-w2n dst < w2n sz /\ w2n dst + (x-w2n dst) = x /\
       w2n dt + (x-w2n dst) = pb + x - db` by decide_tac >> metis_tac[]) >>
  disj2_tac >> disj1_tac >> qexistsl [`token`,`bid`,`db`,`sb`,`pb`,`x-db`] >>
  simp[] >> decide_tac
QED

(* The bounded history supplies only the geometry of the actual write.
   Both executions and the number of bytes written come from the target edge. *)
Theorem ptr_focus_extcodecopy_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  EVERY (\f. fn_inst_wf f /\ opaque_use_ok f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  a.po_inst.inst_opcode = EXTCODECOPY /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\
  (!ops x y n.
    mem_write_ops a.po_inst = SOME ops /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,n) (source_memory_write_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y) /\ 0 < n ==>
    (x = y /\ (w2n x+n <= lo \/ dyn_floor C a.po_state <= w2n x)) \/
    (?token aid b sz pa. MEM token tokens /\
      FLOOKUP births (token,aid) = SOME (b,sz) /\
      FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
      b <= w2n x /\ w2n x+n <= b+sz /\ w2n y = pa + (w2n x-b))) ==>
  ?z ws'. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls ws'
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def, Once frame_reachable_cases] >>
     rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `inst_wf a.po_inst /\ fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn) /\
   (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
     ?p. FLOOKUP (lp a.po_fn) (Allocation i.inst_id) = SOME p)` by
    (fs[EVERY_MEM, IS_SOME_EXISTS] >> metis_tac[]) >>
  `?aop dop rop nop. a.po_inst.inst_operands = [aop;dop;rop;nop] /\
    a.po_inst.inst_outputs = []` by
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `at.po_inst = a.po_inst /\ ~is_terminator a.po_inst.inst_opcode /\
   a.po_inst.inst_opcode <> NOP /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[concretize_positions_unchanged, is_terminator_def] >>
  drule_all ptr_focus_extcodecopy_operands >> strip_tac >>
  `at.po_inst.inst_opcode = EXTCODECOPY` by simp[] >>
  drule_all ptr_focus_extcodecopy_edge >> strip_tac >>
  suspend "execute"
QED

Resume ptr_focus_extcodecopy_step[execute]:
  qpat_assum `ptr_paired_sample _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_paired_sample_def] >> strip_tac >>
  `step_inst fuel C' a.po_inst at.po_state = OK postt` by metis_tac[] >>
  `?dst dt sz bytes post.
    eval_operand dop a.po_state = SOME dst /\ eval_operand dop at.po_state = SOME dt /\
    eval_operand nop a.po_state = SOME sz /\ eval_operand nop at.po_state = SOME sz /\
    (?addr. eval_operand aop a.po_state = SOME addr /\ eval_operand aop at.po_state = SOME addr) /\
    (?src. eval_operand rop a.po_state = SOME src /\ eval_operand rop at.po_state = SOME src) /\
    LENGTH bytes = w2n sz /\ step_inst 0 C a.po_inst a.po_state = OK post /\
    post = write_memory_with_expansion (w2n dst) bytes a.po_state /\
    zt.po_state = (write_memory_with_expansion (w2n dt) bytes at.po_state
      with vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
    (!i. i < w2n sz ==>
      read_byte (w2n dst+i) post.vs_memory = read_byte (w2n dt+i) zt.po_state.vs_memory)` by
    (drule_all ptr_focus_extcodecopy_execute >>
     disch_then (qspec_then `C` strip_assume_tac) >>
     fs[] >> metis_tac[]) >>
  qpat_x_assum `zt.po_state = postt with vs_inst_idx := _` kall_tac >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >> simp[write_memory_with_expansion_def] >>
     qexists `a.po_inst` >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `z.po_fn = a.po_fn /\ z.po_stack = a.po_stack /\ z.po_params = a.po_params /\
   z.po_state = post with vs_inst_idx := SUC a.po_state.vs_inst_idx` by
    simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  suspend "attach"
QED

Resume ptr_focus_extcodecopy_step[attach]:
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    (`ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG` by
       simp[ptr_tagged_step_def, step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
     drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
        a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]) >>
  `ptr_chrono_step C a z` by metis_tac[ptr_tagged_chrono_step_projection] >>
  `ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
    (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)])` by
    (drule ptr_ownership_overlay_fixed >> strip_tac >>
     drule (cj 3 ptr_structural_transcript_rules) >>
     disch_then drule >> disch_then drule >>
     simp[ptr_activation_tokens_def, ptr_activation_registry_def,
          write_memory_with_expansion_def]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >>
     metis_tac[fn_labels_def, concretize_positions_labels]) >>
  `ptr_paired_cursor lp z zt` by
    (irule ptr_ordinary_next_cursor >> rpt conj_tac
     >- (simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
         metis_tac[])
     >- (first_assum ACCEPT_TAC) >>
     qexistsl [`a`,`at`] >> simp[write_memory_with_expansion_def]) >>
  `ptr_paired_sample positions z zt (tokens,registry,births,PT,TG,saved,entries)` by
    (drule_all ptr_focus_extcodecopy_post >>
     disch_then (qspecl_then [`SUC at.po_state.vs_inst_idx`,
       `SUC a.po_state.vs_inst_idx`,`w2n dt`,`w2n dst`,`bytes`] mp_tac) >>
     simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  `ptr_paired_params positions z zt (tokens,registry,births,PT,TG,saved,entries)` by
    fs[ptr_paired_params_def, write_memory_with_expansion_def] >>
  suspend "write"
QED

Resume ptr_focus_extcodecopy_step[write]:
  `(!x. x IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
    w2n dst <= x /\ x < w2n dst + w2n sz) /\
   (!x. x IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
    w2n dt <= x /\ x < w2n dt + w2n sz)` by
    simp[step_writes_def, source_memory_write_ranges_def,
         sized_source_write_range_def, range_bytes_def] >>
  Cases_on `sz = 0w`
  >- (`range_bytes (step_writes a.po_inst a.po_state z.po_state) = {}` by
        simp[pred_setTheory.EXTENSION] >>
      qexistsl [`z`,`ws ++ []`] >> MATCH_MP_TAC ptr_paired_prefix_write_attach >> simp[]) >>
  `op_taint a.po_taint dop = {}` by
    (fs[taint_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `ptr_lookup_transport births positions (op_prov TG dop) {} (SOME dst) (SOME dt)` by
    (`ptr_lookup_transport births positions (op_prov TG dop) (op_taint a.po_taint dop)
       (eval_operand dop a.po_state) (eval_operand dop at.po_state)` suffices_by simp[] >>
     irule ptr_mixed_vars_eval >> conj_tac
     >- metis_tac[ptr_history_content_labels] >>
     qexistsl [`a.po_fn`,`at.po_fn`] >> fs[]) >>
  `0 < w2n sz` by simp[GSYM NOT_ZERO_LT_ZERO] >>
  qpat_assum `!ops x y n. mem_write_ops _ = _ /\ _ ==> _`
    (qspecl_then [`<|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>`,
                   `dst`,`dt`,`w2n sz`] mp_tac) >>
  (impl_tac >- simp[mem_write_ops_def, source_memory_write_ranges_def,
                    sized_source_write_range_def, w2n_eq_0]) >>
  disch_tac >>
  `range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {}` by
    (simp[pred_setTheory.EXTENSION] >> qexists `w2n dst` >> simp[w2n_eq_0]) >>
  `!j. j < w2n sz ==> read_byte (w2n dst+j) z.po_state.vs_memory =
                      read_byte (w2n dt+j) zt.po_state.vs_memory` by
    (`z.po_state.vs_memory = post.vs_memory` by simp[] >>
     qpat_assum `z.po_state.vs_memory = post.vs_memory` SUBST1_TAC >>
     qpat_assum `!i. i < w2n sz ==> read_byte _ post.vs_memory = _`
       MATCH_ACCEPT_TAC) >>
  drule_all ptr_focus_extcodecopy_certificate >>
  disch_then (qx_choose_then `rho_write:num -> num` assume_tac) >>
  qexistsl [`z`,`ws ++ [(LENGTH h - 1,LENGTH done,rho_write)]`] >>
  MATCH_MP_TAC ptr_paired_prefix_write_attach >> simp[]
QED

Finalise ptr_focus_extcodecopy_step
