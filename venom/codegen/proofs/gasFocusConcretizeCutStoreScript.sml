Theory gasFocusConcretizeCutStore
Ancestors
  concretizePtrPrefixWriteAttach concretizePtrOrdinaryNext
  concretizePtrByteStoreFamily concretizePtrWriteFootprint
  concretizePtrPairedPrefix concretizePtrRequestHistory
  concretizePtrOpaqueRetpc concretizePtrValueTransport
  concretizePtrHistoricalWriteClassification gasFocusConcretizeTaggedSupport
  concretizeMemLocDefs concretizePtrChronologicalHistory
  concretizePtrSourceOwnership concretizePtrWritePurity concretizeStepStructure
  concretizePtrLedgerProbe concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory concretizePtrActivationChronology
  concretizePtrPairedFields concretizePtrPrefixLedger concretizePtrComparisonTransport
  codegenRel memLocDefs ptrDiscipline finite_map pred_set words concretizePtrStoreSteps
  venomExecSemantics venomInst venomState opcodeClass list
  concretizePtrParamSupport o1PassContract unitShapeDefs venomWf
  contextCodegenRel unitLabelMapIdentity
  ptrDisciplineEmptyTaint concretizePtrPlacementBounds concretizePtrStagePlacements

(* Instructions in this family are unchanged by Concretize: it is the
   sampled operands, not the text of the store, that may relocate. *)
Theorem ptr_focus_store_text[local]:
  MEM inst.inst_opcode [MSTORE; MSTORE8; ISTORE] ==>
  concretize_inst_with_positions p inst = inst
Proof
  simp[listTheory.MEM] >> strip_tac >> simp[concretize_inst_with_positions_def]
QED

Theorem ptr_focus_store_ok[local]:
  MEM inst.inst_opcode [MSTORE; MSTORE8; ISTORE] ==>
  (step_inst fuel C inst s = OK post <=>
   ?d v x y. inst.inst_operands = [d; v] /\
     eval_operand d s = SOME x /\ eval_operand v s = SOME y /\
     post = (if inst.inst_opcode = MSTORE then mstore (w2n x) y s
             else if inst.inst_opcode = MSTORE8 then mstore8 (w2n x) y s
             else istore (w2n x) y s))
Proof
  simp[listTheory.MEM] >> strip_tac >>
  simp[step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_write2_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ptr_focus_store_edge[local]:
  MEM a.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  ptr_chrono_step C a b ==>
  ?d v x y. a.po_inst.inst_operands = [d; v] /\
    eval_operand d a.po_state = SOME x /\ eval_operand v a.po_state = SOME y /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
    b.po_state = ((if a.po_inst.inst_opcode = MSTORE then mstore (w2n x) y a.po_state
                   else if a.po_inst.inst_opcode = MSTORE8 then mstore8 (w2n x) y a.po_state
                   else istore (w2n x) y a.po_state)
                  with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
    active_inst b.po_fn b.po_inst b.po_state
Proof
  strip_tac >>
  `!fuel rs rv. step_inst fuel C a.po_inst a.po_state <> IntRet rs rv` by
    (qpat_x_assum `MEM a.po_inst.inst_opcode _` mp_tac >>
     simp[listTheory.MEM] >> strip_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
          AllCaseEqs()]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[listTheory.MEM, is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[ptr_focus_store_ok] >> metis_tac[]
QED

Theorem ptr_focus_store_footprint[local]:
  MEM inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  inst.inst_operands = [d; v] /\
  eval_operand d s = SOME x /\ eval_operand v s = SOME y ==>
  !len. len = (if inst.inst_opcode = MSTORE8 then 1 else 32) ==>
    source_memory_write_ranges inst s = [(w2n x,len)] /\
    step_writes inst s post = [(w2n x,len)] /\
    mem_write_ops inst = SOME <|iao_ofst := d; iao_size := SOME (Lit (n2w len));
                               iao_max_size := SOME (Lit (n2w len))|>
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  simp[listTheory.MEM] >> strip_tac >>
  simp[source_memory_write_ranges_def, fixed_source_write_range_def,
       step_writes_def, mem_write_ops_def]
QED

Theorem ptr_focus_store_operand_facts[local]:
  MEM inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  inst.inst_operands = [d; v] /\ taint_ok f tn inst s /\
  fn_ptr_ok P f /\ MEM inst (fn_insts f) /\
  (!x. x IN FDOM TG ==> x IN fn_pv P f) ==>
  op_taint tn d = {} /\ op_prov TG v = NONE /\
  (inst.inst_opcode = ISTORE ==> op_prov TG d = NONE) /\
  (inst.inst_opcode = MSTORE8 ==> op_taint tn v = {})
Proof
  simp[listTheory.MEM] >> strip_tac >>
  `op_taint tn d = {}` by
    (spose_not_then assume_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  simp[] >>
  metis_tac[listTheory.MEM, ptr_mstore_value_no_provenance,
            ptr_byte_store_istore_operands_no_provenance,
            ptr_byte_store_mstore8_value_no_provenance,
            ptr_byte_store_mstore8_operands_untainted]
QED

Theorem ptr_focus_store_post_fields[local]:
  MEM inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  step_inst fuel C inst s = OK post /\ inst.inst_outputs = [] ==>
  post.vs_current_bb = s.vs_current_bb /\ post.vs_prev_bb = s.vs_prev_bb /\
  post.vs_vars = s.vs_vars /\ post.vs_params = s.vs_params /\
  post.vs_allocas = s.vs_allocas /\ post.vs_return_pc_token = s.vs_return_pc_token /\
  (step_taint inst s post tn).t_var = tn.t_var /\
  ptr_tagged_step token PT TG inst post = TG
Proof
  strip_tac >> drule_all ptr_focus_store_ok >>
  simp[listTheory.MEM] >> rpt strip_tac >>
  gvs[mstore_def, mstore8_def, istore_def, ptr_tagged_step_def, step_prov_def,
      set_prov_def, step_taint_def, set_var_taint_def, store_taint_def,
      adopt_reset_def, DRESTRICT_UNIV]
QED

Theorem ptr_focus_store_operand[local]:
  ptr_paired_sample positions a at (tokens,registry,births,PT,TG,saved,entries) /\
  ptr_nonopaque_operand a.po_fn op /\ eval_operand op at.po_state = SOME xt ==>
  ?x. eval_operand op a.po_state = SOME x /\
      ptr_value_transport births positions (op_prov TG op) (op_taint a.po_taint op) x xt
Proof
  strip_tac >> gvs[ptr_paired_sample_def] >>
  drule ptr_history_content_labels >> strip_tac >>
  drule_all ptr_mixed_vars_eval >> simp[ptr_lookup_transport_some_right]
QED

Theorem ptr_focus_store_execute[local]:
  ptr_paired_sample positions a at (tokens,registry,births,PT,TG,saved,entries) /\
  MEM a.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands /\
  ptr_chrono_step C' at zt ==>
  ?d v x y xt yt post postt.
    at.po_inst = a.po_inst /\ a.po_inst.inst_operands = [d;v] /\
    eval_operand d a.po_state = SOME x /\ eval_operand v a.po_state = SOME y /\
    eval_operand d at.po_state = SOME xt /\ eval_operand v at.po_state = SOME yt /\
    ptr_value_transport births positions (op_prov TG d) (op_taint a.po_taint d) x xt /\
    ptr_value_transport births positions (op_prov TG v) (op_taint a.po_taint v) y yt /\
    post = (if a.po_inst.inst_opcode = MSTORE then mstore (w2n x) y a.po_state
            else if a.po_inst.inst_opcode = MSTORE8 then mstore8 (w2n x) y a.po_state
            else istore (w2n x) y a.po_state) /\
    postt = (if a.po_inst.inst_opcode = MSTORE then mstore (w2n xt) yt at.po_state
             else if a.po_inst.inst_opcode = MSTORE8 then mstore8 (w2n xt) yt at.po_state
             else istore (w2n xt) yt at.po_state) /\
    step_inst 0 C a.po_inst a.po_state = OK post /\
    step_inst 0 C' at.po_inst at.po_state = OK postt /\
    zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
    zt.po_state = postt with vs_inst_idx := SUC at.po_state.vs_inst_idx /\
    active_inst zt.po_fn zt.po_inst zt.po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `at.po_inst = a.po_inst` by simp[ptr_focus_store_text] >>
  `MEM at.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE]` by fs[] >>
  drule_all ptr_focus_store_edge >>
  disch_then (qx_choose_then `d` (qx_choose_then `v`
    (qx_choose_then `xt` (qx_choose_then `yt` strip_assume_tac)))) >>
  `a.po_inst.inst_operands = [d;v]` by metis_tac[] >>
  `ptr_nonopaque_operand a.po_fn d /\ ptr_nonopaque_operand a.po_fn v` by fs[] >>
  `?x. eval_operand d a.po_state = SOME x /\
       ptr_value_transport births positions (op_prov TG d) (op_taint a.po_taint d) x xt` by
    (irule ptr_focus_store_operand >> simp[] >> metis_tac[]) >>
  `?y. eval_operand v a.po_state = SOME y /\
       ptr_value_transport births positions (op_prov TG v) (op_taint a.po_taint v) y yt` by
    (irule ptr_focus_store_operand >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`d`,`v`,`x`,`y`,`xt`,`yt`] >>
  simp[ptr_focus_store_ok] >> metis_tac[]
QED

Theorem ptr_focus_store_next[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  active_inst a.po_fn a.po_inst a.po_state /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  MEM a.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  a.po_inst.inst_outputs = [] /\
  step_inst 0 C a.po_inst a.po_state = OK post /\ ptr_chrono_step C' at zt /\
  at.po_inst = a.po_inst /\ zt.po_stack = at.po_stack ==>
  ?i z. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
        z = ptr_ledger_next a i post /\
        ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
        ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
          (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
          (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    fs[listTheory.MEM, is_terminator_def] >>
  drule_all ptr_focus_store_post_fields >>
  disch_then (qspecl_then [`HD tokens`,`a.po_taint`,`TG`,`PT`] strip_assume_tac) >>
  drule_all ptr_ordinary_next_active >> strip_tac >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    (drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
         a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]) >>
  `z.po_stack = a.po_stack /\ z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  qexistsl_tac [`i`,`z`] >> conj_tac >- simp[] >>
  conj_tac >- simp[Abbr `z`] >> simp[] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_ownership_overlay_fixed >> strip_tac >>
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED

(* Numerical classification at the selected write. Erasure distinguishes
   an untagged dynamic allocation from a live static allocation. *)
Theorem ptr_focus_store_destination[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_ledger_erases (dyn_floor C a.po_state) births TG a.po_prov /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  source_memory_write_ranges a.po_inst a.po_state = [(w2n x,len)] /\ len <> 0 /\
  mem_write_ops a.po_inst = SOME ops /\ d = ops.iao_ofst /\
  ptr_value_transport births positions (op_prov TG d) {} x xt /\
  (!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
    pos + sz < dimword (:256)) ==>
  ?rho. (!k. k < len ==> rho (w2n x + k) = w2n xt + k) /\
        ptr_paired_write_owner (dyn_floor C a.po_state) lo positions rho
          (range_bytes [(w2n x,len)]) (tokens,registry,births,PT,TG,saved,entries)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lo < w2n x + len \/ op_prov a.po_prov d <> NONE ==>
     ?v b sz. d = Var v /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
             b <= w2n x /\ w2n x + len <= b + sz` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     simp[access_ok_def] >>
     disch_then (qspecl_then [`w2n x`,`len`] mp_tac o CONJUNCT1) >> simp[]) >>
  Cases_on `op_prov TG d`
  >- (`xt = x` by metis_tac[ptr_value_transport_scalar_empty] >>
      pop_assum SUBST_ALL_TAC >>
      `w2n x + len <= lo \/ dyn_floor C a.po_state <= w2n x` by
        (Cases_on `lo < len + w2n x` >-
           (`?v b sz. d = Var v /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
                b <= w2n x /\ w2n x + len <= b + sz` by
              (qpat_x_assum `_ ==> ?v b sz. _` mp_tac >> simp[]) >>
            fs[op_prov_def] >>
            `ptr_owner_erases (dyn_floor C a.po_state) births
               (FLOOKUP TG v) (FLOOKUP a.po_prov v)` by
              fs[ptr_ledger_erases_def] >>
            `dyn_floor C a.po_state <= b` by
              (pop_assum mp_tac >> simp[ptr_owner_erases_def]) >>
            metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
         fs[arithmeticTheory.NOT_LESS, arithmeticTheory.ADD_COMM]) >>
      qexists_tac `\j:num. j` >> simp[ptr_paired_write_owner_def, range_bytes_def] >>
      rpt strip_tac >> rename1 `j < len + w2n x` >>
      `j < lo \/ dyn_floor C a.po_state <= j` by decide_tac >> gs[]) >>
  rename1 `op_prov TG d = SOME tag` >> PairCases_on `tag` >>
  `?v. d = Var v` by (Cases_on `d` >> fs[op_prov_def]) >>
  `FLOOKUP TG v = SOME (tag0,tag1)` by fs[op_prov_def] >>
  `MEM tag0 tokens` by metis_tac[ptr_source_ownership_live_prov] >>
  `ptr_owner_erases (dyn_floor C a.po_state) births
      (FLOOKUP TG v) (FLOOKUP a.po_prov v)` by fs[ptr_ledger_erases_def] >>
  fs[ptr_value_transport_def, op_prov_def, ptr_owner_erases_def] >>
  rename1 `FLOOKUP births (tag0,tag1) = SOME (b,sz)` >>
  rename1 `FLOOKUP positions (Allocation tag1) = SOME (pos,sz)` >>
  `FLOOKUP a.po_prov v = SOME (b,sz)` by
    (qpat_x_assum `case FLOOKUP TG v of NONE => _ | SOME owner =>
                    FLOOKUP a.po_prov v = FLOOKUP births owner` mp_tac >> simp[]) >>
  `b <= w2n x /\ w2n x + len <= b + sz` by
    (qpat_x_assum `_ ==> ?b sz. FLOOKUP a.po_prov v = SOME (b,sz) /\ _` mp_tac >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `pos + sz < dimword (:256)` by metis_tac[] >>
  `w2n (x - n2w b + n2w pos) = pos + (w2n x - b)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists_tac `sz` >> simp[] >> decide_tac) >>
  qexists_tac `\j. pos + (j - b)` >> simp[ptr_paired_write_owner_def, range_bytes_def] >>
  rpt strip_tac >> rename1 `j < len + w2n x` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`tag0`,`tag1`,`b`,`sz`,`pos`,`j - b`] >> simp[] >> decide_tac
QED

(* The value equality required by the ledger is checked only at written,
   untainted offsets. The two footprints can have different bases. *)
Theorem ptr_focus_store_written_byte[local]:
  MEM inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  inst.inst_operands = [d;v] /\ eval_operand d s = SOME x /\
  word_agree_except (op_taint tn v) y yt /\
  (inst.inst_opcode = MSTORE8 ==> y = yt) /\
  post = (if inst.inst_opcode = MSTORE then mstore (w2n x) y s
          else if inst.inst_opcode = MSTORE8 then mstore8 (w2n x) y s
          else istore (w2n x) y s) /\
  postt = (if inst.inst_opcode = MSTORE then mstore (w2n xt) yt st
           else if inst.inst_opcode = MSTORE8 then mstore8 (w2n xt) yt st
           else istore (w2n xt) yt st) /\
  k < (if inst.inst_opcode = MSTORE8 then 1 else 32) /\
  w2n x + k NOTIN (step_taint inst s post tn).t_mem ==>
  read_byte (w2n x + k) post.vs_memory = read_byte (w2n xt + k) postt.vs_memory
Proof
  simp[listTheory.MEM] >> strip_tac >> gvs[]
  >- (`k NOTIN op_taint tn v` by
        (gvs[step_taint_def, mem_taint_def, written_taint_def] >>
         first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
      pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule ptr_mstore_written_bytes >> metis_tac[word_agree_except_def])
  >- simp[ptr_byte_store_mstore8_written_byte] >>
  `k NOTIN op_taint tn v` by
    (gvs[step_taint_def, mem_taint_def, written_taint_def] >>
     first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_mstore_written_bytes >> metis_tac[word_agree_except_def]
QED

Theorem ptr_focus_store_write_pair[local]:
  ptr_chrono_step C a z /\ ptr_chrono_step C' at zt /\
  at.po_inst = a.po_inst /\ MEM a.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  step_writes a.po_inst a.po_state z.po_state = [(src,len)] /\
  step_writes at.po_inst at.po_state zt.po_state = [(dst,len)] /\
  (!k. k < len ==> reloc (src + k) = dst + k) /\
  (!k. k < len /\ src + k NOTIN z.po_taint.t_mem ==>
    read_byte (src + k) z.po_state.vs_memory = read_byte (dst + k) zt.po_state.vs_memory) ==>
  ptr_ledger_write_pair C C' reloc a z at zt
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    fs[listTheory.MEM, is_terminator_def] >>
  simp[ptr_ledger_write_pair_def, concretizePtrBytesTheory.ptr_bytes_agree_def, range_bytes_def] >>
  conj_tac
  >- (rpt strip_tac >> rename1 `j < len + src` >>
      `j = src + (j - src) /\ j - src < len` by decide_tac >>
      qpat_x_assum `!k. k < len ==> reloc _ = _`
        (qspec_then `j - src` mp_tac) >> simp[] >> decide_tac) >>
  rpt strip_tac >> rename1 `j < len + src` >>
  `j = src + (j - src) /\ j - src < len` by decide_tac >>
  qpat_x_assum `!k. k < len ==> reloc _ = _` (qspec_then `j - src` mp_tac) >>
  qpat_x_assum `!k. _ ==> read_byte _ _ = read_byte _ _`
    (qspec_then `j - src` mp_tac) >> simp[]
QED

Theorem ptr_focus_store_history[local]:
  ptr_history_content tn s st /\ MEM inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  inst.inst_operands = [d;v] /\ eval_operand d s = SOME x /\
  word_agree_except (op_taint tn v) y yt /\
  (inst.inst_opcode = ISTORE ==> xt = x) /\
  post = (if inst.inst_opcode = MSTORE then mstore (w2n x) y s
          else if inst.inst_opcode = MSTORE8 then mstore8 (w2n x) y s
          else istore (w2n x) y s) /\
  postt = (if inst.inst_opcode = MSTORE then mstore (w2n xt) yt st
           else if inst.inst_opcode = MSTORE8 then mstore8 (w2n xt) yt st
           else istore (w2n xt) yt st) ==>
  ptr_history_content (step_taint inst s post tn) post postt
Proof
  simp[listTheory.MEM] >> strip_tac >> gvs[]
  >- (simp[mstore_def] >> irule ptr_history_content_masks >> qexists_tac `tn` >>
      simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def])
  >- (irule ptr_byte_store_mstore8_step_content >> simp[]) >>
  irule ptr_byte_store_istore_step_content >> simp[] >> metis_tac[]
QED

Theorem ptr_focus_store_write_event[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {} /\
  ptr_ledger_write_pair C C' reloc a z at zt /\
  ptr_paired_write_owner (dyn_floor C a.po_state) lo positions reloc
    (range_bytes (step_writes a.po_inst a.po_state z.po_state))
    (tokens,registry,births,PT,TG,saved,entries) ==>
  ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
    (done ++ [LENGTH h - 1]) (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
    (LENGTH h - 1,LENGTH done,reloc)
Proof
  strip_tac >> drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  imp_res_tac ptr_chrono_history_end >>
  `LENGTH ht - 1 = LENGTH done /\ SUC (LENGTH done) = LENGTH ht /\
   SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH done) ht = at` by
    metis_tac[LAST_EL, arithmeticTheory.PRE_SUB1] >>
  simp[ptr_paired_write_def, EL_APPEND_EQN]
QED

Theorem ptr_focus_store_setup[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  MEM a.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] ==>
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  dyn_floor C a.po_state = dyn_floor C vs /\
  MEM a.po_fn C.ctx_functions /\ active_inst a.po_fn a.po_inst a.po_state /\
  MEM a.po_inst (fn_insts a.po_fn) /\ a.po_inst.inst_outputs = [] /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands /\
  fn_ptr_ok P a.po_fn /\ (!x. x IN FDOM TG ==> x IN fn_pv P a.po_fn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def] >> strip_tac >>
  `dyn_floor C a.po_state = dyn_floor C vs` by
    (drule frame_reachable_initial_fmp >> simp[dyn_floor_def]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a.po_inst /\ fn_ptr_ok P a.po_fn` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_outputs = []` by gvs[listTheory.MEM, inst_wf_def] >>
  `wf_function a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[listTheory.MEM]) >>
  qpat_x_assum `MEM a.po_inst.inst_opcode _` kall_tac >>
  fs[wf_function_def, ptr_static_support_def, EVERY_MEM] >>
  conj_tac
  >- (fs[ptr_paired_code_def, fn_labels_def] >> metis_tac[concretize_positions_labels, fn_labels_def]) >>
  rpt strip_tac >>
  `?tag. FLOOKUP TG x = SOME tag` by simp[FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem ptr_focus_store_attach[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
    (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
  ptr_paired_cursor lp z zt /\ z = ptr_ledger_next a i post /\
  zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
  zt.po_state = postt with vs_inst_idx := SUC at.po_state.vs_inst_idx /\
  at.po_inst = a.po_inst /\ MEM a.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  a.po_inst.inst_outputs = [] /\
  step_inst 0 C a.po_inst a.po_state = OK post /\
  step_inst 0 C' at.po_inst at.po_state = OK postt /\
  ptr_history_content (step_taint a.po_inst a.po_state post a.po_taint) post postt /\
  ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
    (done ++ [LENGTH h - 1]) (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
    (LENGTH h - 1,LENGTH done,reloc) ==>
  ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls
    (ws ++ [(LENGTH h - 1,LENGTH done,reloc)])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `MEM at.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\ at.po_inst.inst_outputs = []` by fs[] >>
  `post.vs_vars = a.po_state.vs_vars /\ post.vs_params = a.po_state.vs_params /\
   post.vs_return_pc_token = a.po_state.vs_return_pc_token /\
   (step_taint a.po_inst a.po_state post a.po_taint).t_var = a.po_taint.t_var` by
    (qpat_x_assum `step_inst 0 C' _ _ = OK postt` kall_tac >>
     drule_all ptr_focus_store_post_fields >> simp[]) >>
  `postt.vs_vars = at.po_state.vs_vars /\ postt.vs_params = at.po_state.vs_params /\
   postt.vs_return_pc_token = at.po_state.vs_return_pc_token` by
    (qpat_x_assum `step_inst 0 C _ _ = OK post` kall_tac >>
     drule_all ptr_focus_store_post_fields >> simp[]) >>
  `z.po_fn = a.po_fn /\ z.po_stack = a.po_stack` by simp[ptr_ledger_next_def, ptr_observe_def] >>
  `ptr_paired_params positions z zt (tokens,registry,births,PT,TG,saved,entries)` by
    (fs[ptr_paired_params_def, ptr_ledger_next_def, ptr_observe_def]) >>
  `ptr_paired_sample positions z zt (tokens,registry,births,PT,TG,saved,entries)` by
    (simp[ptr_paired_sample_def, ptr_ledger_next_def, ptr_observe_def] >>
     irule ptr_mixed_vars_fields >>
     fs[ptr_paired_sample_def] >> goal_assum (drule_at Any) >> simp[]) >>
  irule ptr_paired_prefix_write_attach >> simp[] >> metis_tac[]
QED

(* The point erasure describes the live tagged provenance on this prefix;
   no invariant away from the selected source instruction is required. *)
Theorem ptr_focus_store_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  MEM a.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z reloc. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls
    (ws ++ [(LENGTH h - 1,LENGTH done,reloc)])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_focus_store_setup >> strip_tac >>
  drule ptr_paired_stage_local_allocas >> simp[] >> strip_tac >>
  drule ptr_paired_prefix_placements >> strip_tac >>
  `!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
    pos + sz < dimword (:256)` by (rpt strip_tac >> drule_all ptr_stage_placements_strict_bound >> simp[]) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule_all ptr_focus_store_execute >>
  disch_then (qspec_then `C` (qx_choose_then `d` (qx_choose_then `v`
    (qx_choose_then `x` (qx_choose_then `y`
      (qx_choose_then `xt` (qx_choose_then `yt`
        (qx_choose_then `post` (qx_choose_then `postt` strip_assume_tac))))))))) >>
  drule_all ptr_focus_store_next >>
  disch_then (qx_choose_then `i` (qx_choose_then `z` strip_assume_tac)) >>
  drule ptr_tagged_chrono_step_projection >> strip_tac >>
  `ptr_paired_cursor lp z zt` by
    (irule ptr_ordinary_next_cursor >>
     conj_tac >- simp[IgnAsm `post = _`, IgnAsm `zt.po_state = _`,
                      ptr_ledger_next_def, ptr_observe_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`a`,`at`] >>
     `a.po_inst.inst_opcode <> NOP` by fs[listTheory.MEM] >>
     `MEM at.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE] /\ at.po_inst.inst_outputs = []` by fs[] >>
     imp_res_tac ptr_focus_store_post_fields >>
     simp[ptr_ledger_next_def, ptr_observe_def] >> metis_tac[]) >>
  suspend "write"
QED

Resume ptr_focus_store_step[write]:
  drule_all ptr_focus_store_operand_facts >> strip_tac >>
  `word_agree_except (op_taint a.po_taint v) y yt /\
   (a.po_inst.inst_opcode = MSTORE8 ==> y = yt) /\
   (a.po_inst.inst_opcode = ISTORE ==> xt = x)` by
    (conj_tac >- fs[ptr_value_transport_def] >>
     conj_tac >> strip_tac
     >- (`op_taint a.po_taint v = {}` by metis_tac[] >>
         fs[ptr_value_transport_scalar_empty]) >>
     `op_prov TG d = NONE` by metis_tac[] >>
     fs[ptr_value_transport_scalar_empty]) >>
  qabbrev_tac `len:num = if a.po_inst.inst_opcode = MSTORE8 then 1 else 32` >>
  `len <> 0` by (simp[Abbr `len`] >> IF_CASES_TAC >> simp[]) >>
  `source_memory_write_ranges a.po_inst a.po_state = [(w2n x,len)] /\
   step_writes a.po_inst a.po_state z.po_state = [(w2n x,len)] /\
   mem_write_ops a.po_inst = SOME <|iao_ofst := d; iao_size := SOME (Lit (n2w len));
                                   iao_max_size := SOME (Lit (n2w len))|>` by
    (qpat_x_assum `eval_operand d at.po_state = _` kall_tac >>
     drule_all (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV)
       ptr_focus_store_footprint) >>
     disch_then (qspec_then `z.po_state` mp_tac) >> simp[Abbr `len`]) >>
  `step_writes at.po_inst at.po_state zt.po_state = [(w2n xt,len)]` by
    (qpat_x_assum `eval_operand d a.po_state = _` kall_tac >>
     qpat_x_assum `at.po_inst = a.po_inst` SUBST_ALL_TAC >>
     drule_all (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV)
       ptr_focus_store_footprint) >>
     disch_then (qspec_then `zt.po_state` mp_tac) >> simp[Abbr `len`]) >>
  `?reloc. (!k. k < len ==> reloc (w2n x + k) = w2n xt + k) /\
          ptr_paired_write_owner (dyn_floor C a.po_state) lo positions reloc
            (range_bytes [(w2n x,len)]) (tokens,registry,births,PT,TG,saved,entries)` by
    (`ptr_value_transport births positions (op_prov TG d) {} x xt` by fs[] >>
     irule ptr_focus_store_destination >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`h`,`vs`] >> simp[]) >>
  `!k. k < len /\ w2n x + k NOTIN z.po_taint.t_mem ==>
       read_byte (w2n x + k) z.po_state.vs_memory =
       read_byte (w2n xt + k) zt.po_state.vs_memory` by
    (gen_tac >>
     simp[ptr_ledger_next_def, ptr_observe_def,
          IgnAsm `post = _`, IgnAsm `postt = _`] >>
     strip_tac >>
     pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule ptr_focus_store_written_byte >>
     qexistsl_tac [`d`,`a.po_inst`,`a.po_state`,`at.po_state`,`a.po_taint`,`v`,`y`,`yt`] >>
     simp[Abbr `len`, IgnAsm `post = _`, IgnAsm `postt = _`] >>
     simp[]) >>
  `ptr_ledger_write_pair C C' reloc a z at zt` by
    (irule ptr_focus_store_write_pair >>
     simp[IgnAsm `z = _`, IgnAsm `zt.po_state = _`,
          IgnAsm `post = _`, IgnAsm `postt = _`] >>
     pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {}` by
    (simp[range_bytes_def, EXTENSION] >> qexists_tac `w2n x` >> simp[]) >>
  `ptr_paired_write_owner (dyn_floor C a.po_state) lo positions reloc
     (range_bytes (step_writes a.po_inst a.po_state z.po_state))
     (tokens,registry,births,PT,TG,saved,entries)` by
    simp[IgnAsm `dyn_floor C a.po_state = _`] >>
  drule_all ptr_focus_store_write_event >> strip_tac >>
  `ptr_history_content (step_taint a.po_inst a.po_state post a.po_taint) post postt` by
    (irule ptr_focus_store_history >> fs[ptr_paired_sample_def] >> metis_tac[]) >>
  qexistsl_tac [`z`,`reloc`] >>
  drule_all ptr_focus_store_attach >> simp[]
QED
Finalise ptr_focus_store_step
