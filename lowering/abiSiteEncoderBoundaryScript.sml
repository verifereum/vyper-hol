(* Finite-site entry probe for the allocation-bearing complex encoder. *)
Theory abiSiteEncoderBoundary
Ancestors
  abiSiteAllocation abiSiteCaller abiSiteEncoderContract abiEncoderComplexPrefix abiScratchSequence
  abiScratchEffect abiScratchFootprint abiEncoderSequence abiDecoderReentryAddress
  abiDecoderProtectedScratch abiDecoderFootprint abiDecoderAllocation abiDecoderFrame
  abiDecoderContract abiDecoderLoop abiDecoderIndexInit abiDecoderArrayHeader
  abiDecoderGuards venomMemProps compilerOccurrences abiDecoderSiteMembership
  abiEncoderComplexCode fragExec instIdxIndep abiDecoderReentry emitHelperProps exprLoweringProps compileEnv
  context emitHelper venomExecSemantics venomState venomInst finite_map pred_set words list rich_list arithmetic

Theorem abi_site_alloc_buffer_reentry_evolution:
  compile_alloc_buffer 32 st = (buf,st') /\
  abi_site_budget A b cap s /\ st.cs_next_id IN A /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ buf.buf_size = 32 /\
    abi_site_budget A b cap t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    b <= p /\ p + 32 <= b + cap /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted /\
    abi_scratch_evolution A b cap s t
Proof
  simp_tac bool_ss [compile_alloc_buffer_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ALLOCA [Lit 32w] st = (allocated_op,allocation_st)` >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `alloc_inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `alloc_inst.inst_id IN A /\
   alloc_inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)]` by
    simp[Abbr `alloc_inst`, mk_inst_def] >>
  drule_all abi_site_alloca32 >> strip_tac >>
  rename1 `exec_alloca alloc_inst s 32w = OK t` >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString st.cs_next_var),n2w p) /\
   t.vs_labels = s.vs_labels /\ t.vs_halted = s.vs_halted` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     rw[exec_alloca_def] >>
     gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `run_inst_seq (emitted_insts st allocation_st) s = OK t` by
    (simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def] >>
     qpat_x_assum `exec_alloca alloc_inst s 32w = OK t` mp_tac >>
     simp[Abbr `alloc_inst`, mk_inst_def]) >>
  `t.vs_alloca_next <= b + cap` by
    (qpat_x_assum `abi_site_budget A b cap t` mp_tac >>
     simp_tac bool_ss [abi_site_budget_def] >> rpt strip_tac >> decide_tac) >>
  `abi_scratch_evolution A b cap s t` by
    (drule_all abi_scratch_evolution_alloca >> simp[]) >>
  qexistsl_tac [`t`, `p`] >>
  gvs[Abbr `alloc_inst`, mk_inst_def, eval_operand_def]
QED

Theorem abi_site_alloc_buffer_reentry:
  compile_alloc_buffer 32 st = (buf,st') /\
  abi_site_budget A b cap s /\ st.cs_next_id IN A /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ buf.buf_size = 32 /\
    abi_site_budget A b cap t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    b <= p /\ p + 32 <= b + cap /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted
Proof
  strip_tac >> drule_all abi_site_alloc_buffer_reentry_evolution >> strip_tac >>
  qexistsl_tac [`t`, `p`] >> asm_rewrite_tac[]
QED

Theorem abi_site_complex_prefix_sequence_evolution:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_site_budget A b cap initial /\ st.cs_next_id IN A /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual slot. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    mload slot actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
    b <= slot /\ slot+32 <= b+cap /\
    abi_site_budget A b cap actual /\ fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op actual = eval_operand op initial) /\
    abi_decode_frame slot 32 initial actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (slot,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    actual.vs_halted = initial.vs_halted /\
    abi_scratch_evolution A b cap initial actual
Proof
  strip_tac >> drule abi_encoder_complex_prefix_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `allocation_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_site_alloc_buffer_reentry_evolution >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocation_st) initial = OK allocated` >>
  `b+cap < dimword (:256)` by metis_tac[abi_site_budget_def] >>
  `p < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))) allocated =
    SOME (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))` by simp[eval_operand_def] >>
  `run_inst_seq (emitted_insts allocation_st st') allocated =
    OK (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    (drule_all abi_decode_store_sequence >> simp[w2n_n2w]) >>
  `inst_extends st allocation_st /\ inst_extends allocation_st st'` by
    (conj_tac >- (drule abi_decode_alloc_buffer_inst_extends >> simp[]) >>
     drule inst_extends_emit_void >> simp[]) >>
  `run_inst_seq (emitted_insts st st') initial =
    OK (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    (drule_all abi_decode_sequence_chain >> simp[]) >>
  `abi_decode_frame p 32 allocated
    (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    irule abi_decode_mstore_frame >>
  qexistsl_tac [`mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated`, `p`] >>
  `!p w s. abi_site_budget A b cap (mstore p w s) <=> abi_site_budget A b cap s` by
    (rpt gen_tac >> irule abi_site_budget_fields >>
     simp[mstore_def, write_memory_with_expansion_def]) >>
  `!s t p w. abi_scratch_evolution A b cap s (mstore p w t) <=>
      abi_scratch_evolution A b cap s t` by
    simp[mstore_def, write_memory_with_expansion_def, abi_scratch_evolution_def] >>
  asm_simp_tac bool_ss [fresh_vars_wrt_mstore, eval_operand_mstore, mload_mstore_same] >>
  gvs[abi_decode_frame_def, mstore_def, write_memory_with_expansion_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_site_complex_prefix_sequence:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_site_budget A b cap initial /\ st.cs_next_id IN A /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual slot. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    mload slot actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
    b <= slot /\ slot+32 <= b+cap /\
    abi_site_budget A b cap actual /\ fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op actual = eval_operand op initial) /\
    abi_decode_frame slot 32 initial actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (slot,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule_all abi_site_complex_prefix_sequence_evolution >> strip_tac >>
  qexistsl_tac [`actual`, `slot`] >> asm_rewrite_tac[]
QED


(* A real recursive encoder invocation must preserve an already initialized
   parent slot. Its budget is A, not the smaller child footprint. *)
Theorem abi_site_encoder_child_slot:
  abi_site_encoder_effect A lo hi next limit_st d sz b cap s t /\
  abi_site_budget A b cap s /\ site IN A /\ site < lo /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  abi_footprint_disjoint d sz (abi_decoder_child_scratch A b cap s) ==>
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = mload slot s
Proof
  strip_tac >>
  `~(site IN abi_decoder_ids lo hi)` by simp[abi_decoder_ids_def] >>
  drule_all abi_site_effect_slot >> simp[]
QED

Theorem abi_site_encoder_child_run:
  abi_site_encoder ei /\ compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_site_encoder_input ei at av start src dst sb source_cap d (LENGTH (enc at av))
    A b cap initial /\ abi_site_budget A b cap initial /\
  abi_decoder_emitted_sites start.cs_next_id end_st.cs_next_id start end_st SUBSET A /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  site IN A /\ site < start.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_site_encoder_effect A start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    mload slot actual = mload slot initial /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_site_encoder_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_footprint_disjoint d (LENGTH (enc at av))
    (abi_decoder_child_scratch A b cap initial)` by
    (qpat_x_assum `abi_site_encoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_site_encoder_input_def] >> metis_tac[]) >>
  drule_all abi_site_encoder_child_slot >> strip_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[]
QED

Theorem abi_site_complex_prefix_sites:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') ==>
  abi_decoder_emitted_sites st.cs_next_id st'.cs_next_id st st' = {st.cs_next_id}
Proof
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[abi_decoder_emitted_sites_def, compiler_emitted_def, compiler_chrono_def,
    EXTENSION, GSPECIFICATION, APPEND_ASSOC, mk_inst_def] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def] >>
  `!a b:num. a+b-(a+(b+1)) = 0` by decide_tac >>
  asm_simp_tac (srw_ss()) [SF DNF_ss] >> decide_tac
QED
Theorem abi_site_complex_prefix_effect:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_site_budget A b cap initial /\ st.cs_next_id IN A /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual slot. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    mload slot actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
    b <= slot /\ slot+32 <= b+cap /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (slot,32) /\
    abi_site_encoder_effect A st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d sz b cap initial actual
Proof
  strip_tac >> drule_all abi_site_complex_prefix_sequence_evolution >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  qabbrev_tac `B = A INTER abi_decoder_ids st.cs_next_id st'.cs_next_id` >>
  `FINITE A` by
    (qpat_x_assum `abi_site_budget A b cap initial` mp_tac >>
     simp_tac bool_ss [abi_site_budget_def] >> rpt strip_tac >> asm_rewrite_tac[]) >>
  `B SUBSET A /\ st.cs_next_id IN B` by
    simp[Abbr `B`, abi_decoder_ids_def] >>
  `FINITE B` by metis_tac[SUBSET_FINITE] >>
  `abi_scratch_evolution B b cap initial actual` by
    (irule abi_scratch_evolution_subset >> qexists_tac `A` >> asm_rewrite_tac[]) >>
  `abi_decode_footprint_frame (abi_decoder_child_scratch B b cap initial)
      initial actual` by
    (irule abi_scratch_final_slot_frame >> asm_rewrite_tac[] >>
     qexistsl_tac [`st.cs_next_id`, `slot`, `32`] >> asm_rewrite_tac[]) >>
  `abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch B b cap initial)
      initial actual` by
    (qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decode_footprint_frame_def] >> strip_tac >>
     asm_rewrite_tac[] >> rpt strip_tac >> first_x_assum irule >>
     fs[abi_footprint_disjoint_def]) >>
  qexistsl_tac [`actual`, `slot`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [abi_site_encoder_effect_def] >> gvs[Abbr `B`]
QED

Definition abi_site_complex_prefix_post_def:
  abi_site_complex_prefix_post (infos:(abi_enc_info # num # num # bool) list)
      dyn_ptr st st' A limit_st d sz b cap initial actual <=>
    ?slot. eval_operand dyn_ptr actual = SOME (n2w slot) /\
      mload slot actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
      b <= slot /\ slot+32 <= b+cap /\
      FLOOKUP actual.vs_allocas st.cs_next_id = SOME (slot,32) /\
      abi_site_encoder_effect A st.cs_next_id st'.cs_next_id st.cs_next_var
        limit_st d sz b cap initial actual
End

Theorem abi_site_complex_prefix_post_inst_idx[simp]:
  abi_site_complex_prefix_post infos dyn_ptr st st' A limit_st d sz b cap initial
    (actual with vs_inst_idx := ix) <=>
  abi_site_complex_prefix_post infos dyn_ptr st st' A limit_st d sz b cap initial actual
Proof
  simp[abi_site_complex_prefix_post_def, abi_site_encoder_effect_def,
    fresh_vars_wrt_def, abi_site_budget_def, abi_scratch_evolution_def,
    eval_op_inst_idx, mload_def, abi_decode_footprint_frame_def]
QED

Theorem abi_site_complex_prefix_reach:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  abi_site_budget A b cap initial /\ st.cs_next_id IN A /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_site_complex_prefix_post infos dyn_ptr st st' A limit_st d sz b cap
      initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  `frag_exec ctx st st' (\s. s = initial)
    (abi_site_complex_prefix_post infos dyn_ptr st st' A limit_st d sz b cap initial)
    (K F)` by
    (irule frag_exec_run_inst_seq >> asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     disj1_tac >>
     drule_all abi_site_complex_prefix_effect >>
     disch_then (qspecl_then [`sz`, `d`] strip_assume_tac) >>
     qexists_tac `actual` >> simp_tac bool_ss [abi_site_complex_prefix_post_inst_idx] >>
     simp_tac bool_ss [abi_site_complex_prefix_post_def] >> asm_rewrite_tac[] >>
     qexists_tac `slot` >> gvs[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by
    fs[abi_site_complex_prefix_post_def, abi_site_encoder_effect_def] >>
  qexists_tac `actual` >> asm_rewrite_tac[]
QED


(* Reject any transitive admission in the allocation/child interface probes. *)
val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean finite-site encoder boundary: " ^ name)
  end) (DB.thms "abiSiteEncoderBoundary");
