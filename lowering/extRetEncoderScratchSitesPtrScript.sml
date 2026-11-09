(* Compiler-region resources for recursive external-return encoding. *)
Theory extRetEncoderScratchSitesPtr
Ancestors
  extRetScratchResourcePtr extRetEncoderRegionPtr abiEncoderWindowContract abiEncoderProps
  exprSimOperands venomMemDefs pred_set arithmetic abiDecoderCode abiEncoder context venomInst
  loweringHalt exprLoweringProps

Theorem scratch_resource_restrict:
  scratch_resource ctx fn sites q len s /\ children SUBSET sites /\
  (len' <> 0 ==> len <> 0 /\ q <= q' /\ q'+len' <= q+len) ==>
  scratch_resource ctx fn children q' len' s
Proof
  simp_tac std_ss [scratch_resource_def, SUBSET_DEF] >> strip_tac >>
  conj_tac >- (rpt strip_tac >> res_tac >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `id IN sites` by metis_tac[] >>
  qpat_x_assum `!id b sz. _` drule_all >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Reuse the decoder's generic allocation-syntax certificate for encoders. *)
val scratch_code_simps = [abi_decoder_code_emit_op, abi_decoder_code_emit_void,
  abi_decoder_code_emit_inst, abi_decoder_code_return,
  abi_decoder_code_fresh_label, abi_decoder_code_new_block,
  abi_decoder_code_alloc_buffer];
val scratch_db = fn t => rpt gen_tac >> ho_match_mp_tac abi_decoder_code_bind >>
  conj_tac >- simp (t::scratch_code_simps) >> rpt strip_tac;
val scratch_dib = fn t => ho_match_mp_tac abi_decoder_code_ignore_bind >>
  conj_tac >- simp (t::scratch_code_simps) >> rpt strip_tac;

Theorem encoder_static_alloc_code:
  abi_decoder_code st (SND (compile_abi_encode_static dst src st))
Proof
  rewrite_tac[compile_abi_encode_static_def] >>
  scratch_db abi_decoder_code_emit_op >>
  scratch_dib abi_decoder_code_emit_void >> simp[abi_decoder_code_return]
QED

Theorem encoder_static_info_alloc_code:
  !ei dst src st.
    abi_decoder_code st (SND (compile_abi_encode_static_info dst src ei st))
Proof
  Cases >> simp[compile_abi_encode_static_info_def,
    encoder_static_alloc_code, abi_decoder_code_return] >> rpt gen_tac >>
  scratch_dib abi_decoder_code_emit_void >> simp[abi_decoder_code_return]
QED

Theorem encoder_static_loop_alloc_code:
  abi_decoder_code st
    (SND (compile_abi_encode_dyn_static_loop dst src ei asz msz len st))
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  scratch_db abi_decoder_code_alloc_buffer >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  scratch_dib abi_decoder_code_emit_void >>
  ntac 3 (scratch_db abi_decoder_code_fresh_label) >>
  scratch_dib abi_decoder_code_emit_inst >>
  scratch_dib abi_decoder_code_new_block >>
  ntac 3 (scratch_db abi_decoder_code_emit_op) >>
  scratch_dib abi_decoder_code_emit_inst >>
  scratch_dib abi_decoder_code_new_block >>
  ntac 7 (scratch_db abi_decoder_code_emit_op) >>
  scratch_dib encoder_static_info_alloc_code >>
  scratch_db abi_decoder_code_emit_op >>
  scratch_dib abi_decoder_code_emit_void >>
  scratch_dib abi_decoder_code_emit_inst >>
  scratch_dib abi_decoder_code_new_block >>
  ntac 2 (scratch_db abi_decoder_code_emit_op) >>
  simp[abi_decoder_code_emit_op]
QED

Theorem encoder_alloc_code_mutual:
  (!dst cp ci dyn off dp st.
    abi_decoder_code st (SND (compile_abi_encode_child dst cp ci dyn off dp st))) /\
  (!dst src ei st.
    abi_decoder_code st (SND (compile_abi_encode_to_buf dst src ei st))) /\
  (!dst src elems so ho dp st.
    abi_decoder_code st (SND (compile_abi_encode_complex_elems dst src elems so ho dp st))) /\
  (!dst src ei asz msz len st.
    abi_decoder_code st (SND (compile_abi_encode_dyn_loop dst src ei asz msz len st)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  >- (rewrite_tac[Once compile_abi_encode_child_def] >>
      scratch_db abi_decoder_code_emit_op >> IF_CASES_TAC >> fs[] >>
      ntac 2 (scratch_db abi_decoder_code_emit_op) >>
      ho_match_mp_tac abi_decoder_code_bind >> conj_tac
      >- (rpt gen_tac >> first_x_assum irule) >>
      rpt gen_tac >> scratch_dib abi_decoder_code_emit_void >>
      scratch_db abi_decoder_code_emit_op >>
      scratch_dib abi_decoder_code_emit_void >> simp[abi_decoder_code_return])
  >- (rewrite_tac[Once compile_abi_encode_child_def] >> simp[encoder_static_alloc_code])
  >- (rewrite_tac[Once compile_abi_encode_child_def] >>
      ntac 4 (scratch_db abi_decoder_code_emit_op) >>
      scratch_dib abi_decoder_code_emit_void >> scratch_db abi_decoder_code_emit_op >>
      scratch_dib abi_decoder_code_emit_void >>
      ntac 2 (scratch_db abi_decoder_code_emit_op) >> simp[abi_decoder_code_emit_op])
  >- (rewrite_tac[Once compile_abi_encode_child_def] >>
      scratch_dib abi_decoder_code_emit_void >> simp[abi_decoder_code_return])
  >- (rewrite_tac[Once compile_abi_encode_child_def] >>
      scratch_db abi_decoder_code_alloc_buffer >>
      simp_tac pure_ss [LET_THM] >> BETA_TAC >>
      scratch_dib abi_decoder_code_emit_void >> scratch_db abi_decoder_code_emit_op >>
      scratch_dib abi_decoder_code_emit_void >>
      ho_match_mp_tac abi_decoder_code_bind >> conj_tac
      >- (rpt gen_tac >> IF_CASES_TAC
          >- simp[encoder_static_loop_alloc_code] >> gvs[] >> first_x_assum irule >> simp[]) >>
      rpt gen_tac >> ntac 2 (scratch_db abi_decoder_code_emit_op) >>
      scratch_dib abi_decoder_code_emit_void >> simp[abi_decoder_code_emit_op])
  >- (rewrite_tac[Once compile_abi_encode_child_def] >> simp[abi_decoder_code_return])
  >- (rewrite_tac[Once compile_abi_encode_child_def] >>
      simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gnvs[]
      >- (scratch_db abi_decoder_code_alloc_buffer >>
          simp_tac pure_ss [LET_THM] >> BETA_TAC >>
          scratch_dib abi_decoder_code_emit_void >>
          ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
          >- (rpt gen_tac >> first_x_assum irule) >> simp[abi_decoder_code_emit_op]) >>
      rpt gen_tac >> ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
      >- (rpt gen_tac >> first_x_assum irule) >> simp[abi_decoder_code_return])
  >- (rewrite_tac[Once compile_abi_encode_child_def] >> simp[abi_decoder_code_return])
  >- (rewrite_tac[Once compile_abi_encode_child_def] >>
      scratch_db abi_decoder_code_emit_op >>
      ho_match_mp_tac abi_decoder_code_ignore_bind >> conj_tac
      >- (rpt gen_tac >> first_x_assum irule) >> rpt gen_tac >> first_x_assum irule)
  >> rewrite_tac[Once compile_abi_encode_child_def] >>
  scratch_db abi_decoder_code_alloc_buffer >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> scratch_dib abi_decoder_code_emit_void >>
  scratch_db abi_decoder_code_alloc_buffer >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  scratch_db abi_decoder_code_emit_op >> scratch_dib abi_decoder_code_emit_void >>
  ntac 3 (scratch_db abi_decoder_code_fresh_label) >>
  scratch_dib abi_decoder_code_emit_inst >> scratch_dib abi_decoder_code_new_block >>
  ntac 3 (scratch_db abi_decoder_code_emit_op) >>
  scratch_dib abi_decoder_code_emit_inst >> scratch_dib abi_decoder_code_new_block >>
  ntac 9 (scratch_db abi_decoder_code_emit_op) >>
  ho_match_mp_tac abi_decoder_code_bind >> conj_tac
  >- (rpt gen_tac >> first_x_assum irule >> simp[]) >>
  rpt gen_tac >> scratch_dib abi_decoder_code_emit_void >>
  scratch_db abi_decoder_code_emit_op >> scratch_dib abi_decoder_code_emit_void >>
  scratch_db abi_decoder_code_emit_op >> scratch_dib abi_decoder_code_emit_void >>
  scratch_dib abi_decoder_code_emit_inst >> scratch_dib abi_decoder_code_new_block >>
  scratch_dib abi_decoder_code_emit_op >> scratch_db abi_decoder_code_emit_op >>
  simp[abi_decoder_code_emit_op]
QED

Theorem encoder_new_alloca_shape:
  compile_abi_encode_to_buf dst src ei st = (result,en) /\
  abi_decoder_code_member inst en /\ ~abi_decoder_code_member inst st /\
  inst.inst_opcode = ALLOCA ==>
  st.cs_next_id <= inst.inst_id /\ inst.inst_id < en.cs_next_id /\
  inst.inst_operands = [Lit 32w] /\ ?out. inst.inst_outputs = [out]
Proof
  strip_tac >>
  `abi_decoder_code st en` by
    metis_tac[encoder_alloc_code_mutual, pairTheory.SND] >>
  drule_all abi_decoder_code_alloca >> simp[]
QED

Theorem encoder_window_scratch_resource:
  compile_abi_encode_to_buf dst src ei st = (result,en) /\
  fn_has_code st en fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv st /\ sb.cs_next_id <= st.cs_next_id /\
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  scratch_resource ctx fn (window_alloca_sites fn (frag_ids st en))
    (w2n w) (val_footprint tv v) s
Proof
  strip_tac >> irule scratch_resource_from_expr >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl [`cenv`, `cx`, `es`, `sa`, `sb`] >> simp[] >>
  rpt gen_tac >> simp[window_alloca_sites_def, frag_ids_def] >> strip_tac >>
  `encoder_region st en` by metis_tac[encoder_region_mutual, pairTheory.SND] >>
  `st.cs_next_id <= inst.inst_id /\ inst.inst_id < en.cs_next_id` by simp[] >>
  drule_all encoder_region_alloca_fresh >> strip_tac >>
  qexists `out` >>
  conj_tac
  >- (qpat_x_assum `MEM inst (fn_insts fn)` mp_tac >>
      `inst = mk_inst id ALLOCA [Lit 32w] [out]` by
        (simp[venomInstTheory.instruction_component_equality, venomInstTheory.mk_inst_def]) >> simp[]) >>
  metis_tac[fresh_not_local_ptr]
QED

(* Entry cut after lowering the expression and allocating the return buffer.
   Reservation is the statement fragment's initial compiler premise, not a
   fresh hypothesis at the encoder frontier.  The semantic source interval
   remains the expression interval even at this later runtime state. *)
Theorem encoder_return_buffer_scratch_resource:
  lower_value compile_expr cenv ret e sa = (op,sb) /\
  compile_alloc_buffer cenv.ce_max_return_size sb = (buf,st) /\
  compile_abi_encode_to_buf buf.buf_operand op ei st = (result,en) /\
  fn_has_code st en fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  scratch_resource ctx fn (window_alloca_sites fn (frag_ids st en))
    (w2n w) (val_footprint tv v) s
Proof
  strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `local_ptrs_reserved cenv st` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  irule encoder_window_scratch_resource >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`cenv`, `cx`, `es`, `op`, `sa`, `sb`, `ty`] >> simp[]
QED
