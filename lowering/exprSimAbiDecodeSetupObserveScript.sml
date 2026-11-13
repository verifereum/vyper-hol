Theory exprSimAbiDecodeSetupObserve
Ancestors
  exprSimAbiDecodeSetupExec exprSimAbiDecodeSuffixWrites abiBuiltinDecodeSetup
  abiBuiltinAllocation abiDecoderReentry compileEnv emitHelperProps
  exprSimAbiDecodeSuffixFrame exprSimAbiDecodeAllocationPreserve
  exprSimAbiGasBridge abiEncoderObserver fragExec exprLoweringProps
  venomExecSemantics venomExecProofs venomInstProofs venomInst venomState list rich_list pair
  finite_map pred_set arithmetic

Theorem abi_decode_observer_nonentry_phi_zero:
  cs_extends sa sb /\ frag_gas_free sa sb /\ lbl <> sa.cs_current_bb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[] >> drule_all frag_observer_end_nonphi >> strip_tac >>
      Cases_on `sb.cs_current_insts` >>
      fs[phi_prefix_length_def, mk_inst_def]) >>
  `emitted_blocks sa sb <> []` by (strip_tac >> gvs[]) >>
  `bb <> LAST (emitted_blocks sa sb)` by
    (drule frag_extends_emitted_shape >> simp[] >> metis_tac[]) >>
  `MEM bb (FRONT (emitted_blocks sa sb))` by
    (`emitted_blocks sa sb = FRONT (emitted_blocks sa sb) ++
        [LAST (emitted_blocks sa sb)]` by simp[APPEND_FRONT_LAST] >>
     metis_tac[MEM_APPEND, MEM]) >>
  `EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (fs[frag_gas_free_def, frag_code_def, NULL_EQ, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  Cases_on `bb.bb_instructions` >> fs[phi_prefix_length_def]
QED

Theorem abi_decode_observer_region_write_safe:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (!i x. MEM i (frag_code sa sb) /\ x IN protected ==> ~MEM x i.inst_outputs) ==>
  abi_decode_region_write_safe ctx (frag_observer sa sb fn id)
    (frag_observer_cut sb)
    (\s. (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb) protected
Proof
  strip_tac >> simp_tac pure_ss [abi_decode_region_write_safe_def] >>
  conj_tac
  >- (rpt strip_tac >> drule_all frag_observer_code_provenance >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN /\
       ~MEM (Label sa.cs_current_bb) inst.inst_operands` by
        metis_tac[frag_observer_off_cut_opcodes] >>
      `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
        (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
         gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
         pairarg_tac >> gvs[]) >>
      `middle.vs_current_bb <> sa.cs_current_bb` by
        (irule frag_observer_jump_no_reentry >>
         qexistsl_tac [`inst`, `s`] >> metis_tac[step_inst_non_invoke]) >>
      `phi_prefix_length target.bb_instructions = 0` by
        metis_tac[abi_decode_observer_nonentry_phi_zero] >> simp[]) >>
  rpt strip_tac >>
  drule_all frag_observer_region_closed >>
  simp[observer_region_closed_def] >> metis_tac[]
QED

Theorem abi_decode_suffix_observer_output:
  compile_abi_decode_to_buf dst src opc base_op hi info ready = ((),final) /\
  cs_extends ready final /\ fn_has_code ready final fn /\ frag_gas_free ready final /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region ready final /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_observer ready final fn id) s = Halt (stop_view t) /\
  (t.vs_current_bb,t.vs_inst_idx) = frag_observer_cut final /\
  x IN abi_decoder_older_vars ready.cs_next_var /\
  eval_operand (Var x) s = SOME value /\
  FLOOKUP s.vs_allocas site = SOME entry ==>
  eval_operand (Var x) t = SOME value /\ FLOOKUP t.vs_allocas site = SOME entry
Proof
  strip_tac >>
  `abi_decode_region_write_safe ctx (frag_observer ready final fn id)
      (frag_observer_cut final)
      (\s. (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region ready final)
      (abi_decoder_older_vars ready.cs_next_var)` by
    (irule abi_decode_observer_region_write_safe >> simp[] >>
     metis_tac[abi_decode_to_buf_older_outputs_disjoint]) >>
  `?u. local_prefix ctx (frag_observer ready final fn id) (frag_observer_cut final) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[] >>
     conj_tac >- (qexists_tac `fuel` >> simp[]) >>
     simp[stop_view_def, halt_state_def]) >>
  `FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x` by
    (drule abi_decode_local_prefix_var_frame >>
     disch_then (qspecl_then
       [`\s. (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region ready final`,
        `abi_decoder_older_vars ready.cs_next_var`] mp_tac) >> simp[]) >>
  `FLOOKUP u.vs_allocas site = SOME entry` by
    metis_tac[abi_decode_local_prefix_preserves_allocation] >>
  drule stop_view_fields >> strip_tac >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_drop_member_mono[local]:
  n <= m /\ MEM i (DROP m xs) ==> MEM i (DROP n xs)
Proof
  simp[MEM_DROP, MEM_EL] >> rpt strip_tac >>
  rename1 `i = EL (m + k) xs` >>
  qexists_tac `m + k - n` >> simp[]
QED

Theorem abi_decode_setup_suffix_shape:
  abi_builtin_decode_setup data mn mx outsz start = (ops,ready) /\
  frag_gas_free start final ==>
  frag_gas_free ready final /\
  frag_observer ready final fn id = frag_observer start final fn id
Proof
  strip_tac >> drule abi_builtin_decode_setup_shape >> strip_tac >>
  `emitted_blocks ready final = emitted_blocks start final` by
    simp[emitted_blocks_def] >>
  conj_tac
  >- (fs[frag_gas_free_def, frag_code_def, emitted_insts_def] >>
      `LENGTH start.cs_current_insts <= LENGTH ready.cs_current_insts` by
        metis_tac[IS_PREFIX_LENGTH] >>
      Cases_on `NULL (emitted_blocks start final)` >> gvs[EVERY_MEM, MEM_APPEND] >>
      metis_tac[abi_decode_drop_member_mono]) >>
  simp[frag_observer_def]
QED

Theorem abi_decode_setup_run_control:
  abi_builtin_decode_setup data mn mx outsz start = (ops,ready) /\
  run_inst_seq (emitted_insts start ready) s = OK a ==>
  a.vs_current_bb = s.vs_current_bb /\ a.vs_halted = s.vs_halted
Proof
  strip_tac >> drule abi_builtin_decode_setup_shape >> strip_tac >>
  fs[EVERY_MEM] >> conj_tac
  >- (irule (run_inst_seq_preserves_field |> Q.ISPEC `\s. s.vs_current_bb` |> SRULE []) >>
      goal_assum (drule_at Any) >> rpt strip_tac >>
      `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by metis_tac[] >>
      metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  irule (run_inst_seq_preserves_field |> Q.ISPEC `\s. s.vs_halted` |> SRULE []) >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  metis_tac[step_inst_base_OK_preserves_halted]
QED

Theorem abi_decode_lower_observer_output:
  lower_abi_decode data info mn mx outsz start = (result,final) /\
  fn_has_code start final fn /\ frag_gas_free start final /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ ~s.vs_halted /\
  run_from fuel ctx (frag_observer start final fn id) s = Halt (stop_view t) /\
  (t.vs_current_bb,t.vs_inst_idx) = frag_observer_cut final /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site start mn mx) = NONE /\
      d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas (abi_builtin_decode_output_site start mn mx) = SOME(d,outsz)) /\
  outsz < dimword (:256) ==>
  eval_operand result t = SOME (n2w d) /\
  FLOOKUP t.vs_allocas (abi_builtin_decode_output_site start mn mx) = SOME(d,outsz)
Proof
  strip_tac >>
  `fn_has_code start final (frag_observer start final fn id)` by
    metis_tac[frag_observer_has_code] >>
  drule_at (Pat `run_from _ _ _ _ = _`) abi_decode_lower_setup_output >>
  disch_then drule >> simp[] >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule_all abi_decode_setup_run_control >> strip_tac >>
  drule_all abi_decode_setup_suffix_shape >> strip_tac >>
  `cs_extends start ready` by
    (simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code ready final fn` by metis_tac[fn_has_code_split] >>
  `?x. result = Var x` by
    (drule abi_builtin_decode_setup_trace >> strip_tac >>
     drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> gvs[]) >>
  gvs[] >> qpat_x_assum `Var x = _` (SUBST_ALL_TAC o SYM) >>
  irule abi_decode_suffix_observer_output >>
  goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`ctx`, `fn`, `fuel`, `id`,
    `a with vs_inst_idx := LENGTH ready.cs_current_insts`] >>
  qpat_assum `cs_extends ready final`
    (mp_then Any mp_tac frag_observer_start_region) >>
  fs[frag_observer_region_def, abi_decoder_operand_live_def,
     abi_decoder_older_vars_def, eval_operand_def, lookup_var_def]
QED
