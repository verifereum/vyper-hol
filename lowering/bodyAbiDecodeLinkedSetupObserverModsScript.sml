(* Observe the selected setup result at the relabelled caller entry. *)
Theory bodyAbiDecodeLinkedSetupObserverMods
Ancestors
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinLengthGuard
  abiBuiltinBoundTests abiBuiltinAllocation compileEnv emitHelper context
  bodyFullAbiDecodeCutEntryPhase exprSimAbiGasBridge exprSimAbiDecodePrefixExec
  abiEncoderObserver fragGasPath fragExec exprLoweringProps
  venomInstProps venomInst venomExecSemantics venomState
  arithmetic rich_list list

Theorem setup_observer_entry_slice[local]:
  ready.cs_blocks = st.cs_blocks /\
  isPREFIX st.cs_current_insts ready.cs_current_insts /\
  cs_extends st final /\ cs_extends ready final /\
  st.cs_blocks <> final.cs_blocks /\ LENGTH ids = LENGTH st.cs_current_insts /\
  fn_has_code (start_relabel L ids st) (start_swap st L ids final) obs ==>
  ?bb. lookup_block L obs.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts st ready) (DROP (LENGTH st.cs_current_insts) bb.bb_instructions)
Proof
  strip_tac >>
  `emitted_blocks ready final = emitted_blocks st final` by simp[emitted_blocks_def] >>
  `emitted_blocks st final <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  `isPREFIX ready.cs_current_insts (LAST (emitted_blocks st final)).bb_instructions` by
    (qpat_assum `cs_extends ready final` (mp_tac o MATCH_MP frag_extends_emitted_shape) >> simp[]) >>
  qpat_x_assum `fn_has_code _ _ obs` mp_tac >>
  simp[fn_has_code_def, start_swap_emitted_blocks] >> strip_tac >>
  qabbrev_tac `entry = LAST (emitted_blocks st final) with
    <|bb_label := L; bb_instructions := MAP (\j. mk_inst j NOP [] []) ids ++
      DROP (LENGTH st.cs_current_insts) (LAST (emitted_blocks st final)).bb_instructions|>` >>
  qexists_tac `entry` >> conj_tac >-
    (first_x_assum (qspec_then `entry` mp_tac) >> simp[Abbr `entry`]) >>
  `!ys. DROP (LENGTH st.cs_current_insts) (MAP (\j. mk_inst j NOP [] []) ids ++ ys) = ys` by
    (qpat_assum `LENGTH ids = _` (fn th =>
       simp[NoAsms, GSYM th, SRULE [LENGTH_MAP]
         (Q.ISPEC `MAP (\j. mk_inst j NOP [] []) ids` DROP_LENGTH_APPEND)])) >>
  simp[Abbr `entry`, emitted_insts_def] >>
  qpat_x_assum `st.cs_current_insts ≼ ready.cs_current_insts` mp_tac >>
  qpat_x_assum `ready.cs_current_insts ≼ _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> rpt strip_tac >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]
QED

Theorem setup_observer_nonphi[local]:
  abi_builtin_decode_setup data mn mx outsz st = (ops,ready) ==>
  EVERY (\i. i.inst_opcode <> PHI) (emitted_insts st ready)
Proof
  Cases_on `mn = mx` >>
  simp[abi_builtin_decode_setup_def, abi_builtin_decode_header_def,
    abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
    abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem setup_observer_normal_step[local]:
  lookup_block L obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  s.vs_inst_idx < cut /\ ~s.vs_halted /\ ~v.vs_halted /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK v ==>
  abi_observer_step ctx obs (L,cut) (s with vs_current_bb := L)
    ((v with vs_inst_idx := SUC s.vs_inst_idx) with vs_current_bb := L)
Proof
  strip_tac >>
  `v.vs_prev_bb = s.vs_prev_bb` by
    (irule (cj 3 step_preserves_control_flow) >> metis_tac[step_inst_non_invoke]) >>
  `!w. w.vs_prev_bb = s.vs_prev_bb ==>
       (w with <|vs_current_bb := L; vs_prev_bb := s.vs_prev_bb|>) =
       (w with vs_current_bb := L)` by simp[venom_state_component_equality] >>
  drule_all frag_relabel_base_nonphi >> disch_then (qspecl_then [`s.vs_prev_bb`,`L`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[abi_observer_step_def] >> qexists_tac `v with vs_current_bb := L` >>
  simp[step_inst_non_invoke, venom_state_component_equality]
QED

(* The synthetic source STOP isolates the phase. The target prefix does not
   execute it, and its endpoint is related to the given OK state. *)
Theorem setup_observer_success_replay:
  !xs s n.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block L obs.fn_blocks = SOME shadow /\
    DROP s.vs_inst_idx bb.bb_instructions = xs ++ [mk_inst j STOP [] []] /\
    isPREFIX xs (DROP s.vs_inst_idx shadow.bb_instructions) /\
    s.vs_inst_idx + LENGTH xs = cut /\ ~s.vs_halted /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode) xs /\
    gas_path ctx fn s n (OK t) /\ t.vs_inst_idx = cut ==>
    ?w. ~w.vs_halted /\ w.vs_current_bb = L /\ w.vs_inst_idx = cut /\
        frag_relabel_state L s.vs_current_bb w t /\
        local_prefix ctx obs (L,cut) (s with vs_current_bb := L) w
Proof
  Induct_on `xs`
  >- (simp_tac bool_ss [LENGTH, EVERY_DEF, APPEND, ADD_CLAUSES] >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `isPREFIX [mk_inst j STOP [] []] (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
      drule abi_decode_contiguous_prefix_fetch >> strip_tac >>
      drule_all entry_phase_path_stop >> strip_tac >> gvs[] >>
      qexists_tac `s with vs_current_bb := L` >>
      simp[cj 1 local_prefix_rules, frag_relabel_state_def] >>
      qexists_tac `s.vs_prev_bb` >> simp[venom_state_component_equality]) >>
  simp_tac bool_ss [LENGTH, EVERY_DEF, APPEND] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `DROP _ bb.bb_instructions = i::(xs ++ _)` >>
  `isPREFIX (i::xs) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  every_drule_then strip_assume_tac abi_decode_contiguous_prefix_fetch >>
  drule_all entry_phase_path_cons >> strip_tac
  >- (gvs[] >> decide_tac)
  >- suspend "continue" >>
  gvs[]
QED
Resume setup_observer_success_replay[continue]:
  `v.vs_current_bb = s.vs_current_bb` by metis_tac[step_inst_non_invoke, step_preserves_control_flow] >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs ++ [mk_inst j STOP [] []]` by
    (Q_TAC (TRANS_TAC EQ_TRANS) `DROP 1 (DROP s.vs_inst_idx bb.bb_instructions)` >>
     conj_tac >- simp[NoAsms, DROP_DROP_T, ADD1, ADD_COMM] >> simp[]) >>
  `s.vs_inst_idx < cut /\ SUC s.vs_inst_idx + LENGTH xs = cut` by decide_tac >>
  drule_all setup_observer_normal_step >> disch_then (qspec_then `ctx` assume_tac) >>
  first_x_assum (qspecl_then [`v with vs_inst_idx := SUC s.vs_inst_idx`,`m`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  qexists_tac `w` >> simp[] >>
  irule (cj 2 local_prefix_rules) >> goal_assum (drule_at Any) >> gvs[]
QED
Finalise setup_observer_success_replay[local]

Theorem setup_observer_success[local]:
  st.cs_blocks = ready.cs_blocks /\
  st.cs_current_bb = ready.cs_current_bb /\
  isPREFIX st.cs_current_insts ready.cs_current_insts /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_block L obs.fn_blocks = SOME shadow /\
  isPREFIX (emitted_insts st ready) (DROP (LENGTH st.cs_current_insts) shadow.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode)
    (emitted_insts st ready) /\
  (!f. fn_has_code st ready f ==> gas_path ctx f s 0 (OK t)) /\
  t.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?w. ~w.vs_halted /\ w.vs_current_bb = L /\ w.vs_inst_idx = LENGTH ready.cs_current_insts /\
      frag_relabel_state L st.cs_current_bb w t /\
      local_prefix ctx obs (L,LENGTH ready.cs_current_insts) (s with vs_current_bb := L) w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `bb = <|bb_label := ready.cs_current_bb;
                       bb_instructions := ready.cs_current_insts ++ [mk_inst 0 STOP [] []]|>` >>
  qabbrev_tac `source = (ARB : ir_function) with fn_blocks := [bb]` >>
  `lookup_block ready.cs_current_bb source.fn_blocks = SOME bb` by
    simp[Abbr `source`, Abbr `bb`, lookup_block_def, FIND_thm] >>
  `fn_has_code st ready source` by
    simp[fn_has_code_def, emitted_blocks_def, Abbr `source`, Abbr `bb`, lookup_block_def, FIND_thm,
         IS_PREFIX_APPEND] >>
  qpat_assum `s.vs_current_bb = st.cs_current_bb` (SUBST1_TAC o SYM) >>
  irule setup_observer_success_replay >> simp[] >>
  qexistsl_tac [`bb`, `source`, `0`, `0`, `emitted_insts st ready`] >>
  simp[Abbr `bb`] >>
  qpat_x_assum `st.cs_current_insts ≼ ready.cs_current_insts` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  asm_rewrite_tac[emitted_insts_def] >>
  (conj_tac >-
    (pure_once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> rewrite_tac[DROP_LENGTH_APPEND])) >>
  simp[DROP_LENGTH_APPEND, LENGTH_APPEND]
QED

Theorem abi_decode_linked_setup_observer_mods:
  abi_builtin_decode_setup data mn mx outsz st = (ops,ready) /\
  cs_extends st final /\ cs_extends ready final /\
  st.cs_blocks <> final.cs_blocks /\ LENGTH ids = LENGTH st.cs_current_insts /\
  fn_has_code (start_relabel L ids st) (start_swap st L ids final) obs /\
  FST (cut : string # num) <> L /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!f. fn_has_code st ready f ==> gas_path ctx f s 0 r) /\
  ((?t. r = OK t /\ t.vs_inst_idx = LENGTH ready.cs_current_insts) \/
   (?z. r = Abort Revert_abort z)) ==>
  (?t w. r = OK t /\ ~w.vs_halted /\ w.vs_current_bb = L /\
         w.vs_inst_idx = LENGTH ready.cs_current_insts /\
         frag_relabel_state L st.cs_current_bb w t /\
         local_prefix ctx obs (L,LENGTH ready.cs_current_insts) (s with vs_current_bb := L) w) \/
  (?z w k. r = Abort Revert_abort z /\ frag_relabel_state L st.cs_current_bb w z /\
           run_from k ctx obs (s with vs_current_bb := L) = Abort Revert_abort w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule setup_observer_nonphi >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode)
      (emitted_insts st ready)` by fs[EVERY_MEM] >>
  drule_all setup_observer_entry_slice >>
  disch_then (qx_choose_then `shadow` strip_assume_tac) >>
  qpat_assum `(?t. r = OK t /\ _) \/ _` strip_assume_tac
  >- (disj1_tac >> qexists_tac `t` >> gvs[] >>
      irule setup_observer_success >> simp[] >> qexists_tac `shadow` >> simp[]) >>
  disj2_tac >>
  `cs_extends st ready` by (irule cs_extends_same_block >> simp[]) >>
  `frag_relabel_state L st.cs_current_bb (s with vs_current_bb := L) s` by
    (simp[frag_relabel_state_def] >> qexists_tac `s.vs_prev_bb` >>
     simp[venom_state_component_equality]) >>
  `st.cs_blocks = ready.cs_blocks /\ (s with vs_current_bb := L).vs_current_bb = L` by simp[] >>
  qpat_assum `r = Abort Revert_abort z` SUBST_ALL_TAC >>
  drule_all (BETA_RULE abi_decode_cut_entry_phase) >> simp[]
QED
