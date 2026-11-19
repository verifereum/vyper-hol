(* Synchronize the setup-only observation with the relabelled entry. *)
Theory bodyFullAbiDecodeCallerSetupCut
Ancestors
  bodyFullAbiDecodeCallerSetupOrigin abiBuiltinDecodeSetup
  exprSimAbiGasBridge exprSimAbiDecodePrefixExec fragFuel fragGasPath
  abiEncoderObserver venomInstProps venomInst venomExecSemantics venomState
  fragExec exprLoweringProps arithmetic rich_list list
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  context compileEnv emitHelper
  bodyFullAbiDecodeCutEntryPhase[qualified]

Theorem setup_cut_entry_prefix[local]:
  abi_builtin_decode_setup data lo hi outsz st = (ops,ready) /\
  cs_extends st final /\ cs_extends ready final /\
  st.cs_blocks <> final.cs_blocks /\ LENGTH ids = LENGTH st.cs_current_insts /\
  fn_has_code (start_relabel L ids st) (start_swap st L ids final)
    (frag_relabel_observer st final L ids func id) ==>
  ?bb. lookup_block L (frag_relabel_observer st final L ids func id).fn_blocks = SOME bb /\
       isPREFIX (emitted_insts st ready) (DROP (LENGTH st.cs_current_insts) bb.bb_instructions)
Proof
  strip_tac >> drule abi_builtin_decode_setup_shape >> strip_tac >>
  `emitted_blocks ready final = emitted_blocks st final` by simp[emitted_blocks_def] >>
  `emitted_blocks st final <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  `isPREFIX ready.cs_current_insts (LAST (emitted_blocks st final)).bb_instructions` by
    (qpat_assum `cs_extends ready final` (mp_tac o MATCH_MP frag_extends_emitted_shape) >> simp[]) >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, start_swap_emitted_blocks] >>
  strip_tac >> qexists `LAST (emitted_blocks st final) with
    <|bb_label := L; bb_instructions := MAP (\j. mk_inst j NOP [] []) ids ++
      DROP (LENGTH st.cs_current_insts) (LAST (emitted_blocks st final)).bb_instructions|>` >>
  conj_tac >-
    (first_x_assum (qspec_then `LAST (emitted_blocks st final) with
         <|bb_label := L; bb_instructions := MAP (\j. mk_inst j NOP [] []) ids ++
           DROP (LENGTH st.cs_current_insts) (LAST (emitted_blocks st final)).bb_instructions|>` mp_tac) >> simp[]) >>
  `!ys. DROP (LENGTH st.cs_current_insts) (MAP (\j. mk_inst j NOP [] []) ids ++ ys) = ys` by
    (qpat_assum `LENGTH ids = _` (fn th =>
       simp[NoAsms, GSYM th, SRULE [LENGTH_MAP]
         (Q.ISPEC `MAP (\j. mk_inst j NOP [] []) ids` DROP_LENGTH_APPEND)])) >>
  simp[emitted_insts_def] >>
  qpat_x_assum `st.cs_current_insts ≼ ready.cs_current_insts` mp_tac >>
  qpat_x_assum `ready.cs_current_insts ≼ _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> rpt strip_tac >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]
QED

Theorem setup_cut_shadow_step[local]:
  lookup_block L obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  s.vs_inst_idx < cut /\ ~s.vs_halted /\ ~v.vs_halted /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK v ==>
  abi_observer_step ctx obs (L,cut) (s with vs_current_bb := L)
    (v with <|vs_inst_idx := SUC s.vs_inst_idx; vs_current_bb := L|>) /\
  (!k. run_from k ctx obs (s with vs_current_bb := L) =
       run_from k ctx obs (v with <|vs_inst_idx := SUC s.vs_inst_idx; vs_current_bb := L|>))
Proof
  strip_tac >>
  `v.vs_prev_bb = s.vs_prev_bb` by
    (irule (cj 3 step_preserves_control_flow) >> metis_tac[step_inst_non_invoke]) >>
  `!w. w.vs_prev_bb = s.vs_prev_bb ==>
       (w with <|vs_current_bb := L; vs_prev_bb := s.vs_prev_bb|>) =
       (w with vs_current_bb := L)` by simp[venom_state_component_equality] >>
  drule_all frag_relabel_base_nonphi >> disch_then (qspecl_then [`s.vs_prev_bb`,`L`] mp_tac) >>
  simp[] >> strip_tac >> conj_tac >-
    (simp[abi_observer_step_def] >> qexists `v with vs_current_bb := L` >>
     simp[step_inst_non_invoke, venom_state_component_equality]) >>
  `lookup_block (s with vs_current_bb := L).vs_current_bb obs.fn_blocks = SOME bb /\
   get_instruction bb (s with vs_current_bb := L).vs_inst_idx = SOME i` by simp[] >>
  drule_all run_from_nonterm >> simp[step_inst_non_invoke]
QED

Theorem setup_cut_shadow_abort[local]:
  lookup_block L obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = Abort Revert_abort t ==>
  ?u k. frag_relabel_state L s.vs_current_bb u t /\
    run_from k ctx obs (s with vs_current_bb := L) = Abort Revert_abort u
Proof
  strip_tac >>
  drule_all frag_relabel_base_abort >> strip_tac >>
  `!b. (s with <|vs_current_bb := b; vs_prev_bb := s.vs_prev_bb|>) =
       (s with vs_current_bb := b)` by simp[venom_state_component_equality] >>
  `(s with vs_current_bb := s.vs_current_bb) = s` by simp[venom_state_component_equality] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (`t = (t with <|vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb|>)` by
       (qpat_x_assum `!p b. step_inst_base _ _ = _`
          (qspecl_then [`s.vs_prev_bb`,`s.vs_current_bb`] mp_tac) >> simp[]) >>
     pop_assum (mp_tac o AP_TERM ``\v:venom_state. v.vs_current_bb``) >> simp[]) >>
  qexistsl [`t with <|vs_current_bb := L; vs_prev_bb := s.vs_prev_bb|>`,`0`] >>
  conj_tac >-
    (simp[frag_relabel_state_def] >> qexists `t.vs_prev_bb` >>
     simp[venom_state_component_equality]) >>
  `step_inst 0 ctx i (s with vs_current_bb := L) =
    Abort Revert_abort (t with <|vs_current_bb := L; vs_prev_bb := s.vs_prev_bb|>)` by
    (simp[step_inst_non_invoke] >>
     qpat_x_assum `!p b. step_inst_base _ _ = _`
       (qspecl_then [`s.vs_prev_bb`,`L`] mp_tac) >> simp[]) >>
  `lookup_block (s with vs_current_bb := L).vs_current_bb obs.fn_blocks = SOME bb /\
   get_instruction bb (s with vs_current_bb := L).vs_inst_idx = SOME i` by simp[] >>
  drule_all run_from_nonterm >> simp[]
QED

val setup_shadow = ``\ctx obs L entry cut s r.
  (?t u. r = OK t /\ ~u.vs_halted /\ u.vs_current_bb = L /\
         u.vs_inst_idx = cut /\ frag_relabel_state L entry u t /\
         local_prefix ctx obs (L,cut) (s with vs_current_bb := L) u) \/
  (?t u k. r = Abort Revert_abort t /\ frag_relabel_state L entry u t /\
           run_from k ctx obs (s with vs_current_bb := L) = Abort Revert_abort u)``;

(* Use the exact selected path: STOP is a boundary, not a projection of
   the normal result (which would discard its return data). *)
Theorem setup_cut_replay[local]:
  !xs s n r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block L obs.fn_blocks = SOME shadow /\
    DROP s.vs_inst_idx bb.bb_instructions = xs ++ [mk_inst j STOP [] []] /\
    isPREFIX xs (DROP s.vs_inst_idx shadow.bb_instructions) /\
    s.vs_inst_idx + LENGTH xs = cut /\ ~s.vs_halted /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode) xs /\
    gas_path ctx fn s n r /\
    ((?t. r = OK t /\ t.vs_inst_idx = cut) \/ (?t. r = Abort Revert_abort t)) ==>
    (^setup_shadow) ctx obs L s.vs_current_bb cut s r
Proof
  Induct >- suspend "ready" >>
  simp_tac pure_ss [LENGTH, EVERY_DEF, APPEND, BETA_THM] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `DROP _ bb.bb_instructions = i::(xs ++ _)` >>
  `isPREFIX (i::xs) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  imp_res_tac abi_decode_contiguous_prefix_fetch >>
  drule_all bodyFullAbiDecodeCutEntryPhaseTheory.entry_phase_path_cons >> strip_tac
  >- (qpat_x_assum `(?t. _ = OK t /\ _) \/ _` mp_tac >> simp[])
  >- suspend "continue"
  >- suspend "reject" >>
  metis_tac[]
QED
Resume setup_cut_replay[ready]:
  simp_tac bool_ss [LENGTH, EVERY_DEF, APPEND, ADD_CLAUSES] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `isPREFIX [mk_inst j STOP [] []] (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule abi_decode_contiguous_prefix_fetch >> strip_tac >>
  drule_all bodyFullAbiDecodeCutEntryPhaseTheory.entry_phase_path_stop >> strip_tac
  >- (disj1_tac >> qexistsl [`s`, `s with vs_current_bb := L`] >>
      simp[cj 1 local_prefix_rules, frag_relabel_state_def] >>
      qexists `s.vs_prev_bb` >> simp[venom_state_component_equality]) >>
  metis_tac[exec_result_distinct]
QED
Resume setup_cut_replay[continue]:
  `v.vs_current_bb = s.vs_current_bb` by metis_tac[step_inst_non_invoke, step_preserves_control_flow] >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs ++ [mk_inst j STOP [] []]` by
    (Q_TAC (TRANS_TAC EQ_TRANS) `DROP 1 (DROP s.vs_inst_idx bb.bb_instructions)` >>
     conj_tac >- simp[NoAsms, DROP_DROP_T, ADD1, ADD_COMM] >> simp[]) >>
  `s.vs_inst_idx < cut` by decide_tac >>
  drule_all setup_cut_shadow_step >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  first_x_assum (qspec_then `v with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`m`, `r`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac
  >- (disj1_tac >> qexistsl [`t`, `u`] >>
      conj_tac >- first_assum ACCEPT_TAC >> simp[] >>
      irule (cj 2 local_prefix_rules) >> goal_assum (drule_at Any) >> gvs[]) >>
  disj2_tac >> qexistsl [`t`, `u`, `k`] >> metis_tac[]
QED
Resume setup_cut_replay[reject]:
  `a = Revert_abort` by metis_tac[exec_result_distinct, exec_result_11] >>
  gvs[] >> drule_all setup_cut_shadow_abort >> simp[]
QED
Finalise setup_cut_replay

Theorem setup_cut_nonphi[local]:
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
  pure_rewrite_tac [GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

(* Specialize the all-observers path to the one-block setup observation.
   The trailing STOP bounds replay; the replay does not execute it. *)
Theorem setup_cut_from_observed_path[local]:
  abi_builtin_decode_setup data mn mx outsz st = (ops,ready) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_block L obs.fn_blocks = SOME shadow /\
  isPREFIX (emitted_insts st ready) (DROP s.vs_inst_idx shadow.bb_instructions) /\
  (!o'. fn_has_code st ready o' ==> gas_path ctx o' s 0 r) /\
  ((?t. r = OK t /\ t.vs_inst_idx = LENGTH ready.cs_current_insts) \/
   (?t. r = Abort Revert_abort t)) ==>
  (^setup_shadow) ctx obs L st.cs_current_bb (LENGTH ready.cs_current_insts) s r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule setup_cut_nonphi >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  qabbrev_tac `bb = <|bb_label := ready.cs_current_bb;
                       bb_instructions := ready.cs_current_insts ++ [mk_inst 0 STOP [] []]|>` >>
  qabbrev_tac `source = (ARB : ir_function) with fn_blocks := [bb]` >>
  `lookup_block ready.cs_current_bb source.fn_blocks = SOME bb` by
    simp[Abbr `source`, Abbr `bb`, lookup_block_def, FIND_thm] >>
  `fn_has_code st ready source` by
    simp[fn_has_code_def, emitted_blocks_def, Abbr `bb`, IS_PREFIX_APPEND] >>
  `gas_path ctx source s 0 r` by metis_tac[] >>
  qpat_assum `s.vs_current_bb = st.cs_current_bb` (SUBST1_TAC o SYM) >>
  irule setup_cut_replay >> simp_tac pure_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`bb`, `source`, `0`, `0`, `shadow`, `emitted_insts st ready`] >>
  simp[Abbr `bb`, EVERY_MEM] >>
  qpat_x_assum `st.cs_current_insts ≼ ready.cs_current_insts` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  conj_tac >-
    (asm_rewrite_tac[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  conj_tac >- simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  conj_tac >- gvs[] >>
  gvs[EVERY_MEM]
QED

(* Reuse the setup post verbatim, including the same outcome and ghosts. *)
val (cut_pre, origin_post) = dest_imp (snd (strip_forall
  (concl abi_decode_caller_setup_origin_observed)));
val (cut_witnesses, cut_core) = strip_exists origin_post;
val cut_r = hd cut_witnesses;
val cut_extra = ``
  cs_extends st final /\ cs_extends ready final /\ fn_has_code st final fn /\
  st.cs_blocks <> final.cs_blocks /\ st.cs_current_bb = final.cs_current_bb /\
  LENGTH ids = LENGTH st.cs_current_insts /\ L <> final.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks st final)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code st final) /\
  frag_gas_free (start_relabel L ids st) (start_swap st L ids final) /\
  fn_has_code (start_relabel L ids st) (start_swap st L ids final) obs /\
  fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts fn)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  (!bb. lookup_block final.cs_current_bb obs.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)``;
val cut_post = list_mk_exists (cut_witnesses, ``^cut_core /\
  (^setup_shadow) ctx obs L st.cs_current_bb (LENGTH ready.cs_current_insts) s ^cut_r``);
val cut_stmt = ``let obs = frag_relabel_observer st final L ids fn id in
  (^cut_pre /\ ^cut_extra) ==> ^cut_post``;

Theorem abi_decode_caller_setup_cut:
  ^(list_mk_forall (free_vars cut_stmt, cut_stmt))
Proof
  simp_tac pure_ss [LET_THM, BETA_THM] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS) assume_tac)
    (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (SPEC_ALL (BETA_RULE abi_decode_caller_setup_origin_observed)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gs` (qx_choose_then `ts`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl [`r`, `Gs`, `ts`] >>
  (conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  drule_all setup_cut_entry_prefix >>
  disch_then (qx_choose_then `shadow` (map_every assume_tac o CONJUNCTS)) >>
  irule (BETA_RULE setup_cut_from_observed_path) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- goal_assum (drule_at Any) >>
  qpat_x_assum `(?t. r = Abort Revert_abort t) \/ _`
    (DISJ_CASES_THEN2 assume_tac
      (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)))
  >- (disj2_tac >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexists `t` >>
  qpat_x_assum `?output input. ~t.vs_halted /\ _`
    (qx_choose_then `output` (qx_choose_then `input` (map_every assume_tac o CONJUNCTS))) >>
  simp[]
QED
