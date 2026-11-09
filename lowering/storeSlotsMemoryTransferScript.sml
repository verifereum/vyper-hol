(* Execution agreement and memory-safe transport for sparse stores. *)
Theory storeSlotsMemoryTransfer
Ancestors
  storeSlotsObserverMemory storeSlotsMemoryFootprint storeSlotsMemoryPaths exprSimAbiGasBridge abiEncoderPrefixSafety
  fragGasPath fragGasPathMem gasCount abiEncoderObserver fragExec venomState list
  simplifyCfgMergeRuns memSafeRun exprSimHash placeStoreSlots placeStoreStorage

Theorem observer_nonstart_phi_zero[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  lbl <> sa.cs_current_bb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> Cases_on `bb.bb_instructions`
  >- simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  rename1 `bb.bb_instructions = inst::rest` >>
  Cases_on `(lbl,0) = frag_observer_cut sb`
  >- (gvs[frag_observer_cut_def] >>
      drule frag_observer_lookup_cases >> strip_tac >>
      gvs[venomInstTheory.mk_inst_def,
          venomExecSemanticsTheory.phi_prefix_length_def]) >>
  `get_instruction bb 0 = SOME inst` by simp[venomInstTheory.get_instruction_def] >>
  `(lbl,0) IN frag_observer_region sa sb` by
    (drule frag_observer_lookup_cases >> strip_tac >>
     simp[frag_observer_region_def, MEM_MAP] >> metis_tac[]) >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem gas_path_stop_view_agreement:
  gas_path ctx fn s n (OK t) /\ gas_path ctx fn s m (OK u) /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME ub /\
  get_instruction ub u.vs_inst_idx = SOME (mk_inst uid STOP [] []) ==>
  stop_view t = stop_view u
Proof
  strip_tac >>
  `run_from 0 ctx fn t = Halt (stop_view t)` by
    (irule run_from_stop_view >> metis_tac[]) >>
  `run_from 0 ctx fn u = Halt (stop_view u)` by
    (irule run_from_stop_view >> metis_tac[]) >>
  `?a. run_from a ctx fn s = Halt (stop_view t)` by
    (qpat_assum `gas_path _ _ _ _ (OK t)` (mp_tac o MATCH_MP gas_path_normal) >>
     disch_then (mp_tac o CONJUNCT2) >>
     disch_then (qspecl_then [`0`, `Halt (stop_view t)`] mp_tac) >> simp[]) >>
  `?b. run_from b ctx fn s = Halt (stop_view u)` by
    (qpat_assum `gas_path _ _ _ _ (OK u)` (mp_tac o MATCH_MP gas_path_normal) >>
     disch_then (mp_tac o CONJUNCT2) >>
     disch_then (qspecl_then [`0`, `Halt (stop_view u)`] mp_tac) >> simp[]) >>
  `run_from (a+b) ctx fn s = Halt (stop_view t)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `a` >> simp[]) >>
  `run_from (a+b) ctx fn s = Halt (stop_view u)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `b` >> simp[]) >>
  gvs[]
QED

Theorem observer_safe_step_path[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s t /\
  (!bb inst.
    lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==> mem_safe_step 0 ctx inst s) ==>
  gas_path_mem ctx fn s 0 (OK t)
Proof
  strip_tac >>
  `gas_path_mem_edge ctx fn s 0 (OK t)` suffices_by
    (strip_tac >>
     once_rewrite_tac[GSYM (CONJUNCT1 arithmeticTheory.ADD)] >>
     irule (cj 2 gas_path_mem_rules) >>
     qexists_tac `t` >> simp[] >>
     irule (cj 1 gas_path_mem_rules) >>
     gvs[abi_observer_step_def]) >>
  qpat_x_assum `abi_observer_step _ _ _ _ _` mp_tac >>
  rw[abi_observer_step_def] >>
  `inst.inst_opcode <> GAS` by metis_tac[frag_observer_off_cut_opcodes] >>
  `?original. lookup_block s.vs_current_bb fn.fn_blocks = SOME original /\
    get_instruction original s.vs_inst_idx = SOME inst` by
    (irule frag_observer_instruction_agrees >> metis_tac[]) >>
  `mem_safe_step 0 ctx inst s` by metis_tac[] >>
  simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
  simp[gas_count_step_def]
  >- gvs[] >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[scfg_terminator_jump] >>
  `middle.vs_current_bb <> sa.cs_current_bb` by
    (irule frag_observer_jump_no_reentry >>
     qexistsl_tac [`inst`, `s`] >>
     metis_tac[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  `phi_prefix_length target.bb_instructions = 0` by
    (irule observer_nonstart_phi_zero >> metis_tac[]) >>
  `entered = middle` by gvs[eval_phis_no_phi] >>
  `middle = jump_to middle.vs_current_bb s` by
    metis_tac[scfg_terminator_jump] >>
  disj2_tac >> disj1_tac >> qexists_tac `middle.vs_current_bb` >>
  simp[venomStateTheory.jump_to_def] >>
  qpat_assum `middle = jump_to _ _`
    (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  fs[venomStateTheory.jump_to_def]
QED

Theorem observer_safe_prefix_path:
  !ctx observed cut s t. local_prefix ctx observed cut s t ==>
  !sa sb fn id I.
    observed = frag_observer sa sb fn id /\ cut = frag_observer_cut sb /\
    cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
    (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\ I s /\
    (!u v. I u /\
      (u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region sa sb /\
      abi_observer_step ctx observed cut u v ==> I v) /\
    (!u bb inst. I u /\
      (u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region sa sb /\
      (u.vs_current_bb,u.vs_inst_idx) <> cut /\
      lookup_block u.vs_current_bb observed.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME inst ==>
      mem_safe_step 0 ctx inst u) ==>
    gas_path_mem ctx fn s 0 (OK t)
Proof
  ho_match_mp_tac local_prefix_ind >> rpt strip_tac
  >- (irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  rename1 `abi_observer_step ctx observed cut s middle` >> gvs[] >>
  `gas_path_mem ctx fn s 0 (OK middle)` by
    (irule observer_safe_step_path >> qexistsl_tac [`id`, `sa`, `sb`] >>
     simp[] >> rpt strip_tac >>
     first_assum irule >>
     simp[] >> metis_tac[abi_observer_step_def]) >>
  `I' middle` by metis_tac[] >>
  `(middle.vs_current_bb,middle.vs_inst_idx) IN frag_observer_region sa sb` by
    (drule_all frag_observer_region_closed >>
     simp[observer_region_closed_def] >> metis_tac[]) >>
  `gas_path_mem ctx fn middle 0 (OK t)` by
    (first_x_assum irule >> metis_tac[]) >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem store_slots_stop_view_post:
  ~u.vs_halted /\ ~t.vs_halted /\ stop_view u = stop_view t /\
  stmt_state_rel ctx fn cenv cx ee t /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  stmt_state_rel ctx fn cenv cx ee u /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all stop_view_recover >> strip_tac >>
  qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
  fs[hash_returndata_state_rel, venomStateTheory.lookup_var_def]
QED

Theorem store_slots_semantic_endpoint:
  evaluate_type (get_tenv cx) dty = SOME tv /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx fn cenv cx ee s /\
  local_ptrs_reserved cenv sa /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\
  value_has_type tv v /\ start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore)
      (n2w start + n2w j) (mload (w2n sw + 32*j) s) q) s ks /\
  (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx fn cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t
Proof
  strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  qpat_x_assum `start = _` SUBST_ALL_TAC >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `store_copy_normalize _ _ = _` SUBST1_TAC >>
  pure_rewrite_tac [wordsTheory.word_add_n2w] >>
  ho_match_mp_tac place_store_encoded_leaf_state_sparse >>
  goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qexistsl_tac [`path`, `delta`, `tv`, `v`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> irule place_store_memory_live_at >>
  metis_tac[]
QED

(* Raw execution is in the observer; all semantic relations use fn. *)
Theorem store_slots_observer_semantic_post:
  store_slots_entry cenv ctx dty tv v /\
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  fn_has_code sa sb (frag_observer sa sb fn id) /\
  fn_inst_ids_distinct (frag_observer sa sb fn id) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx fn cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  gas_path ctx (frag_observer sa sb fn id) s n (OK u) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  stmt_state_rel ctx fn cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) u /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  qpat_x_assum `store_slots_entry _ _ _ _ _` mp_tac >>
  rewrite_tac[store_slots_entry_def] >>
  disch_then (qspecl_then [`src`, `dst`, `tr`, `sa`, `sb`,
    `frag_observer sa sb fn id`, `s`, `sw`, `n2w start`, `writes`] mp_tac) >>
  (impl_tac >- (simp[wordsTheory.w2n_n2w] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`t`, `ks`] strip_assume_tac) >>
  `stmt_state_rel ctx fn cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t` by
    (drule_all store_slots_semantic_endpoint >> simp[]) >>
  `stop_view u = stop_view t` by
    (fs[fragGasModeTheory.gas_marked_path_def] >>
     irule gas_path_stop_view_agreement >>
     goal_assum (drule_at (Pat `gas_path _ _ _ _ (OK u)`)) >>
     goal_assum (drule_at (Pat `gas_path _ _ _ _ (OK t)`)) >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction] >>
     qexistsl_tac [`id`, `id`] >> simp[]) >>
  irule store_slots_stop_view_post >> metis_tac[]
QED
