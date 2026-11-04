Theory loadElimCounterexample
Ancestors
  loadElimDefs venomExecSemantics venomState venomInst loadElimByteHelpers
  venomWf dfgCorrectnessProof memoryCopyElisionSound cfgTransform
  basePtrDefs memLocDefs venomMemDefs venomMemProps stateEquiv

Definition ce_bb_def:
  ce_bb = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 MLOAD [Lit 0w] ["x"];
     mk_inst 1 MSTORE [Lit 0w; Var "x"] [];
     mk_inst 2 MEMTOP [] ["y"];
     mk_inst 3 STOP [] []] |>
End

Definition ce_fn_def:
  ce_fn = mk_raw_function "ce" [ce_bb]
End

Definition ce_s_def:
  ce_s = init_venom_state "entry"
End

Definition ce_ctx_def:
  ce_ctx = mk_venom_context [] NONE
End

Definition ce_target_def:
  ce_target = mk_raw_function "ce"
    [ce_bb with bb_instructions :=
      [mk_inst 0 MLOAD [Lit 0w] ["x"];
       mk_inst 2 MEMTOP [] ["y"];
       mk_inst 3 STOP [] []]]
End

Definition ce_cfg_def:
  ce_cfg = cfg_analyze ce_fn
End

Theorem ce_cfg_compute:
  ce_cfg = <| cfg_succs := FEMPTY |+ ("entry", []);
              cfg_preds := FEMPTY |+ ("entry", []);
              cfg_dfs_pre := ["entry"];
              cfg_dfs_post := ["entry"];
              cfg_reachable := FEMPTY |+ ("entry", T) |>
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED
Theorem ce_source_run:
  run_blocks 2 ce_ctx ce_fn ce_s =
    Halt (ce_s with <| vs_vars := FEMPTY |+ ("x",0w) |+ ("y",32w);
                       vs_memory := REPLICATE 32 0w;
                       vs_inst_idx := 3; vs_halted := T |>)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``word_of_bytes``, ``word_to_bytes_aux``]) >>
  simp[wordsTheory.w2n_n2w, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  rewrite_tac[GSYM (EVAL ``REPLICATE 32 (0w:8 word)``)] >>
  simp[word_of_bytes_zero_256, word_to_bytes_aux_zero,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC
QED

Theorem ce_target_run:
  run_blocks 2 ce_ctx ce_target ce_s =
    Halt (ce_s with <| vs_vars := FEMPTY |+ ("x",0w) |+ ("y",0w);
                       vs_inst_idx := 2; vs_halted := T |>)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``word_of_bytes``, ``word_to_bytes_aux``]) >>
  simp[wordsTheory.w2n_n2w, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  rewrite_tac[GSYM (EVAL ``REPLICATE 32 (0w:8 word)``)] >>
  simp[word_of_bytes_zero_256, word_to_bytes_aux_zero,
       fcpLib.INDEX_CONV ``dimindex (:256)``] >> EVAL_TAC
QED

Theorem ce_bp_compute:
  bp_analyze ce_cfg ce_fn = FEMPTY
Proof
  EVAL_TAC
QED

Definition ce_dfg_def:
  ce_dfg = <| dfg_uses := FEMPTY |+ ("x", [mk_inst 1 MSTORE [Lit 0w; Var "x"] []]);
    dfg_defs := FEMPTY |+ ("x", mk_inst 0 MLOAD [Lit 0w] ["x"])
                       |+ ("y", mk_inst 2 MEMTOP [] ["y"]);
    dfg_ids := FEMPTY |+ (0, mk_inst 0 MLOAD [Lit 0w] ["x"])
                     |+ (1, mk_inst 1 MSTORE [Lit 0w; Var "x"] [])
                     |+ (2, mk_inst 2 MEMTOP [] ["y"])
                     |+ (3, mk_inst 3 STOP [] []) |>
End

Theorem ce_dfg_compute:
  dfg_build_function ce_fn = ce_dfg
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_COMMUTES]
QED

Definition ce_loc_def:
  ce_loc = <| ml_offset := SOME 0; ml_size := SOME 32;
              ml_alloca := NONE; ml_volatile := F |>
End

Theorem ce_mem_alias_compute:
  memory_alias_analyze FEMPTY ce_fn = FEMPTY |+ (ce_loc, [ce_loc; ce_loc; ce_loc])
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                   fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_other_alias_compute:
  storage_alias_analyze FEMPTY ce_fn = FEMPTY /\
  transient_alias_analyze FEMPTY ce_fn = FEMPTY
Proof
  EVAL_TAC
QED

Definition ce_mem_ctx_def:
  ce_mem_ctx = mk_load_context FEMPTY
    (FEMPTY |+ (ce_loc, [ce_loc; ce_loc; ce_loc])) ce_dfg memory_config
End

Definition ce_known_def:
  ce_known = SOME (FEMPTY |+ (LK_Loc ce_loc, [Var "x"]))
End

Definition ce_mem_result_def:
  ce_mem_result = <|
    ds_inst := FEMPTY |+ (("entry",0), SOME FEMPTY)
                     |+ (("entry",1), ce_known)
                     |+ (("entry",2), ce_known)
                     |+ (("entry",3), ce_known)
                     |+ (("entry",4), ce_known);
    ds_boundary := FEMPTY |+ ("entry",SOME FEMPTY) |>
End

Theorem ce_mem_analyze:
  load_analyze ce_mem_ctx ce_fn = ce_mem_result
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                   fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem ce_mem_actions:
  collect_phi_actions 3 ce_mem_ctx ce_cfg ce_mem_result ce_fn = []
Proof
  EVAL_TAC
QED

Definition ce_fn1_def:
  ce_fn1 = mk_raw_function "ce"
    [ce_bb with bb_instructions :=
      [mk_inst 0 MLOAD [Lit 0w] ["x"];
       mk_inst 1 NOP [] [];
       mk_inst 2 MEMTOP [] ["y"];
       mk_inst 3 STOP [] []]]
End

Theorem ce_mem_round:
  load_elim_one ce_mem_ctx ce_cfg ce_fn = ce_fn1
Proof
  simp[load_elim_one_def, ce_mem_analyze] >>
  `fn_max_inst_id ce_fn = 3` by EVAL_TAC >>
  simp[ce_mem_actions] >>
  EVAL_TAC >> simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def,
                   fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  EVAL_TAC
QED

Theorem ce_transient_round:
  load_elim_one
    (mk_load_context FEMPTY FEMPTY (dfg_build_function ce_fn1) transient_config)
    ce_cfg ce_fn1 = ce_fn1
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_storage_round:
  load_elim_one
    (mk_load_context FEMPTY FEMPTY (dfg_build_function ce_fn1) storage_config)
    ce_cfg ce_fn1 = ce_fn1
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_dload_round:
  load_elim_one
    (mk_load_context FEMPTY (FEMPTY |+ (ce_loc,[ce_loc;ce_loc;ce_loc]))
      (dfg_build_function ce_fn1) dload_config)
    ce_cfg ce_fn1 = ce_fn1
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_calldata_round:
  load_elim_one
    (mk_load_context FEMPTY (FEMPTY |+ (ce_loc,[ce_loc;ce_loc;ce_loc]))
      (dfg_build_function ce_fn1) calldataload_config)
    ce_cfg ce_fn1 = ce_fn1
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem ce_clear_nops:
  clear_nops_function ce_fn1 = ce_target
Proof
  EVAL_TAC
QED

Theorem ce_transform:
  load_elim_function ce_fn = ce_target
Proof
  simp[load_elim_function_def, GSYM ce_cfg_def,
       ce_bp_compute, ce_mem_alias_compute, ce_other_alias_compute,
       ce_dfg_compute, GSYM ce_mem_ctx_def, ce_mem_round,
       ce_transient_round, ce_storage_round, ce_dload_round,
       ce_calldata_round, ce_clear_nops]
QED

Theorem ce_structural_wf:
  wf_function ce_fn /\ fn_inst_wf ce_fn /\ ssa_form ce_fn /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars ce_fn) /\
  ce_s.vs_inst_idx = 0 /\
  fn_entry_label ce_fn = SOME ce_s.vs_current_bb
Proof
  EVAL_TAC
QED

Theorem ce_dominates_self:
  fn_dominates ce_fn "entry" "entry"
Proof
  simp[fn_dominates_def, fn_reachable_def, ce_fn_def, ce_bb_def,
       mk_raw_function_def, fn_entry_label_def, entry_block_def,
       relationTheory.RTC_REFL] >>
  rpt strip_tac >>
  Cases_on `path` >> gvs[]
QED

Theorem ce_wf_ssa:
  wf_ssa ce_fn
Proof
  simp[wf_ssa_def, ce_structural_wf, def_dominates_uses_def] >>
  simp[ce_fn_def, ce_bb_def, mk_raw_function_def, mk_inst_def,
       def_available_at_def] >>
  simp[GSYM ce_fn_def, GSYM ce_bb_def, GSYM mk_inst_def,
       ce_dominates_self] >>
  rpt strip_tac >> gvs[mk_inst_def] >>
  qexists `mk_inst 0 MLOAD [Lit 0w] ["x"]` >>
  simp[mk_inst_def] >>
  conj_tac >- (mp_tac ce_dominates_self >>
              simp[ce_fn_def, ce_bb_def, mk_raw_function_def]) >>
  qexistsl [`0`, `1`] >> simp[]
QED

Theorem ce_dfg_sound:
  !s. dfg_assigns_sound ce_dfg s
Proof
  simp[dfg_assigns_sound_def, ce_dfg_def, finite_mapTheory.FLOOKUP_UPDATE,
       mk_inst_def] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ce_bp_stable:
  bp_assigns_stable FEMPTY ce_dfg
Proof
  simp[bp_assigns_stable_def, ce_dfg_def, finite_mapTheory.FLOOKUP_UPDATE,
       mk_inst_def] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ce_bp_sound:
  !s. bp_ptr_sound FEMPTY s /\ bp_phis_closed FEMPTY ce_fn
Proof
  simp[bp_ptr_sound_def, bp_phis_closed_def, bp_get_ptrs_def]
QED

Theorem ce_bp_bounded:
  !s. bp_ptrs_bounded FEMPTY ce_fn s
Proof
  simp[bp_ptrs_bounded_def, ce_fn_def, ce_bb_def, mk_raw_function_def] >>
  rpt strip_tac >> gvs[mk_inst_def, mem_write_ops_def, mem_read_ops_def,
                       bp_segment_from_ops_def]
QED

Theorem ce_initial_allocas:
  alloca_inv ce_s /\ allocas_in_word ce_s /\
  LENGTH ce_s.vs_memory < dimword (:256)
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       allocas_in_word_def, ce_s_def, init_venom_state_def,
       wordsTheory.dimword_def]
QED

Theorem ce_step_allocas:
  !fuel ctx inst s s'.
    MEM inst ce_bb.bb_instructions /\ step_inst fuel ctx inst s = OK s' ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >> irule step_inst_non_alloca_preserves_allocas >>
  goal_assum (drule_at Any) >>
  gvs[ce_bb_def, mk_inst_def, is_alloca_op_def]
QED

Theorem ce_step_preserves:
  !fuel ctx bb inst s0 s1.
    MEM bb ce_fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst_wf inst /\
    dfg_assigns_sound ce_dfg (s0 with vs_inst_idx := 0) /\
    bp_ptr_sound FEMPTY (s0 with vs_inst_idx := 0) /\
    allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
    allocas_in_word (s0 with vs_inst_idx := 0) /\
    bp_ptrs_bounded FEMPTY ce_fn (s0 with vs_inst_idx := 0) /\
    step_inst fuel ctx inst s0 = OK s1 ==>
    dfg_assigns_sound ce_dfg (s1 with vs_inst_idx := 0) /\
    bp_ptr_sound FEMPTY (s1 with vs_inst_idx := 0) /\
    allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
    allocas_in_word (s1 with vs_inst_idx := 0) /\
    bp_ptrs_bounded FEMPTY ce_fn (s1 with vs_inst_idx := 0)
Proof
  simp[ce_dfg_sound, ce_bp_sound, ce_bp_bounded,
       ce_fn_def, mk_raw_function_def] >>
  rpt strip_tac >>
  `s1.vs_allocas = s0.vs_allocas` by
    (irule ce_step_allocas >> goal_assum (drule_at Any) >> simp[]) >>
  fs[allocas_non_overlapping_def, allocas_in_word_def] >>
  metis_tac[]
QED

Theorem ce_phi_preserves:
  !bb s0 s_phi.
    MEM bb ce_fn.fn_blocks /\
    MEM bb.bb_label ce_cfg.cfg_dfs_pre /\
    eval_phis s0 bb.bb_instructions = OK s_phi /\
    dfg_assigns_sound ce_dfg s0 ==>
    dfg_assigns_sound ce_dfg s_phi
Proof
  simp[ce_dfg_sound]
QED

Theorem ce_antecedent:
    wf_function ce_fn /\
    fn_inst_wf ce_fn /\
    wf_ssa ce_fn /\
    EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars ce_fn) /\
    ce_s.vs_inst_idx = 0 /\
    fn_entry_label ce_fn = SOME ce_s.vs_current_bb /\
    dfg_assigns_sound (dfg_build_function ce_fn) ce_s /\
    bp_ptr_sound (bp_analyze (cfg_analyze ce_fn) ce_fn) ce_s /\
    alloca_inv ce_s /\
    allocas_in_word ce_s /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze ce_fn) ce_fn) ce_fn ce_s /\
    bp_phis_closed (bp_analyze (cfg_analyze ce_fn) ce_fn) ce_fn /\
    bp_assigns_stable (bp_analyze (cfg_analyze ce_fn) ce_fn) (dfg_build_function ce_fn) /\
    (!bb s0 s_phi.
       MEM bb ce_fn.fn_blocks /\
       MEM bb.bb_label (cfg_analyze ce_fn).cfg_dfs_pre /\
       eval_phis s0 bb.bb_instructions = OK s_phi /\
       dfg_assigns_sound (dfg_build_function ce_fn) s0 ==>
       dfg_assigns_sound (dfg_build_function ce_fn) s_phi) /\
    (!fuel' run_ctx bb inst s0 s1.
       MEM bb ce_fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       inst_wf inst /\
       dfg_assigns_sound (dfg_build_function ce_fn) (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound (bp_analyze (cfg_analyze ce_fn) ce_fn) (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze ce_fn) ce_fn) ce_fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst s0 = OK s1 ==>
       dfg_assigns_sound (dfg_build_function ce_fn) (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound (bp_analyze (cfg_analyze ce_fn) ce_fn) (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze ce_fn) ce_fn) ce_fn (s1 with vs_inst_idx := 0)) /\
    LENGTH ce_s.vs_memory < dimword (:256)
Proof
  rewrite_tac[GSYM ce_cfg_def, ce_bp_compute, ce_dfg_compute] >>
  simp[ce_structural_wf, ce_wf_ssa, ce_initial_allocas,
       ce_dfg_sound, ce_bp_sound, ce_bp_stable, ce_bp_bounded] >>
  mp_tac ce_step_preserves >>
  simp[ce_dfg_sound, ce_bp_sound, ce_bp_bounded]
QED

Theorem ce_conclusion_false:
  ~((?e. run_blocks 2 ce_ctx ce_fn ce_s = Error e) \/
    lift_result (state_equiv {v | isPREFIX "$le_phi_" v})
      (execution_equiv {v | isPREFIX "$le_phi_" v})
      (execution_equiv {v | isPREFIX "$le_phi_" v})
      (run_blocks 2 ce_ctx ce_fn ce_s)
      (run_blocks 2 ce_ctx (load_elim_function ce_fn) ce_s))
Proof
  rewrite_tac[ce_transform, ce_source_run, ce_target_run,
              lift_result_def] >>
  simp[execution_equiv_def] >>
  strip_tac >> qexists `"y"` >>
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

(* Exact negation of the frozen universal statement. *)
Theorem load_elim_function_correct_counterexample:
  ~(!fuel ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    wf_ssa fn /\
    EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_assigns_sound (dfg_build_function fn) s /\
    bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
    alloca_inv s /\
    allocas_in_word s /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
    bp_phis_closed (bp_analyze (cfg_analyze fn) fn) fn /\
    bp_assigns_stable (bp_analyze (cfg_analyze fn) fn) (dfg_build_function fn) /\
    (!bb s0 s_phi.
       MEM bb fn.fn_blocks /\
       MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
       eval_phis s0 bb.bb_instructions = OK s_phi /\
       dfg_assigns_sound (dfg_build_function fn) s0 ==>
       dfg_assigns_sound (dfg_build_function fn) s_phi) /\
    (!fuel' run_ctx bb inst s0 s1.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       inst_wf inst /\
       dfg_assigns_sound (dfg_build_function fn) (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst s0 = OK s1 ==>
       dfg_assigns_sound (dfg_build_function fn) (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn (s1 with vs_inst_idx := 0)) /\
    LENGTH s.vs_memory < dimword (:256) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {v | isPREFIX "$le_phi_" v})
      (execution_equiv {v | isPREFIX "$le_phi_" v})
      (execution_equiv {v | isPREFIX "$le_phi_" v})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (load_elim_function fn) s))
Proof
  strip_tac >>
  first_x_assum (qspecl_then [`2`, `ce_ctx`, `ce_fn`, `ce_s`] mp_tac) >>
  rewrite_tac[ce_antecedent] >>
  metis_tac[ce_conclusion_false]
QED

(* Repair boundary for this counterexample (not a claim of full correctness):
   a redundant MSTORE at offset a may only be removed if a + 32 is no
   greater than the current memory length, as well as writing the known value.
   A pure MLOAD does not establish this no-expansion condition. *)
