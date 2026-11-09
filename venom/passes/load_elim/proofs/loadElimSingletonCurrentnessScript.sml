Theory loadElimSingletonCurrentness
Ancestors
  loadElimSingletonSuffix loadElimConfiguredGeneration loadElimGenerationSound
  loadElimRetainedStore loadElimNoWriteRead loadElimOccurrenceRead
  loadElimTransferRetention loadElimKeyShapeInvariant loadElimKeyRead
  loadElimKeyReadOperational loadElimAbsoluteKey
  loadElimSolverProvenance loadElimActualGeneration loadElimOccurrence
  dfAnalyzeDefs cfgDefs rich_list venomExecProofs venomExecProps
  loadElimDefs loadElimTransferProvenance dfgCorrectnessProof loadElimOperandValidity
  venomExecSemantics venomState venomEffects venomInst
  finite_map list pred_set words passSharedProps venomWf

Theorem le_mutable_no_write_read:
  MEM (space,eff) [(AddrSp_Memory,Eff_MEMORY);
    (AddrSp_Storage,Eff_STORAGE); (AddrSp_Transient,Eff_TRANSIENT)] /\
  step_inst fuel C inst s = OK t /\
  eff NOTIN write_effects inst.inst_opcode ==>
  le_read_address space a t = le_read_address space a s
Proof
  simp[] >> strip_tac >> gvs[]
  >- (drule_all le_memory_read_no_write_step >> simp[])
  >- (drule_all le_storage_read_no_write_step >> simp[]) >>
  drule_all le_transient_read_no_write_step >> simp[]
QED

Theorem le_configured_mutable_store_exists:
  le_configured_context ctx /\
  MEM ctx.lctx_addr_space [AddrSp_Memory;AddrSp_Storage;AddrSp_Transient] ==>
  ?st. ctx.lctx_config.lc_store = SOME st
Proof
  simp[le_configured_context_def] >> strip_tac >>
  gvs[memory_config_def, storage_config_def, transient_config_def,
      dload_config_def, calldataload_config_def]
QED

Theorem le_configured_load_no_mutable_write:
  le_configured_context ctx /\ inst.inst_opcode = ctx.lctx_config.lc_load /\
  MEM (ctx.lctx_addr_space,eff) [(AddrSp_Memory,Eff_MEMORY);
    (AddrSp_Storage,Eff_STORAGE); (AddrSp_Transient,Eff_TRANSIENT)] ==>
  eff NOTIN write_effects inst.inst_opcode
Proof
  strip_tac >> drule_all le_configured_load_opcode >>
  simp[] >> strip_tac >> gvs[write_effects_def, empty_effects_def]
QED

Theorem le_configured_retained_other_read:
  le_configured_context ctx /\
  MEM ctx.lctx_addr_space [AddrSp_Memory;AddrSp_Storage;AddrSp_Transient] /\
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) key = SOME ops /\
  ctx.lctx_config.lc_store <> SOME inst.inst_opcode /\
  step_inst fuel C inst s = OK t ==>
  le_read_address ctx.lctx_addr_space a t = le_read_address ctx.lctx_addr_space a s
Proof
  strip_tac >> drule_all le_configured_mutable_store_exists >> strip_tac >>
  Cases_on `inst.inst_opcode = ctx.lctx_config.lc_load`
  >- (`?eff. MEM (ctx.lctx_addr_space,eff)
        [(AddrSp_Memory,Eff_MEMORY); (AddrSp_Storage,Eff_STORAGE);
         (AddrSp_Transient,Eff_TRANSIENT)]` by (gvs[] >> simp[]) >>
      drule_all le_configured_load_no_mutable_write >> strip_tac >>
      drule_all le_mutable_no_write_read >> simp[]) >>
  `inst.inst_opcode <> st` by metis_tac[] >>
  drule_all le_retained_nonstore_no_write_effect >> strip_tac >>
  gvs[]
  >- (drule_all le_memory_read_no_write_step >> simp[])
  >- (drule_all le_storage_read_no_write_step >> simp[]) >>
  drule_all le_transient_read_no_write_step >> simp[]
QED

Theorem le_configured_retained_step_read_local:
  le_configured_context ctx /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  le_inst_operands_valid ctx.lctx_dfg inst s /\ inst_wf inst /\
  le_absolute_key ctx.lctx_addr_space key /\
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) key = SOME ops /\
  (!op. ops = [op] ==> ~le_transfer_generates ctx inst key op) /\
  le_key_address ctx.lctx_addr_space key s = SOME a /\ a < dimword (:256) /\
  step_inst fuel C inst s = OK t ==>
  le_read_address ctx.lctx_addr_space a t = le_read_address ctx.lctx_addr_space a s
Proof
  strip_tac >>
  Cases_on `MEM ctx.lctx_addr_space [AddrSp_Memory;AddrSp_Storage;AddrSp_Transient]`
  >- (Cases_on `ctx.lctx_config.lc_store = SOME inst.inst_opcode`
      >- (drule_all le_configured_store_opcode >> strip_tac >>
          `inst.inst_opcode IN {MSTORE;MSTORE8;SSTORE;TSTORE}` by gvs[] >>
          drule_all inst_wf_store_shape >> strip_tac >>
          drule_all le_generating_store_address_exists >> strip_tac >>
          `eval_operand (normalize_operand ctx.lctx_dfg [] op1) s = SOME w` by
            metis_tac[le_inst_operands_valid_eval, MEM] >>
          `inst.inst_opcode <> ctx.lctx_config.lc_load` by
            (spose_not_then assume_tac >>
             drule_all le_configured_load_opcode >> gvs[]) >>
          `key IN FDOM (load_invalidate ctx.lctx_aliases ctx.lctx_bp
            ctx.lctx_addr_space (unwrap_load_lattice initial)
            (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
              (normalize_operand ctx.lctx_dfg []) inst))` by
            (irule le_retained_store_invalidation_member >> simp[] >> metis_tac[]) >>
          irule le_retained_store_read_step >> metis_tac[]) >>
      drule_all le_configured_retained_other_read >> simp[]) >>
  `ctx.lctx_addr_space = AddrSp_Calldata \/ ctx.lctx_addr_space = AddrSp_Data` by
    (fs[le_configured_context_def] >>
     gvs[memory_config_def, storage_config_def, transient_config_def,
         dload_config_def, calldataload_config_def]) >>
  gvs[]
  >- (drule le_calldata_read_step >> simp[]) >>
  drule le_data_read_step >> simp[]
QED

(* Alternatives need not all denote the current read. Their multiplicity
   alone excludes a singleton overwrite at this retained step. *)
Theorem le_configured_multivalue_step_read_local:
  le_configured_context ctx /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  le_inst_operands_valid ctx.lctx_dfg inst s /\ inst_wf inst /\
  le_absolute_key ctx.lctx_addr_space key /\
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) key = SOME ops /\
  1 < LENGTH ops /\
  le_key_address ctx.lctx_addr_space key s = SOME a /\ a < dimword (:256) /\
  step_inst fuel C inst s = OK t ==>
  le_read_address ctx.lctx_addr_space a t = le_read_address ctx.lctx_addr_space a s
Proof
  strip_tac >>
  `!op. ops = [op] ==> ~le_transfer_generates ctx inst key op` by
    (rpt strip_tac >> gvs[]) >>
  drule_all le_configured_retained_step_read_local >> simp[]
QED

Theorem le_configured_generation_address_local:
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  le_inst_operands_valid ctx.lctx_dfg inst s /\
  le_transfer_generates ctx inst key op /\
  step_inst fuel C inst s = OK t /\
  (!a. key = LK_Op (Var a) ==> ~MEM a inst.inst_outputs) ==>
  ?a. le_key_address ctx.lctx_addr_space key t = SOME a /\ a < dimword (:256)
Proof
  strip_tac >>
  `le_absolute_key ctx.lctx_addr_space key` by
    metis_tac[le_generated_key_absolute] >>
  fs[le_transfer_generates_def]
  >- (drule_all le_configured_load_opcode >> strip_tac >>
      drule_all le_generating_load_address_exists >> strip_tac >>
      `eval_operand (normalize_operand ctx.lctx_dfg [] addr) s = SOME w` by
        metis_tac[le_inst_operands_valid_eval, MEM] >>
      `le_key_address ctx.lctx_addr_space
        (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
          (normalize_operand ctx.lctx_dfg []) inst) s = SOME (w2n w)` by
        (Cases_on `inst.inst_opcode = DLOAD`
         >- (gvs[] >> drule_all le_dload_key_address >> simp[]) >>
         irule le_empty_read_key_address >> gvs[]) >>
      drule_all le_generating_load_state >> strip_tac >> gvs[] >>
      qexists `w2n w` >> simp[w2n_lt] >>
      irule EQ_TRANS >> irule_at Any le_absolute_key_update_var >>
      simp[] >> metis_tac[]) >>
  drule_all le_configured_store_opcode >> strip_tac >>
  drule_all le_generating_store_address_exists >> strip_tac >>
  `eval_operand (normalize_operand ctx.lctx_dfg [] addr) s = SOME w` by
    metis_tac[le_inst_operands_valid_eval, MEM] >>
  `le_key_address ctx.lctx_addr_space
    (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) inst) s = SOME (w2n w)` by
    (irule le_empty_write_key_address >> simp[] >> metis_tac[]) >>
  drule_all le_generating_store_state >> strip_tac >>
  qexists `w2n w` >> simp[w2n_lt] >>
  metis_tac[le_absolute_key_same_bindings]
QED

Theorem le_configured_retained_step_read:
  le_configured_context ctx /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  dfg_assigns_sound ctx.lctx_dfg s /\ inst_wf inst /\
  le_absolute_key ctx.lctx_addr_space key /\
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) key = SOME ops /\
  (!op. ops = [op] ==> ~le_transfer_generates ctx inst key op) /\
  le_key_address ctx.lctx_addr_space key s = SOME a /\ a < dimword (:256) /\
  step_inst fuel C inst s = OK t ==>
  le_read_address ctx.lctx_addr_space a t = le_read_address ctx.lctx_addr_space a s
Proof
  metis_tac[le_configured_retained_step_read_local,
            le_dfg_sound_inst_operands_valid]
QED

Theorem le_configured_multivalue_step_read:
  le_configured_context ctx /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  dfg_assigns_sound ctx.lctx_dfg s /\ inst_wf inst /\
  le_absolute_key ctx.lctx_addr_space key /\
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) key = SOME ops /\
  1 < LENGTH ops /\
  le_key_address ctx.lctx_addr_space key s = SOME a /\ a < dimword (:256) /\
  step_inst fuel C inst s = OK t ==>
  le_read_address ctx.lctx_addr_space a t = le_read_address ctx.lctx_addr_space a s
Proof
  metis_tac[le_configured_multivalue_step_read_local,
            le_dfg_sound_inst_operands_valid]
QED

Theorem le_configured_generation_address:
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  dfg_assigns_sound ctx.lctx_dfg s /\
  le_transfer_generates ctx inst key op /\
  step_inst fuel C inst s = OK t /\
  (!a. key = LK_Op (Var a) ==> ~MEM a inst.inst_outputs) ==>
  ?a. le_key_address ctx.lctx_addr_space key t = SOME a /\ a < dimword (:256)
Proof
  metis_tac[le_configured_generation_address_local,
            le_dfg_sound_inst_operands_valid]
QED

Theorem le_analyze_step_transfer:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ n < LENGTH bb.bb_instructions ==>
  df_at NONE (load_analyze ctx fn) lbl (SUC n) =
  load_transfer ctx (EL n bb.bb_instructions)
    (df_at NONE (load_analyze ctx fn) lbl n)
Proof
  strip_tac >>
  `SUC n <= LENGTH bb.bb_instructions` by simp[] >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  `df_at NONE (load_analyze ctx fn) lbl (SUC n) =
    FOLDL (\a i. load_transfer ctx i a)
      (df_at NONE (load_analyze ctx fn) lbl 0)
      (TAKE (SUC n) bb.bb_instructions)` by
    (irule le_analyze_prefix_fold >> simp[]) >>
  `df_at NONE (load_analyze ctx fn) lbl n =
    FOLDL (\a i. load_transfer ctx i a)
      (df_at NONE (load_analyze ctx fn) lbl 0)
      (TAKE n bb.bb_instructions)` by
    (irule le_analyze_prefix_fold >> simp[]) >>
  simp[TAKE_SUC, FOLDL_APPEND]
QED

Theorem le_retained_occ_read_local:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  le_occ_valid C fn e /\ le_singleton_retained_occ ctx fn key op e /\
  (!bb n fuel u t. e = StepOcc bb n fuel u t ==>
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    inst_wf (EL n bb.bb_instructions) /\
    le_inst_operands_valid ctx.lctx_dfg (EL n bb.bb_instructions) u) /\
  le_absolute_key ctx.lctx_addr_space key /\
  le_key_address ctx.lctx_addr_space key (le_occ_pre e) = SOME a /\
  a < dimword (:256) ==>
  le_read_address ctx.lctx_addr_space a (le_occ_after e) =
  le_read_address ctx.lctx_addr_space a (le_occ_pre e)
Proof
  strip_tac >> Cases_on `e`
  >- (gvs[le_occ_valid_def, le_singleton_retained_occ_def,
          le_occ_pre_def, le_read_address_occ_after, le_occ_post_def] >>
      rename1 `step_inst k C (EL u.vs_inst_idx bb.bb_instructions) u = OK t` >>
      `df_at NONE (load_analyze ctx fn) bb.bb_label (SUC u.vs_inst_idx) =
        load_transfer ctx (EL u.vs_inst_idx bb.bb_instructions)
          (df_at NONE (load_analyze ctx fn) bb.bb_label u.vs_inst_idx)` by
        (irule le_analyze_step_transfer >> simp[] >>
         metis_tac[lookup_block_label]) >>
      `FLOOKUP (unwrap_load_lattice
        (load_transfer ctx (EL u.vs_inst_idx bb.bb_instructions)
          (df_at NONE (load_analyze ctx fn) bb.bb_label u.vs_inst_idx))) key =
        SOME [op]` by metis_tac[] >>
      `!v. [op] = [v] ==>
        ~le_transfer_generates ctx (EL u.vs_inst_idx bb.bb_instructions) key v` by
        simp[] >>
      drule_all le_configured_retained_step_read_local >> simp[]) >>
  metis_tac[le_phi_read_occ_after]
QED

Theorem le_absolute_key_occ_after:
  le_absolute_key space key /\ le_occ_valid C fn e /\
  (!v. key = LK_Op (Var v) ==> v NOTIN le_occ_writes e) ==>
  le_key_address space key (le_occ_after e) =
  le_key_address space key (le_occ_pre e)
Proof
  strip_tac >> Cases_on `key`
  >- (rename1 `LK_Op op` >> Cases_on `op` >>
      simp[le_key_address_def, eval_operand_def] >>
      AP_TERM_TAC
      >- (irule le_occ_chain_lookup >>
          qexistsl [`C`, `[e]`, `fn`] >>
          simp[le_occ_chain_def] >> metis_tac[]) >>
      Cases_on `e` >>
      gvs[le_occ_valid_def, le_occ_after_def, le_occ_pre_def]
      >- (drule step_inst_preserves_labels_always >> strip_tac >>
          IF_CASES_TAC >> simp[]) >>
      drule eval_phis_preserves_labels >> simp[]) >>
  metis_tac[le_absolute_location_address]
QED

Theorem le_occ_chain_fixed_read:
  !es u s. le_occ_chain u es s /\
  EVERY (\e. le_read_address space a (le_occ_after e) =
    le_read_address space a (le_occ_pre e)) es ==>
  le_read_address space a s = le_read_address space a u
Proof
  Induct >> simp[le_occ_chain_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem le_occ_chain_key_address:
  !es u s. le_occ_chain u es s /\ EVERY (le_occ_valid C fn) es /\
  le_absolute_key space key /\
  (!v. key = LK_Op (Var v) ==> EVERY (\e. v NOTIN le_occ_writes e) es) ==>
  le_key_address space key s = le_key_address space key u
Proof
  Induct >> simp[le_occ_chain_def] >> rpt strip_tac >>
  `le_key_address space key (le_occ_after h) =
    le_key_address space key (le_occ_pre h)` by
    (irule le_absolute_key_occ_after >> metis_tac[]) >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem le_occ_chain_retained_read:
  !es u s. le_occ_chain u es s /\ EVERY (le_occ_valid C fn) es /\
  le_absolute_key space key /\
  (!v. key = LK_Op (Var v) ==> EVERY (\e. v NOTIN le_occ_writes e) es) /\
  EVERY (\e. !a. le_key_address space key (le_occ_pre e) = SOME a /\
    a < dimword (:256) ==>
    le_read_address space a (le_occ_after e) =
    le_read_address space a (le_occ_pre e)) es /\
  le_key_address space key u = SOME a /\ a < dimword (:256) ==>
  le_read_address space a s = le_read_address space a u
Proof
  Induct >> simp[le_occ_chain_def] >> rpt strip_tac >>
  `le_key_address space key (le_occ_after h) =
    le_key_address space key (le_occ_pre h)` by
    (irule le_absolute_key_occ_after >> metis_tac[]) >>
  `le_read_address space a (le_occ_after h) =
    le_read_address space a (le_occ_pre h)` by metis_tac[] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem le_absolute_key_after_post:
  le_absolute_key space key ==>
  le_key_address space key (le_occ_after e) =
  le_key_address space key (le_occ_post e)
Proof
  strip_tac >> Cases_on `key`
  >- (rename1 `LK_Op op` >> Cases_on `op` >> Cases_on `e` >>
      simp[le_occ_after_def, le_occ_post_def, le_key_address_def,
        eval_operand_def, lookup_var_def, COND_RAND]) >>
  metis_tac[le_absolute_location_address]
QED

Theorem le_occ_step_dfs:
  wf_function fn /\ fn_inst_wf fn /\ fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\ MEM (StepOcc bb n fuel u t) es ==>
  MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >>
  `le_occ_valid C fn (StepOcc bb n fuel u t)` by
    metis_tac[le_occ_prefix_member] >>
  `?before. le_occ_prefix C fn s0 before (EL n bb.bb_instructions) u /\
    (!e. MEM e before ==> MEM e es)` by
    metis_tac[loadElimSingletonAvailabilityTheory.le_occ_prefix_step_before] >>
  `MEM u.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >>
  gvs[le_occ_valid_def] >> metis_tac[lookup_block_label]
QED

Theorem le_occ_step_wf:
  wf_function fn /\ fn_inst_wf fn /\ le_occ_valid C fn (StepOcc bb n fuel u t) ==>
  inst_wf (EL n bb.bb_instructions)
Proof
  simp[le_occ_valid_def] >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  fs[fn_inst_wf_def] >> metis_tac[EL_MEM]
QED

Theorem le_prefix_retained_suffix_read_local:
  wf_function fn /\ fn_inst_wf fn /\
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
  (!bb n fuel u t. MEM (StepOcc bb n fuel u t) (pre ++ e::suffix) ==>
    le_inst_operands_valid ctx.lctx_dfg (EL n bb.bb_instructions) u) /\
  EVERY (le_singleton_retained_occ ctx fn key op) suffix /\
  le_absolute_key ctx.lctx_addr_space key /\
  (!v. key = LK_Op (Var v) ==> EVERY (\q. v NOTIN le_occ_writes q) suffix) /\
  le_key_address ctx.lctx_addr_space key (le_occ_post e) = SOME a /\
  a < dimword (:256) ==>
  le_read_address ctx.lctx_addr_space a s =
  le_read_address ctx.lctx_addr_space a (le_occ_post e)
Proof
  strip_tac >>
  `le_occ_chain (le_occ_after e) suffix s` by
    (drule le_occ_prefix_chain >> simp[le_occ_chain_append, le_occ_chain_def] >>
     metis_tac[]) >>
  `EVERY (le_occ_valid C fn) suffix` by
    (drule le_occ_prefix_valid >> simp[]) >>
  `EVERY (\q. !a. le_key_address ctx.lctx_addr_space key (le_occ_pre q) = SOME a /\
    a < dimword (:256) ==>
    le_read_address ctx.lctx_addr_space a (le_occ_after q) =
    le_read_address ctx.lctx_addr_space a (le_occ_pre q)) suffix` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM q (pre ++ e::suffix)` by simp[] >>
     `le_occ_valid C fn q /\ le_singleton_retained_occ ctx fn key op q` by
       metis_tac[EVERY_MEM] >>
     irule le_retained_occ_read_local >> simp[] >>
     qexistsl [`C`, `fn`, `key`, `op`] >> simp[] >>
     rpt gen_tac >> strip_tac >> gvs[] >>
     conj_tac
     >- (metis_tac[le_occ_step_dfs, MEM_APPEND, MEM]) >>
     conj_tac >- (irule le_occ_step_wf >> metis_tac[]) >>
     metis_tac[]) >>
  `le_key_address ctx.lctx_addr_space key (le_occ_after e) = SOME a` by
    metis_tac[le_absolute_key_after_post] >>
  drule_all le_occ_chain_retained_read >> simp[le_read_address_occ_after]
QED

Theorem le_key_address_operand_injective:
  le_key_address space (LK_Op op) s = le_key_address space (LK_Op op) t ==>
  eval_operand op s = eval_operand op t
Proof
  simp[le_key_address_def] >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >> simp[w2n_11]
QED

Theorem le_prefix_suffix_key_address:
  le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
  le_absolute_key space key /\
  (!v. key = LK_Op (Var v) ==> EVERY (\q. v NOTIN le_occ_writes q) suffix) ==>
  le_key_address space key s = le_key_address space key (le_occ_post e)
Proof
  strip_tac >>
  `le_occ_chain (le_occ_after e) suffix s` by
    (drule le_occ_prefix_chain >> simp[le_occ_chain_append, le_occ_chain_def] >>
     metis_tac[]) >>
  `EVERY (le_occ_valid C fn) suffix` by
    (drule le_occ_prefix_valid >> simp[]) >>
  drule_all le_occ_chain_key_address >>
  simp[le_absolute_key_after_post]
QED

Theorem le_occ_prefix_singleton_current_local:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
    le_inst_operands_valid ctx.lctx_dfg (EL n bb.bb_instructions) u) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand op s
Proof
  strip_tac >>
  drule_all le_occ_prefix_singleton_suffix >> strip_tac >>
  qpat_x_assum `es = _` SUBST_ALL_TAC >>
  `MEM (StepOcc bb n fuel u t) (pre ++ StepOcc bb n fuel u t::suffix)` by simp[] >>
  `le_occ_valid C fn (StepOcc bb n fuel u t)` by
    metis_tac[le_occ_prefix_member] >>
  `MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions` by
    (fs[le_occ_valid_def] >> metis_tac[lookup_block_MEM]) >>
  `(!v. key = LK_Op (Var v) ==> ~MEM v (EL n bb.bb_instructions).inst_outputs)` by
    (rpt strip_tac >> gvs[] >> drule_all le_generator_key_output_separate >> simp[]) >>
  `le_absolute_key ctx.lctx_addr_space key` by
    metis_tac[le_generated_key_absolute] >>
  `step_inst fuel C (EL n bb.bb_instructions) u = OK t` by
    fs[le_occ_valid_def] >>
  `le_inst_operands_valid ctx.lctx_dfg (EL n bb.bb_instructions) u` by metis_tac[] >>
  `le_key_read ctx.lctx_addr_space key t = eval_operand op t` by
    (irule le_configured_generation_read_local >> simp[] >> metis_tac[]) >>
  drule_all le_configured_generation_address_local >> strip_tac >>
  `!v. key = LK_Op (Var v) ==> EVERY (\q. v NOTIN le_occ_writes q) suffix` by
    (rpt strip_tac >> qpat_x_assum `key = _` SUBST_ALL_TAC >>
     drule_all le_singleton_suffix_key_no_writes >> simp[]) >>
  `le_key_address ctx.lctx_addr_space key s = le_key_address ctx.lctx_addr_space key t` by
    (drule_all le_prefix_suffix_key_address >> simp[le_occ_post_def]) >>
  `le_read_address ctx.lctx_addr_space a s = le_read_address ctx.lctx_addr_space a t` by
    (drule_at_then (Pat `le_occ_prefix _ _ _ _ _ _`)
       (mp_tac o SRULE [le_occ_post_def]) le_prefix_retained_suffix_read_local >>
     disch_then irule >> simp[] >>
     conj_tac >- (gvs[] >> metis_tac[]) >>
     qexistsl [`key`, `op`] >> simp[]) >>
  `eval_operand op s = eval_operand op t` by suspend "operand" >>
  gvs[le_key_read_def]
QED

Resume le_occ_prefix_singleton_current_local[operand]:
  irule le_key_address_operand_injective >>
  qexists `ctx.lctx_addr_space` >>
  `!v. op = Var v ==> EVERY (\q. v NOTIN le_occ_writes q) suffix` by
    (rpt strip_tac >> qpat_x_assum `op = _` SUBST_ALL_TAC >>
     drule_all le_singleton_suffix_value_no_writes >> simp[]) >>
  `le_absolute_key ctx.lctx_addr_space (LK_Op op)` by simp[le_absolute_key_def] >>
  `!v. LK_Op op = LK_Op (Var v) ==> EVERY (\q. v NOTIN le_occ_writes q) suffix` by
    simp[] >>
  drule_all le_prefix_suffix_key_address >> simp[le_occ_post_def]
QED
Finalise le_occ_prefix_singleton_current_local

Theorem le_frame_singleton_current_local:
  frame_reach C fn s0 i s /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!es bb n fuel u t. le_occ_prefix C fn s0 es i s /\
    MEM (StepOcc bb n fuel u t) es ==>
    le_inst_operands_valid ctx.lctx_dfg (EL n bb.bb_instructions) u) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand op s
Proof
  strip_tac >> drule_all le_occ_prefix_annotate >> strip_tac >>
  irule le_occ_prefix_singleton_current_local >> simp[] >>
  qexistsl [`C`, `es`, `fn`, `i`, `s0`] >> simp[] >> metis_tac[]
QED

(* Compatibility boundaries for callers carrying global DFG soundness. *)
Theorem le_retained_occ_read:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  le_occ_valid C fn e /\ le_singleton_retained_occ ctx fn key op e /\
  (!bb n fuel u t. e = StepOcc bb n fuel u t ==>
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    inst_wf (EL n bb.bb_instructions) /\ dfg_assigns_sound ctx.lctx_dfg u) /\
  le_absolute_key ctx.lctx_addr_space key /\
  le_key_address ctx.lctx_addr_space key (le_occ_pre e) = SOME a /\
  a < dimword (:256) ==>
  le_read_address ctx.lctx_addr_space a (le_occ_after e) =
  le_read_address ctx.lctx_addr_space a (le_occ_pre e)
Proof
  strip_tac >> irule le_retained_occ_read_local >> simp[] >>
  qexistsl [`C`, `fn`, `key`, `op`] >> simp[] >>
  metis_tac[le_dfg_sound_inst_operands_valid]
QED

Theorem le_prefix_retained_suffix_read:
  wf_function fn /\ fn_inst_wf fn /\
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
  (!bb n fuel u t. MEM (StepOcc bb n fuel u t) (pre ++ e::suffix) ==>
    dfg_assigns_sound ctx.lctx_dfg u) /\
  EVERY (le_singleton_retained_occ ctx fn key op) suffix /\
  le_absolute_key ctx.lctx_addr_space key /\
  (!v. key = LK_Op (Var v) ==> EVERY (\q. v NOTIN le_occ_writes q) suffix) /\
  le_key_address ctx.lctx_addr_space key (le_occ_post e) = SOME a /\
  a < dimword (:256) ==>
  le_read_address ctx.lctx_addr_space a s =
  le_read_address ctx.lctx_addr_space a (le_occ_post e)
Proof
  strip_tac >> irule le_prefix_retained_suffix_read_local >> simp[] >>
  qexistsl [`C`, `fn`, `i`, `key`, `op`, `pre`, `s0`, `suffix`] >> simp[] >>
  gvs[MEM_APPEND, MEM] >> metis_tac[le_dfg_sound_inst_operands_valid]
QED

Theorem le_occ_prefix_singleton_current:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
    dfg_assigns_sound ctx.lctx_dfg u) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand op s
Proof
  strip_tac >> irule le_occ_prefix_singleton_current_local >> simp[] >>
  qexistsl [`C`, `es`, `fn`, `i`, `s0`] >> simp[] >>
  metis_tac[le_dfg_sound_inst_operands_valid]
QED

Theorem le_frame_singleton_current:
  frame_reach C fn s0 i s /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!es bb n fuel u t. le_occ_prefix C fn s0 es i s /\
    MEM (StepOcc bb n fuel u t) es ==> dfg_assigns_sound ctx.lctx_dfg u) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand op s
Proof
  strip_tac >> irule le_frame_singleton_current_local >> simp[] >>
  qexistsl [`C`, `fn`, `i`, `s0`] >> simp[] >>
  metis_tac[le_dfg_sound_inst_operands_valid]
QED
