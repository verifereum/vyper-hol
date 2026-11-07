(* The external-return caller's encoder run, derived from the shared
   encoder spine over the function's 32-byte ALLOCA sites. *)
Theory abiEncoderSharedWindowRun
Ancestors
  abiEncoderSharedRecursive abiEncoderSharedContract abiEncoderVarRestore
  abiEncoderSharedWindowAdapter abiEncoderEmptyRun abiEncoderEntry abiEncoderExitPhi
  abiScratchEncoderContract
  abiEncoderRegisteredEffect abiEncoderWindow abiEncoderAdmissible
  abiDecoderAllocation abiDecoderFootprint abiDecoderReentry abiDecoderLoop
  abiEncoderProps exprLoweringProps fragExec compileEnv
  venomState venomInst venomExecSemantics venomMemDefs venomWf
  contractABI valueEncoding words list finite_map pred_set

Theorem compile_abi_encode_to_buf_positive_shared_window_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_inv initial /\ alloca_room ctx func initial /\
  sb + source_cap <= initial.vs_alloca_next /\
  d + LENGTH (enc at av) <= initial.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,source_cap) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st st' /\
    FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,source_cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ LENGTH (enc at av) <> 0 ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_registered_effect (frag_ids st st')
      [(d,LENGTH (enc at av))] initial actual /\
    alloca_inv actual /\ alloca_room ctx func actual /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  qabbrev_tac `cap = initial.vs_alloca_next + 32 * CARD (abi_sites_decoder_missing
    (abi_encoder_alloca_sites func) st.cs_next_id st'.cs_next_id initial)` >>
  `abi_sites_decoder_budget (abi_encoder_alloca_sites func)
    st.cs_next_id st'.cs_next_id 0 cap initial` by
    (simp_tac bool_ss [Abbr `cap`] >> irule abi_encoder_alloca_window_budget >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `initial.vs_alloca_next <= cap /\ cap < dimword (:256)` by
    (qpat_x_assum `abi_sites_decoder_budget _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[abi_sites_decoder_budget_def] >> strip_tac >>
     decide_tac) >>
  `abi_sites_encoder_shared_input (abi_encoder_alloca_sites func)
    (ei,at,av) (st,src,dst) (sb,source_cap) (d,LENGTH (enc at av))
    (st.cs_next_id,st'.cs_next_id,0,cap)
    (abi_decoder_prune_vars st.cs_next_var initial)` by
    (irule abi_encoder_positive_window_input >> asm_rewrite_tac[]) >>
  `?actual. abi_sites_encoder_shared_endpoint (abi_encoder_alloca_sites func)
    (ctx,func) (st,st',out,st') (st.cs_next_id,st'.cs_next_id,0,cap) (at,av,d)
    (abi_decoder_prune_vars st.cs_next_var initial) actual` by
    (irule abi_encoder_shared_run >> asm_rewrite_tac[] >>
     suspend "shared_entry") >>
  drule abi_encoder_shared_restore >> strip_tac >>
  qexists_tac `restored` >> asm_rewrite_tac[] >>
  suspend "restored_resources"
QED

Resume compile_abi_encode_to_buf_positive_shared_window_run[shared_entry]:
  `fresh_vars_wrt st' (abi_decoder_prune_vars st.cs_next_var initial)` by
    (drule abi_encoder_prune_limit_fresh >> simp[]) >>
  `st.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (drule_all abi_encoder_core_containing_exit_phi >> simp[]) >>
  `abi_sites_encoder_shared (abi_encoder_alloca_sites func) ei` by
    (irule abi_encoder_shared_admissible >> first_assum ACCEPT_TAC) >>
  `abi_sites_decoder_budget (abi_encoder_alloca_sites func) st.cs_next_id st'.cs_next_id 0 cap
    (abi_decoder_prune_vars st.cs_next_var initial)` by
    (qpat_x_assum `abi_sites_decoder_budget _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[abi_sites_decoder_budget_def, abi_sites_decoder_missing_def,
       abi_decoder_prune_vars_def] >>
     pure_rewrite_tac[venom_state_accfupds] >>
     disch_then ACCEPT_TAC) >>
  asm_rewrite_tac [abi_encoder_alloca_sites_cover, abi_decoder_prune_vars_def,
    venom_state_accfupds, arithmeticTheory.LESS_EQ_REFL] >>
  qexistsl_tac [`dst`, `ei`, `sb`, `source_cap`, `src`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `abi_sites_encoder_shared_input _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_prune_vars_def] >> disch_then ACCEPT_TAC
QED

Resume compile_abi_encode_to_buf_positive_shared_window_run[restored_resources]:
  drule abi_encoder_vars_extend_fields >>
  simp_tac bool_ss [pairTheory.PAIR_EQ] >> strip_tac >>
  `alloca_inv (abi_decoder_prune_vars st.cs_next_var initial)` by
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     simp[abi_decoder_prune_vars_def, alloca_inv_def,
       alloca_next_valid_def, allocas_non_overlapping_def]) >>
  `alloca_inv actual` by
    (drule_all abi_encoder_shared_endpoint_alloca_inv >> simp[]) >>
  `alloca_inv restored` by
    (qpat_x_assum `alloca_inv actual` mp_tac >>
     asm_rewrite_tac[alloca_inv_def, alloca_next_valid_def, allocas_non_overlapping_def]) >>
  `abi_encoder_registered_effect
    (abi_sites_decoder_ids (abi_encoder_alloca_sites func) st.cs_next_id st'.cs_next_id)
    [(d,LENGTH (enc at av))] initial restored` by
    (drule abi_encoder_shared_endpoint_registered >>
     pure_rewrite_tac[abi_encoder_registered_effect_def, abi_decoder_prune_vars_def,
       venom_state_accfupds] >>
     asm_rewrite_tac[abi_encoder_registered_effect_def]) >>
  `abi_sites_decoder_budget (abi_encoder_alloca_sites func) st.cs_next_id st'.cs_next_id
    0 cap restored` by
    (drule abi_encoder_shared_endpoint_scratch >>
     pure_rewrite_tac[abi_sites_scratch_effect_def] >> strip_tac >>
     qpat_x_assum `abi_sites_decoder_budget _ _ _ _ _ actual` mp_tac >>
     asm_rewrite_tac[abi_sites_decoder_budget_def, abi_sites_decoder_missing_def]) >>
  `alloca_room ctx func restored` by
    (qpat_x_assum `abi_sites_decoder_budget _ _ _ _ _ restored` mp_tac >>
     simp_tac bool_ss [Abbr `cap`] >> strip_tac >>
     drule_all abi_encoder_alloca_room_from_budget >> simp[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule abi_encoder_registered_effect_enlarge >>
      goal_assum (drule_at Any) >>
      simp_tac (srw_ss()) [abi_sites_decoder_ids_def, frag_ids_def, SUBSET_DEF]) >>
  rpt strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x)` by
    fs[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
  drule_all abi_encoder_restored_operand >> simp[eval_operand_def]
QED

Finalise compile_abi_encode_to_buf_positive_shared_window_run

(* The public caller splits empty encodings (straight-line zero-byte copies)
   from positive encodings (the shared spine on concrete 32-byte sites).
   Pruning/restoration supplies freshness without changing caller operands;
   exact selected-site charge accounting recovers the full allocation room. *)
Theorem compile_abi_encode_to_buf_shared_window_run:
  !dst src ei st out st' ctx func initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
    eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv initial /\ alloca_room ctx func initial /\
    sb + source_cap <= initial.vs_alloca_next /\
    d + LENGTH (enc at av) <= initial.vs_alloca_next /\
    venomMemDefs$regions_disjoint
      (sb,source_cap) (d,LENGTH (enc at av)) /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      venomMemDefs$regions_disjoint (sb,source_cap) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~initial.vs_halted /\
    initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
      eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (frag_ids st st')
        [(d,LENGTH (enc at av))] initial actual /\
      alloca_inv actual /\ alloca_room ctx func actual /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
             lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\
      actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH (enc at av) = 0`
  >- (drule_all compile_abi_encode_to_buf_empty_window_run >> simp[]) >>
  drule_all compile_abi_encode_to_buf_positive_shared_window_run >> simp[]
QED
