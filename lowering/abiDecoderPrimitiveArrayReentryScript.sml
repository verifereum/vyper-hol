Theory abiDecoderPrimitiveArrayReentry
Ancestors
  abiDecoderArrayInit abiDecoderArrayLoopInit abiDecoderLoopEmit
  abiDecoderPrimitiveLoopInvariant abiDecoderPrimitiveLoopLayout abiDecoderAppend abiDecoderCode
  abiDecoderContract fragExec exprLoweringProps emitHelperProps compileEnv venomState words list
  arithmetic abiDecoderPrimitiveArrayFacts abiDecoderPrimitiveLoopContext
  abiDecoderArrayInvariant abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry
  abiDecoderLoop abiDecoderFrame abiDecoderAllocation valueEncoding abiDecoderArrayInitReentry
  finite_map abiDecoderBulkExecute abiDecoderPrimitiveLoopEntry abiDecoderArrayInitExec
  abiDecoderBulkReentry abiDecoderProtectedScratch
Libs
  Omega

(* Extract actual initialization/loop subfragments from primitive array compilation. *)
Theorem abi_decoder_primitive_loop_end:
  compile_abi_decode_dyn_loop dst src opc hi (DecPrimWord clamp) 32 32 ip cnt
    start = ((),end_st) /\ abi_decode_source_opcode opc ==>
  start.cs_next_id <= end_st.cs_next_id /\ start.cs_next_var <= end_st.cs_next_var /\
  end_st.cs_current_insts = [] /\
  end_st.cs_current_bb = fresh_label_output "dec_dyn_exit" (start.cs_next_label + 2) /\
  cs_extends start end_st
Proof
  strip_tac >> drule_all abi_decoder_dyn_loop_code >> strip_tac >>
  qpat_assum `abi_decoder_code _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_code_def]) >>
  `cs_extends start end_st` by metis_tac[cj 3 cs_appends_abi_decode_mutual, cs_appends_def] >>
  drule_all abi_decode_dyn_loop_trace >> strip_tac >>
  `st0.cs_current_insts = [] /\ st0.cs_next_var = start.cs_next_var + 4` by
    gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def] >>
  drule_all abi_decoder_primitive_body_counters >> strip_tac >>
  drule_all abi_decoder_primitive_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >>
  gvs[abi_decode_loop_suffix_state_def] >> decide_tac
QED

Theorem abi_decoder_primitive_array_code:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  dec_info_needs_clamp (DecPrimWord clamp) /\ abi_decode_source_opcode opc /\
  fn_has_code st end_st fn ==>
  ?setup loop_st.
    abi_decode_array_loop_init dst src opc hi maxn 32 st = (setup,loop_st) /\
    compile_abi_decode_dyn_loop dst src opc hi (DecPrimWord clamp) 32 32 (FST setup) (SND setup)
      loop_st = ((),end_st) /\
    fn_has_code st loop_st fn /\ fn_has_code loop_st end_st fn /\
    loop_st.cs_next_id <= end_st.cs_next_id /\ loop_st.cs_next_var <= end_st.cs_next_var /\
    end_st.cs_current_insts = [] /\
    end_st.cs_current_bb = fresh_label_output "dec_dyn_exit" (loop_st.cs_next_label + 2)
Proof
  strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`elem_dyn` |-> `F`] abi_decode_loop_array_trace)) >>
  strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decoder_primitive_loop_end >> strip_tac >>
  `cs_extends st loop_st` by (irule cs_extends_same_block >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl_tac [`setup`, `loop_st`] >> simp[]
QED

(* Actual initialized loop entry from the typed primitive-array precondition. *)
Theorem abi_decoder_primitive_array_pre_ranges:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap initial ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  fresh_vars_wrt st initial /\ (d + 32 <= b \/ b + cap <= d)
Proof
  strip_tac >> drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [] >> Omega.OMEGA_TAC
QED

Theorem abi_decoder_primitive_array_initialize:
  abi_decode_array_loop_init dst src opc hi maxn 32 st = (setup,loop_st) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st end_st.cs_next_id src dst opc hi sb d b cap initial /\
  abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap initial /\
  loop_st.cs_next_id <= end_st.cs_next_id /\ loop_st.cs_next_var <= end_st.cs_next_var /\
  fn_has_code st loop_st fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared slot.
    abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared /\
    abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot
      [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)] /\
    abi_decoder_loop_inputs loop_st.cs_next_var (FST setup) src dst sb d slot prepared /\
    fresh_vars_wrt loop_st prepared /\ fresh_vars_wrt end_st prepared /\
    ~prepared.vs_halted /\ mload slot prepared = 0w /\
    prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    b <= slot /\ slot + 32 <= b + cap /\
    abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap prepared /\
    (!op w. eval_operand op initial = SOME w ==> eval_operand op prepared = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] initial prepared /\
    abi_decode_sim ctx fn initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_pre_ranges >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`first` |-> `st.cs_next_id`] abi_decode_array_loop_init_from_state)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx fn initial prepared` >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  rename1 `mload slot prepared = 0w` >>
  `!op w. eval_operand op initial = SOME w ==> eval_operand op prepared = SOME w` by
    metis_tac[abi_decoder_operand_live_fresh] >>
  drule_all abi_decoder_array_init_memory >> strip_tac >>
  `eval_operand src prepared = SOME (n2w sb) /\ eval_operand dst prepared = SOME (n2w d)`
    by metis_tac[] >>
  `abi_decoder_loop_inputs loop_st.cs_next_var (FST setup) src dst sb d slot prepared` by
    (simp_tac bool_ss [abi_decoder_loop_inputs_def] >>
     metis_tac[abi_decoder_operand_live_fresh]) >>
  `fresh_vars_wrt end_st prepared` by
    (mp_tac (Q.SPECL [`loop_st`, `end_st`, `prepared`] fresh_vars_wrt_mono) >> simp[GREATER_EQ]) >>
  qexistsl_tac [`prepared`, `slot`] >> gvs[Excl "enc_def"]
QED

(* Typed primitive-array entry under an enclosing loop's freshness/budget bounds. *)
Theorem abi_decoder_pre_pruned_operands:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) ==>
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by simp[abi_decoder_operand_live_def] >>
  metis_tac[abi_decoder_pruned_operand_defined]
QED

Theorem abi_decoder_primitive_array_reentry_pre_facts:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH vs * 32 <= h /\ h < dimword (:256)) /\
  (d + 32 <= b \/ b + cap <= d) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * 32
Proof
  strip_tac >> drule_all abi_decoder_primitive_array_pre_ranges >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[abi_decoder_prune_eval, Excl "enc_def"] >>
  rename1 `eval_operand hi initial = SOME (n2w h)` >>
  disj2_tac >> qexists_tac `h` >> simp[]
QED

Theorem abi_decoder_primitive_array_reentry_initialize:
  abi_decode_array_loop_init dst src opc hi maxn 32 st = (setup,loop_st) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ fn_has_code st loop_st fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared slot.
    abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared /\
    abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot
      [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)] /\
    abi_decoder_loop_inputs loop_st.cs_next_var (FST setup) src dst sb d slot prepared /\
    fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\ mload slot prepared = 0w /\
    prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    b <= slot /\ slot + 32 <= b + cap /\ abi_decoder_budget first last b cap prepared /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op prepared = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] initial prepared /\
    abi_decode_footprint_frame [(d,32);(slot,32)] initial prepared /\
    FLOOKUP prepared.vs_allocas (loop_st.cs_next_id - 2) = SOME (slot,32) /\
    (!id. id <> loop_st.cs_next_id - 2 ==>
      FLOOKUP prepared.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    abi_decode_sim ctx fn initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_reentry_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_reentry_from_state >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx fn initial prepared` >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  rename1 `mload slot prepared = 0w` >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`,
    `t` |-> `prepared:venom_state`] abi_decoder_array_init_memory) >>
  impl_tac >- asm_simp_tac bool_ss [abi_decoder_footprint_prune_before] >> strip_tac >>
  `eval_operand src prepared = SOME (n2w sb) /\ eval_operand dst prepared = SOME (n2w d)`
    by metis_tac[] >>
  drule abi_decode_array_loop_index_live >> strip_tac >>
  `abi_decoder_loop_inputs loop_st.cs_next_var (FST setup) src dst sb d slot prepared` by
    (simp_tac bool_ss [abi_decoder_loop_inputs_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
  qexistsl_tac [`prepared`, `slot`] >> gvs[Excl "enc_def"]
QED

(* Typed execution of complete primitive-array decoders, with and without clamps. *)
Theorem abi_decoder_loop_frame_to_arena:
  abi_decode_footprint_frame [(d,outsz);(slot,32)] s t /\
  b <= slot /\ slot + 32 <= b + cap ==>
  abi_decode_footprint_frame [(d,outsz);(b,cap)] s t
Proof
  strip_tac >> irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(d,outsz);(slot,32)]` >> simp[] >> rw[]
  >- (qexistsl_tac [`d`, `outsz`] >> simp[]) >>
  qexistsl_tac [`b`, `cap`] >> simp[]
QED

Theorem abi_decoder_clamped_array:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  dec_info_needs_clamp (DecPrimWord clamp) /\ fn_has_code st end_st fn /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st end_st.cs_next_id src dst opc hi sb d b cap initial /\
  abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) end_st d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap t /\
    t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~t.vs_halted /\
    abi_decode_sim ctx fn initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_pre_ranges >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_code >> strip_tac >>
  drule_all abi_decoder_primitive_array_initialize >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`limit_st` |-> `end_st:compile_state`] abi_decoder_primitive_dyn_loop)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_loop_rel _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_loop_rel_def]) >>
  `abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap t` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w` by
    metis_tac[abi_decoder_operand_live_fresh] >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial prepared` by (drule_all abi_decoder_array_init_frame_widen >> simp[]) >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    prepared t` by (drule_all abi_decoder_loop_frame_to_arena >> simp[]) >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial t` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> simp[]) >>
  `abi_decode_sim ctx fn initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]) >>
  qexists_tac `t` >> simp[abi_decoder_post_def]
QED

Theorem abi_decoder_primitive_array:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  fn_has_code st end_st fn /\
  (dec_info_needs_clamp (DecPrimWord clamp) ==>
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st end_st.cs_next_id src dst opc hi sb d b cap initial /\
  abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) end_st d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap t /\
    t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~t.vs_halted /\
    abi_decode_sim ctx fn initial t
Proof
  Cases_on `dec_info_needs_clamp (DecPrimWord clamp)`
  >- (strip_tac >>
      `!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
      drule_all abi_decoder_clamped_array >> disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  strip_tac >> drule_all abi_decoder_bulk_execute >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

(* A complete clamped primitive-array child can execute repeatedly in an outer loop. *)
Theorem abi_decoder_clamped_array_reentry:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  dec_info_needs_clamp (DecPrimWord clamp) /\ fn_has_code st end_st fn /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t slot site.
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w) /\
    b <= slot /\ slot + 32 <= b + cap /\ st.cs_next_id <= site /\ site < end_st.cs_next_id /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    (!id. id <> site ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)] initial t /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)] initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_reentry_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_code >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  `loop_st.cs_next_id <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_primitive_array_reentry_initialize >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decoder_primitive_dyn_loop >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_loop_rel _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_loop_rel_def]) >>
  `abi_decoder_budget first last b cap t` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op t = SOME w` by metis_tac[abi_decoder_operand_live_mono] >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)]
    initial prepared` by (irule abi_decoder_array_init_frame_widen >> simp[]) >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)]
    initial t` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial t` by (drule_all abi_decoder_loop_frame_to_arena >> simp[]) >>
  `abi_decode_sim ctx fn initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]) >>
  qexistsl_tac [`t`, `slot`, `loop_st.cs_next_id - 2`] >>
  asm_simp_tac bool_ss [] >> simp[] >> decide_tac
QED

Theorem abi_decoder_clamped_array_reentry_protected:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  dec_info_needs_clamp (DecPrimWord clamp) /\ fn_has_code st end_st fn /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)] initial t /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!other protected. other IN abi_decoder_ids first last /\
      (other < st.cs_next_id \/ end_st.cs_next_id <= other) /\
      FLOOKUP initial.vs_allocas other = SOME (protected,32) ==>
      mload protected t = mload protected initial) /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_clamped_array_reentry >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_output_separated >> disch_then assume_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `t:venom_state`,
    `child_first` |-> `st.cs_next_id`, `child_last` |-> `end_st.cs_next_id`,
    `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
    abi_decoder_child_scratch_preservation) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  `!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (rpt strip_tac >> `id <> site` by decide_tac >> metis_tac[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem abi_decoder_primitive_array_reentry:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  fn_has_code st end_st fn /\
  (dec_info_needs_clamp (DecPrimWord clamp) ==>
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)] initial t /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!other protected. other IN abi_decoder_ids first last /\
      (other < st.cs_next_id \/ end_st.cs_next_id <= other) /\
      FLOOKUP initial.vs_allocas other = SOME (protected,32) ==>
      mload protected t = mload protected initial) /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_pruned_operands >> strip_tac >>
  Cases_on `dec_info_needs_clamp (DecPrimWord clamp)`
  >- (
      `!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
      drule_all abi_decoder_clamped_array_reentry_protected >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  drule_all abi_decoder_bulk_reentry_protected >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> rpt strip_tac >> metis_tac[]
QED
