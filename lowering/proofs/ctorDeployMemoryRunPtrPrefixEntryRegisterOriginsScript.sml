Theory ctorDeployMemoryRunPtrPrefixEntryRegisterOrigins
Ancestors
  loweringStateRelDefs
 ctorDeployMemoryRunPtrPrefixEntryRegisterListSizes
 ctorDeployMemoryRunPtrPrefixEntryRegisterSizes ctorRegisterArgs
 abiEncoderRegisteredEffect abiEncoderProps venomMemDefs ptrDiscipline pred_set
 compileVyper moduleLowering compileEnv abiDecoderLoop abiDecoderMembers abiDecoderCounters
 emitHelperProps loweringHalt list rich_list arithmetic finite_map

Theorem entry_origins_retained_slot_bytes[local]:
  abi_encoder_registered_effect ids [] s t /\ alloca_inv t /\
  FLOOKUP s.vs_allocas aid = SOME (d,n) /\ aid NOTIN ids /\
  B SUBSET range_bytes [(d,n)] ==>
  !a. a IN B ==> mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (d,n)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  qpat_assum `B SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF, range_bytes_def] >>
  disch_tac >> gen_tac >> disch_tac >>
  `d <= a /\ a < d+n` by metis_tac[] >>
  qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  `aid <> i` by metis_tac[] >>
  qpat_x_assum `alloca_inv t` mp_tac >>
  simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >>
  strip_tac >>
  `d+n <= b \/ b+sz <= d` by metis_tac[] >> decide_tac
QED

Theorem entry_origins_unmentioned_var[local]:
  !rest ce0 vars ce st st' off data_size name.
    ~MEM name (MAP FST rest) /\ ALL_DISTINCT (MAP FST rest) /\
    EVERY (\a. ?old. FLOOKUP vars (FST a) =
      SOME (MemLoc old (type_memory_bytes ce0 (SND a)))) rest /\
    compile_register_constructor_args (ce0 with ce_vars := vars)
      (build_positional_args ce0 rest) off data_size st = (ce,st') ==>
    FLOOKUP ce.ce_vars name = FLOOKUP vars name
Proof
  Induct >- simp[build_positional_args_def, compile_register_constructor_args_def,
                 comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[EVERY_DEF] >> strip_tac >>
  `FLOOKUP (ce0 with ce_vars := vars).ce_vars h0 =
     SOME (MemLoc old (type_memory_bytes (ce0 with ce_vars := vars) h1))` by simp[] >>
  drule ctor_register_cons >>
  disch_then (qspecl_then [`st`,`rest`,`off`,`data_size`] mp_tac) >>
  simp[NoAsms] >> disch_then (fn th =>
    qpat_x_assum `compile_register_constructor_args _ _ _ _ _ = _`
      (mp_tac o REWRITE_RULE [th])) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> fs[] >> pairarg_tac >> fs[] >> strip_tac >>
  `FLOOKUP ce.ce_vars name =
    FLOOKUP (vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1))) name` suffices_by
      simp[FLOOKUP_UPDATE] >>
  first_x_assum irule >> conj_tac >- asm_rewrite_tac[] >>
  qexists `ce0` >>
  qexistsl [`data_size`,`off + abi_embedded_static_size ce0.ce_struct_fields h1`,`cs''`,`st'`] >>
  asm_rewrite_tac[] >>
  fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  `FST a <> h0` by metis_tac[MEM_MAP] >> simp[FLOOKUP_UPDATE]
QED

(* Retain the lower frontier of every freshly registered argument slot.
   All other outputs are the literal-size paired registration interface. *)
Theorem prefix_entry_register_suffix_origins:
  !rest ce0 vars env fargs avs atys encoded scope i st ce st' ctx func site initial G tn D lo PG k.
    rest = DROP i fargs /\ i <= LENGTH fargs /\
    ALL_DISTINCT (MAP FST rest) /\ LENGTH avs = LENGTH fargs /\
    atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
    encoded = enc (Tuple atys) (ListV avs) /\
    LENGTH encoded < dimword (:256) /\
    mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
    EVERY (\a. ?off. FLOOKUP vars (FST a) =
      SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest /\
    EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) rest /\
    (!j. j < LENGTH fargs ==>
      ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
        val_wf entry.type entry.value /\
        type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
        abi_decoder_coherent ce0 env ce0.ce_struct_fields
          (SND (EL j fargs)) entry.type /\
        abi_decoder_metadata ce0 env (SND (EL j fargs)) entry.type
          (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL j fargs)))
          (EL j avs) entry.value) /\
    compile_register_constructor_args (ce0 with ce_vars := vars)
      (build_positional_args ce0 rest)
      (SUM (MAP abi_member_head_size (TAKE i atys))) 0 st = (ce,st') /\
    local_ptrs_rel func (ce0 with ce_vars := vars) [scope] initial /\ fresh_vars_wrt st initial /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    (st.cs_blocks = st'.cs_blocks \/
      !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
    k + unit_alloca_budget ctx < dimword (:256) /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts /\
    allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
    ?actual H qt.
      (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit n] /\
        FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
      local_ptrs_rel func ce [scope] actual /\
      abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
      alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
      fresh_vars_wrt st' actual /\
      (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
      actual.vs_data_section = initial.vs_data_section /\
      actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
        lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual /\
      allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
      initial.vs_alloca_next <= actual.vs_alloca_next /\
      actual.vs_code = initial.vs_code /\ actual.vs_outcomes = initial.vs_outcomes /\
      actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
      actual.vs_gas_readings = initial.vs_gas_readings /\
      (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
      qt.t_mem SUBSET (tn.t_mem UNION
        {j | initial.vs_alloca_next <= j /\ j < actual.vs_alloca_next}) /\
      (!j. j < initial.vs_alloca_next /\ j IN qt.t_mem ==> j IN tn.t_mem) /\
      (!C. (!j. j IN C ==> j < initial.vs_alloca_next) /\ DISJOINT C tn.t_mem ==>
        DISJOINT C qt.t_mem) /\
      qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
      (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
        op_taint qt (Var x) = op_taint tn (Var x)) /\
      ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt actual) ==>
        !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
      (!j. i <= j /\ j < LENGTH fargs ==>
        ?entry d B.
          lo <= d /\
          lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
          local_region ce [scope] actual (FST (EL j fargs)) d
            (type_memory_bytes ce0 (SND (EL j fargs))) /\
          FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce0 (SND (EL j fargs)))] /\
          DISJOINT B qt.t_mem /\ (!a. a IN B ==> a < actual.vs_alloca_next) /\
          (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
            val_in_memory entry.type entry.value d mem))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[build_positional_args_def, compile_register_constructor_args_def, comp_return_def] >>
      qexistsl [`initial`,`G`,`tn`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      simp[abi_encoder_registered_effect_refl, abi_decode_sim_refl] >>
      `i = LENGTH fargs` by (fs[DROP_EQ_NIL] >> decide_tac) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "cons"
QED

Resume prefix_entry_register_suffix_origins[cons]:
  PairCases_on `h` >>
  `i < LENGTH fargs` by
    (`LENGTH ((h0,h1)::rest) = LENGTH (DROP i fargs)` by
       (qpat_assum `_::rest = DROP i fargs` (fn th => rewrite_tac[th])) >>
     qpat_x_assum `LENGTH (_::rest) = LENGTH (DROP i fargs)` mp_tac >>
     pure_rewrite_tac [LENGTH, LENGTH_DROP] >> decide_tac) >>
  `EL i fargs = (h0,h1) /\ rest = DROP (SUC i) fargs` by
    (qspecl_then [`fargs`,`i`] mp_tac DROP_EL_CONS >>
     (impl_tac >- simp[]) >> pure_rewrite_tac[GSYM ADD1] >>
     disch_then (fn th => qpat_assum `_::rest = DROP i fargs`
       (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
  qpat_assum `!j. j < LENGTH fargs ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `entry` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `!ce0 vars env fargs avs atys encoded scope i st ce st' ctx func site initial G tn D lo PG k. _`
    (mk_asm "suffix_ih") >>
  qpat_x_assum `EVERY (\a. ?off. _) (_::rest)` mp_tac >>
  simp_tac pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
  qpat_x_assum `EVERY _ (_::rest)` mp_tac >>
  simp_tac pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `FLOOKUP (ce0 with ce_vars := vars).ce_vars h0 =
     SOME (MemLoc off (type_memory_bytes (ce0 with ce_vars := vars) h1))` by simp[] >>
  drule ctor_register_cons >>
  disch_then (fn th => qpat_x_assum `compile_register_constructor_args _ _ _ _ st = _`
    (mp_tac o PURE_REWRITE_RULE [SRULE[] th])) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce0 h1) st` >>
  rename1 `compile_alloc_buffer _ st = (buf,sa)` >>
  simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
  qmatch_goalsub_abbrev_tac `compile_decode_args next _ _ _ _ _` >>
  Cases_on `compile_decode_args next [build_positional_arg ce0 (h0,h1)]
    (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit 0w) 0 sa` >>
  rename1 `compile_decode_args _ _ _ _ _ _ sa = (u,sd)` >> Cases_on `u` >>
  simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >>
  drule_all ctor_registration_code_phases >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_registration_phi_phases >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "head"
QED

Resume prefix_entry_register_suffix_origins[head]:
  `LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env h1` by
    simp[vyper_to_abi_types_MAP, MAP_COMPOSE, EL_MAP] >>
  `compile_alloc_buffer (type_memory_bytes (ce0 with ce_vars := vars) h1) st = (buf,sa)` by simp[] >>
  `next = ((ce0 with ce_vars := vars) with ce_vars :=
      vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes (ce0 with ce_vars := vars) h1)))` by
    simp[Abbr `next`] >>
  `lookup_scopes h0 [scope] = SOME entry /\
   type_memory_size entry.type <= type_memory_bytes (ce0 with ce_vars := vars) h1 /\
   abi_decoder_coherent (ce0 with ce_vars := vars) env
     (ce0 with ce_vars := vars).ce_struct_fields h1 entry.type /\
   abi_decoder_metadata (ce0 with ce_vars := vars) env h1 entry.type
     (type_to_abi_dec_info (ce0 with ce_vars := vars).ce_struct_fields
       (ce0 with ce_vars := vars) h1) (EL i avs) entry.value` by
    (qpat_assum `EL i fargs = _` (fn th => fs[th])) >>
  `compile_decode_args next [build_positional_arg (ce0 with ce_vars := vars) (h0,h1)]
    (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit 0w) 0 sa = ((),sd)` by
    (pure_rewrite_tac[ctor_positional_arg_vars] >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) prefix_entry_register_one_slot_sizes >>
  disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `_ = enc _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (MemLoc _ _)`)) >>
  disch_then (qspecl_then [`tn`,`lo`,`PG`,`G`,`D`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `middle` (qx_choose_then `MG` (qx_choose_then `mt`
    (qx_choose_then `B` (map_every assume_tac o CONJUNCTS))))) >>
  suspend "recurse"
QED

Resume prefix_entry_register_suffix_origins[recurse]:
  `abi_embedded_static_size ce0.ce_struct_fields h1 = abi_member_head_size (EL i atys)` by
    (drule ctor_coherent_head_size >> simp[]) >>
  `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) =
    SUM (MAP abi_member_head_size (TAKE i atys)) +
    abi_embedded_static_size ce0.ce_struct_fields h1` by
    (irule EQ_TRANS >> irule_at Any ctor_canonical_offset_step >> simp[]) >>
  `EVERY (\a. ?off. FLOOKUP
     (vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1))) (FST a) =
     SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest` by
    (qpat_assum `EVERY (\a. ?off. _) rest` mp_tac >>
     qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, MEM_MAP, FLOOKUP_UPDATE] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     `FST a <> h0` by metis_tac[] >> simp[]) >>
  `compile_register_constructor_args
    (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
    (build_positional_args ce0 rest)
    (SUM (MAP abi_member_head_size (TAKE (SUC i) atys))) 0 sd = (ce,st')` by
    (qpat_assum `compile_register_constructor_args next _ _ _ sd = _` mp_tac >>
     qpat_assum `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) = _`
       (fn th => pure_rewrite_tac[th]) >> simp[Abbr `next`, NoAsms]) >>
  `local_ptrs_rel func
    (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
    [scope] middle` by
    (qpat_assum `local_ptrs_rel func next _ middle` mp_tac >> simp[Abbr `next`, NoAsms]) >>
  `mem_bytes_at 0 (LENGTH encoded) middle.vs_data_section = encoded` by
    (qpat_assum `middle.vs_data_section = _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `ALL_DISTINCT (MAP FST rest)` by
    (qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MAP, ALL_DISTINCT]) >>
  asm "suffix_ih" (drule_at (Pat `compile_register_constructor_args _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `_ = DROP _ _`)) >>
  disch_then (drule_at (Pat `_ = enc _ _`)) >>
  disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
  disch_then (qspecl_then [`env`,`MG`,`mt`,`D`,`lo`,`PG`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[NoAsms] >> decide_tac)) >>
  disch_then (qx_choose_then `actual` (qx_choose_then `H` (qx_choose_then `qt`
    (map_every assume_tac o CONJUNCTS)))) >>
  asm_x "suffix_ih" kall_tac >> suspend "finish"
QED

Resume prefix_entry_register_suffix_origins[finish]:
  `st.cs_next_id <= sd.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     `sa.cs_next_id <= sd.cs_next_id` by
       metis_tac[ctor_decode_args_next_id, pairTheory.SND] >> decide_tac) >>
  `st.cs_next_var <= sd.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     `sa.cs_next_var <= sd.cs_next_var` by
       metis_tac[ctor_decode_args_vars_mono, abi_decoder_vars_mono_def, pairTheory.SND] >> decide_tac) >>
  `sd.cs_next_id <= st'.cs_next_id` by metis_tac[ctor_registration_next_id] >>
  `!x. not_fresh_at st x ==> not_fresh_at sd x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexistsl [`actual`,`H`,`qt`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "effect" >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
  conj_tac >- decide_tac >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- suspend "window" >>
  conj_tac >- (rpt strip_tac >>
    `j < middle.vs_alloca_next` by decide_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> conj_tac
    >- (rpt strip_tac >> `j < initial.vs_alloca_next` by metis_tac[] >> decide_tac) >>
    metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  suspend "supports"
QED

Resume prefix_entry_register_suffix_origins[effect]:
  `abi_encoder_registered_effect (frag_ids st st') [] initial middle` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`frag_ids st sd`,`[]`] >> simp[] >>
     simp[frag_ids_def, SUBSET_DEF] >> rpt strip_tac >> decide_tac) >>
  `abi_encoder_registered_effect (frag_ids st st') [] middle actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`frag_ids sd st'`,`[]`] >> simp[]) >>
  metis_tac[abi_encoder_registered_effect_trans]
QED

Resume prefix_entry_register_suffix_origins[window]:
  qpat_x_assum `qt.t_mem SUBSET _` mp_tac >>
  qpat_x_assum `mt.t_mem SUBSET _` mp_tac >>
  qpat_x_assum `initial.vs_alloca_next <= middle.vs_alloca_next` mp_tac >>
  qpat_x_assum `middle.vs_alloca_next <= actual.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> rpt strip_tac >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Resume prefix_entry_register_suffix_origins[supports]:
  rpt strip_tac >> Cases_on `j = i`
  >- suspend "head_support"
  >> `SUC i <= j` by decide_tac >> metis_tac[]
QED

Resume prefix_entry_register_suffix_origins[head_support]:
  qpat_assum `j = i` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `EL i fargs = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac pure_ss [pairTheory.FST, pairTheory.SND] >>
  qpat_x_assum `?p. buf.buf_operand = Var p /\ _` strip_assume_tac >>
  `~MEM h0 (MAP FST rest)` by
    (qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
     simp_tac (srw_ss()) []) >>
  `FLOOKUP ce.ce_vars h0 = SOME (PtrVar buf.buf_operand (type_memory_bytes ce0 h1))` by
    (drule_at (Pat `compile_register_constructor_args _ _ _ _ sd = _`)
       entry_origins_unmentioned_var >>
     disch_then (qspec_then `h0` mp_tac) >>
     asm_rewrite_tac[] >> simp[FLOOKUP_UPDATE]) >>
  `lookup_var p actual = SOME (n2w initial.vs_alloca_next)` by metis_tac[] >>
  `local_region ce [scope] actual h0 initial.vs_alloca_next (type_memory_bytes ce0 h1)` by
    (qpat_assum `local_region next _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [local_region_def] >> strip_tac >>
     qexistsl [`entry`,`p`,`n2w initial.vs_alloca_next`] >>
     asm_rewrite_tac[] >> fs[Abbr `next`, FLOOKUP_UPDATE]) >>
  `st.cs_next_id < sd.cs_next_id` by
    (spose_not_then assume_tac >>
     `sd.cs_next_id <= st.cs_next_id` by decide_tac >>
     qpat_assum `!aid. sd.cs_next_id <= aid ==> _` (qspec_then `st.cs_next_id` mp_tac) >>
     asm_rewrite_tac[] >> fs[]) >>
  `st.cs_next_id NOTIN frag_ids sd st'` by simp[frag_ids_def] >>
  `B SUBSET range_bytes [(initial.vs_alloca_next,type_memory_bytes ce0 h1)]` by fs[] >>
  `!a. a IN B ==> mem_bytes_at a 1 actual.vs_memory = mem_bytes_at a 1 middle.vs_memory` by
    (drule_at (Pat `abi_encoder_registered_effect _ _ middle actual`)
       entry_origins_retained_slot_bytes >>
     disch_then (drule_at (Pat `FLOOKUP middle.vs_allocas _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl [`entry`,`initial.vs_alloca_next`,`B`] >> asm_rewrite_tac[] >>
  conj_tac >- (first_x_assum irule >> asm_rewrite_tac[]) >>
  conj_tac >- (rpt strip_tac >> `a < middle.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  rpt strip_tac >> qpat_assum `!mem. _ ==> val_in_memory _ _ _ _` irule >>
  rpt strip_tac >> metis_tac[]
QED

Finalise prefix_entry_register_suffix_origins
