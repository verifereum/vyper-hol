Theory calldataScratchArrayEntryPtr
Ancestors
  decoderScratchInitPtr calldataScratchLoopEntryPtr abiScratchDecoderLoopInput
  venomState compileEnv abiDecoderExecution abiDecoderLoop
  abiScratchEffect abiDecoderFrame abiDecoderReentry bodyPtrDefs ptrDiscipline
  abiScratchFootprint abiScratchEncoderContract abiDecoderContract abiDecoderAllocation pred_set finite_map

(* The calldata instance of trunk's position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`, `src_base` |-> `0:num`] th);

Theorem scratch_effect_allocas_from[local]:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  first <= lo /\ hi <= last /\ allocas_from lower s /\ lower <= s.vs_alloca_next ==>
  allocas_from lower t
Proof
  simp_tac bool_ss [abi_scratch_effect_def, abi_scratch_evolution_def, allocas_from_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP t.vs_allocas id = SOME (p,n)` >>
  Cases_on `id < lo \/ hi <= id`
  >- metis_tac[] >>
  `id IN abi_decoder_ids first last` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (first_x_assum drule_all >> strip_tac >> decide_tac) >>
  metis_tac[]
QED

Theorem calldata_scratch_array_constructor_entry_ptr:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) maxn
    (abi_embedded_static_size ce.ce_struct_fields ty) start = (setup,loop_st) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) start src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  loop_st.cs_next_id <= last /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ fn_has_code start loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ lower <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  compile_abi_decode_dyn_loop (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (FST setup) (SND setup) loop_st = ((),final) /\
  fn_has_code loop_st final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  first <= lo /\ lo <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < loop_st.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  ?actual slot H u q labels st ops middle end_st.
    abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      bs (ArrayV (DynArrayV vs)) loop_st src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
      0 sb d first last b cap actual /\
    abi_scratch_effect first last start.cs_next_id loop_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    abi_scratch_effect first last start.cs_next_id loop_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial
      (jump_to (FST labels) actual) /\
    FLOOKUP actual.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    eval_operand (FST setup) actual = SOME (n2w slot) /\ mload slot actual = 0w /\
    eval_operand (SND setup) actual = SOME (n2w (LENGTH vs)) /\ FST setup = Var q /\
    abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs CALLDATALOAD (Lit 0w) (Lit 0w)
      (Var q) src (Var root) 0 sb d slot first last b cap loop_st.cs_next_var actual /\
    abi_decode_loop_prefix (Var q) src CALLDATALOAD (Lit 0w) loop_st = (labels,st) /\
    abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    abi_decode_loop_suffix (Var q) (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
    abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var q)
      src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w) (FST labels) (SND (SND labels))
      (loop_st.cs_next_id+1) loop_st.cs_next_var first last lo hi loop_st.cs_next_var
      limit_st (loop_st.cs_next_id-2) /\
    abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot (loop_st.cs_next_id-2)
      first last lo hi loop_st.cs_next_var limit_st b cap actual (FST labels) 0
      (jump_to (FST labels) actual) /\
    ptr_covers H u q (jump_to (FST labels) actual) 32 /\
    ptr_covers H u root (jump_to (FST labels) actual)
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    b <= slot /\ slot+32 <= b+cap /\ slot+32 < dimword (:256) /\
    DISJOINT {a | d <= a /\ a < d+32} u.t_mem /\
    DISJOINT {a | slot <= a /\ a < slot+32} u.t_mem /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower (jump_to (FST labels) actual) /\
    abi_decode_sim ctx func initial (jump_to (FST labels) actual) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u (jump_to (FST labels) actual)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_scratch_array_initialize_clean_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual` by
    fs[abi_scratch_effect_def] >>
  `allocas_from lower actual` by
    (drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)
       scratch_effect_allocas_from >> simp[]) >>
  `first <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < last` by decide_tac >>
  drule_at (Pat `abi_scratch_decoder_input _ _ _ _ _ _ _ loop_st _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (calldata_pos abi_scratch_decoder_loop_input) >>
  disch_then drule_all >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `loop_st.cs_next_var <= loop_st.cs_next_var /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp actual)` by simp[] >>
  drule_all (calldata_scratch_compiled_loop_entry_ptr |> Q.INST
    [`lo` |-> `lo`, `hi` |-> `hi`, `next` |-> `loop_st.cs_next_var`,
     `site` |-> `loop_st.cs_next_id-2`]) >>
  disch_then (qspecl_then [`u`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
    `PG`, `H`, `D`] strip_assume_tac) >>
  qexistsl_tac [`actual`,`slot`,`H`,`u`,`q`,`labels`,`st`,`ops`,`middle`,`end_st`] >>
  qpat_assum `FST setup = Var q` (fn th => fs[GSYM th]) >>
  suspend "entry_frames"
QED

Resume calldata_scratch_array_constructor_entry_ptr[entry_frames]:
  conj_tac >- (irule abi_scratch_effect_jump >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- fs[ptr_covers_def, decoder_jump_fields, lookup_var_def] >>
  conj_tac >- fs[ptr_covers_def, decoder_jump_fields, lookup_var_def] >>
  `abi_decoder_operand_live start.cs_next_var src` by
    fs[abiScratchDecoderContractTheory.abi_scratch_decoder_input_def] >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (qpat_assum `abi_decoder_operand_live start.cs_next_var src` mp_tac >>
     qpat_assum `!x. not_fresh_at start x ==> _` mp_tac >>
     qpat_assum `op_taint tn src = {}` mp_tac >>
     qpat_assum `op_prov G src = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `src` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def,
       op_taint_def, op_prov_def] >> metis_tac[SPECIFICATION]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (fs[allocas_from_def, decoder_jump_fields] >> metis_tac[]) >>
  irule abi_decode_sim_trans >> qexists_tac `actual` >> asm_rewrite_tac[]
QED

Finalise calldata_scratch_array_constructor_entry_ptr
