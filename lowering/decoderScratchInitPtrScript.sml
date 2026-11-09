Theory decoderScratchInitPtr
Ancestors
  decoderArrayInitPtr abiScratchDecoderInitReentry
  abiDecoderArrayLoopInit abiDecoderArrayInit abiDecoderReentry
  compileEnv bodyPtrDefs ptrSafeRun ptrDiscipline abiDecoderContract
  abiDecoderArrayInitReentry venomState abiDecoderIndexInit words arithmetic
  abiScratchDecoderArray abiScratchDecoderContract abiDecoderLoop valueEncoding
  abiDecoderValidArrayMemory abiScratchDecoderTransport abiScratchEffect
  abiScratchDecoderLoopInput abiDecoderArrayInitExec exprLowering emitHelperProps fragExec
  abiScratchFootprint abiDecoderFootprint pred_set

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

(* Physical ownership and the ghost follow the same original-state execution.
   In particular generated names may already be bound at loop reentry. *)
Theorem calldata_scratch_array_init_reentry_ptr:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    maxn abi_sz st = (setup,loop_st) /\
  eval_operand src initial = SOME (n2w source_base) /\
  eval_operand (Var root) initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load CALLDATALOAD (n2w source_base:bytes32) initial = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ ptr_covers G tn root initial totalbytes /\
  32 <= totalbytes /\ op_taint tn src = {} ==>
  ?actual slot H u q.
    run_inst_seq (emitted_insts st loop_st) initial = OK actual /\
    inst_extends st loop_st /\
    abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id - 2)
      first last b cap d n initial actual /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
      limit_st d 32 b cap initial actual /\
    FST setup = Var q /\ eval_operand (FST setup) actual = SOME (n2w slot) /\
    b <= slot /\ slot + 32 <= b + cap /\ slot + 32 < dimword (:256) /\
    mload slot actual = 0w /\
    ptr_covers H u q
      (actual with vs_inst_idx := LENGTH (emitted_insts st loop_st) + initial.vs_inst_idx) 32 /\
    ptr_covers H u root
      (actual with vs_inst_idx := LENGTH (emitted_insts st loop_st) + initial.vs_inst_idx) totalbytes /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    frag_exec_ptr cx ctx PG st loop_st
      (\g z v. g = G /\ z = tn /\ v = initial)
      (\g z v. g = H /\ z = u /\
        v = (actual with vs_inst_idx := LENGTH (emitted_insts st loop_st) + initial.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem = (tn.t_mem DIFF {x | d <= x /\ x < d + 32})
      DIFF {x | slot <= x /\ x < slot + 32} /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code st loop_st func /\ allocas_from lower initial /\ lower <= initial.vs_alloca_next /\
      ~ctx_has_dalloca ctx' /\ initial.vs_current_bb = st.cs_current_bb /\
      initial.vs_inst_idx = LENGTH st.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (actual with vs_inst_idx := LENGTH loop_st.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD /\
   abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decode_source_opcode_def, abi_decoder_operand_live_def] >>
  `first <= abiDecoderTypedContract$abi_decoder_entry_floor st` by
    simp[abiDecoderTypedContractTheory.abi_decoder_entry_floor_def] >>
  drule_all ((calldata_pos abi_scratch_decoder_init_reentry) |> Q.INST [`hi` |-> `Lit 0w`] |> SRULE []) >> strip_tac >>
  `abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id - 2)
    first last b cap d n initial actual` by
    (simp_tac bool_ss [abi_decoder_array_init_post_def] >> qexists_tac `slot` >>
     asm_simp_tac bool_ss []) >>
  drule_all (calldata_pos abi_decode_array_loop_init_site_bounds) >> strip_tac >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d 32 b cap initial actual` by
    (irule abi_scratch_decoder_init_effect >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`n`, `setup`, `loop_st.cs_next_id - 2`] >> simp[]) >>
  `not_fresh_at st root /\ (!x. src = Var x ==> not_fresh_at st x)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  `lookup_var root initial = SOME (n2w d)` by fs[eval_operand_def] >>
  drule_all calldata_array_init_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] strip_assume_tac) >>
  `slot + 32 < dimword (:256)` by
    (drule abi_decoder_budget_word_bound >> decide_tac) >>
  `slot = p` by
    (gvs[] >> metis_tac[n2w_11, LESS_TRANS, DECIDE ``!x:num. x < x + 32``]) >>
  qexistsl_tac [`actual`, `slot`, `H`, `u`, `q`] >> gvs[]
QED

(* Source-valid caller of the joint physical/ghost initializer. *)
Theorem calldata_scratch_array_initialize_clean_ptr:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) maxn
    (abi_embedded_static_size ce.ce_struct_fields ty) st = (setup,loop_st) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
    0 source_base d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  op_taint tn src = {} /\ allocas_from lower initial /\ lower <= initial.vs_alloca_next /\
  ~ctx_has_dalloca ctx ==>
  ?actual slot H u q.
    abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      bs (ArrayV (DynArrayV vs)) loop_st src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
      0 source_base d first last b cap actual /\
    abi_decoder_valid_array_memory CALLDATALOAD bs tv vs source_base d 0 actual /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
      limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    FLOOKUP actual.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    eval_operand (FST setup) actual = SOME (n2w slot) /\ mload slot actual = 0w /\
    eval_operand (SND setup) actual = SOME (n2w (LENGTH vs)) /\
    abi_decoder_operand_live loop_st.cs_next_var (FST setup) /\
    actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    FST setup = Var q /\ ptr_covers H u q actual 32 /\
    ptr_covers H u root actual (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    b <= slot /\ slot + 32 <= b + cap /\ slot + 32 < dimword (:256) /\
    DISJOINT {a | d <= a /\ a < d + 32} u.t_mem /\
    DISJOINT {a | slot <= a /\ a < slot + 32} u.t_mem /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (calldata_pos abi_scratch_decoder_array_init_inputs) >> simp[] >> strip_tac >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[Once type_memory_bytes_def] >>
  drule_all calldata_scratch_array_init_reentry_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`R`,`PG`] strip_assume_tac) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac >>
  drule_all (calldata_pos abi_decode_array_loop_init_shape) >> strip_tac >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `loop_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `32`] >> simp[]) >>
  `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
    0 source_base d first last b cap actual` by
    (irule (calldata_pos abi_scratch_decoder_input_effect) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) loop_st src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
    0 source_base d first last b cap actual` by
    (irule (calldata_pos abi_scratch_decoder_input_mono) >> qexists_tac `st` >> fs[inst_extends_def]) >>
  `mem_bytes_at source_base (LENGTH bs) (abi_decode_source CALLDATALOAD actual) = bs` by
    fs[abi_scratch_decoder_input_def, cj 1 venomStateTheory.eval_operand_def] >>
  `abi_decoder_valid_array_memory CALLDATALOAD bs tv vs source_base d 0 actual` by
    (irule abi_decoder_valid_array_memory_init >>
     fs[abi_decoder_array_init_post_def]) >>
  `frag_exec ctx st loop_st (\s. s = initial)
    (\s. s = actual with vs_inst_idx := LENGTH loop_st.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> qexists_tac `actual` >> simp[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  `LENGTH (emitted_insts st loop_st) + initial.vs_inst_idx = LENGTH loop_st.cs_current_insts` by
    (fs[inst_extends_def] >> simp[ADD_COMM]) >>
  drule (calldata_pos abi_decode_array_loop_index_live) >> strip_tac >>
  qexistsl_tac [`actual with vs_inst_idx := LENGTH loop_st.cs_current_insts`, `slot`, `H`, `u`] >>
  gvs[abi_decoder_array_init_post_def, abi_scratch_decoder_input_def,
    abi_scratch_decoder_ranges_def, abi_decoder_valid_array_memory_def,
    abi_decoder_child_scratch_def, abi_decode_source_def, mload_def,
    lookup_var_def, ptr_covers_def, SUBSET_DEF, DISJOINT_DEF, EXTENSION, cj 1 venomStateTheory.eval_operand_def] >>
  drule abi_decoder_budget_word_bound >> decide_tac
QED

(* Compatibility projection: initialization has one operational proof. *)
Theorem calldata_scratch_array_initialize_ptr:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) maxn
    (abi_embedded_static_size ce.ce_struct_fields ty) st = (setup,loop_st) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
    0 source_base d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  op_taint tn src = {} /\ allocas_from lower initial /\ lower <= initial.vs_alloca_next /\
  ~ctx_has_dalloca ctx ==>
  ?actual slot H u q.
    abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      bs (ArrayV (DynArrayV vs)) loop_st src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
      0 source_base d first last b cap actual /\
    abi_decoder_valid_array_memory CALLDATALOAD bs tv vs source_base d 0 actual /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
      limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    FLOOKUP actual.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    eval_operand (FST setup) actual = SOME (n2w slot) /\ mload slot actual = 0w /\
    eval_operand (SND setup) actual = SOME (n2w (LENGTH vs)) /\
    abi_decoder_operand_live loop_st.cs_next_var (FST setup) /\
    actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    FST setup = Var q /\ ptr_covers H u q actual 32 /\
    ptr_covers H u root actual (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    op_taint u (SND setup) = {} /\ op_prov H (SND setup) = NONE /\
    b <= slot /\ slot + 32 <= b + cap /\ slot + 32 < dimword (:256) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_scratch_array_initialize_clean_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`actual`, `slot`, `H`, `u`, `q`] >> asm_rewrite_tac[]
QED
