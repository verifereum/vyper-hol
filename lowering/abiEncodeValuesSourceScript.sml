Theory abiEncodeValuesSource
Ancestors
  abiEncoderWindow
  abiEncoderSourceRobust abiEncoderLiveSource abiEncoderWindowJoint
  abiEncoderWindowPhase abiEncoderWindowContract exprSimAbiEncodeExecFrame
  abiEncoderSourceInvoke abiEncoderAdmissible abiEncoderProps abiEncoderOpenInput entryDecodePlanProps
  exprSimAbiEncodeSiteResources allocationPtr allocaSiteResource stateRelProj
  fragGasOriginPtr bodyPtrDefs ptrDiscipline fragExec
  exprLoweringProps exprSimProps exprSimMemDefs loweringPosts
  loweringStateRelDefs exprLowering context compileEnv vyperContext
  valueEncodingProps valueEncodingDefs vyperABI vyperValue vyperTyping contractABI
  venomState venomInst venomMemDefs words finite_map list pred_set


(* Choose one representative for all memories that agree on the live source. *)
Theorem abi_encode_values_plan_window_input:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tainted initial_mem mem ==> val_in_memory tv v sb mem) ==>
  abi_encoder_admissible ei /\
  ?ct rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    !mem. mem_agree_outside tainted initial_mem mem ==>
      abi_encoder_window_input ei ct rv sb (val_footprint tv v) mem
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  conj_tac >- metis_tac[cj 1 abi_enc_plan_admissible] >>
  drule_all abi_encoder_source_window_robust >>
  disch_then (qx_choosel_then [`ct`,`rv`] strip_assume_tac) >>
  qexistsl_tac [`ct`,`rv`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_values_source_window_input:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_admissible ei /\
  (?ct rv. enc ct rv = bs /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input ei ct rv sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH bs <= s.vs_alloca_next /\
  (0 < LENGTH bs ==> ?p. dst = Var p /\ ptr_covers G tn p s (LENGTH bs)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH bs) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
    eval_operand out t = SOME (n2w (LENGTH bs)) /\
    window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH bs)] s t /\ abi_encode_exec_frame func s t /\
    op_taint tn' out = {} /\ (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH bs <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ct rv. enc ct rv = bs /\ _`
    (qx_choosel_then [`ct`,`rv`] strip_assume_tac) >>
  mp_tac (Q.INST [`at` |-> `ct`, `av` |-> `rv`, `explicit` |-> `explicit`, `PG` |-> `PG`]
    (SPEC_ALL compile_abi_encode_to_buf_window_joint)) >>
  impl_tac
  >- (qpat_assum `enc ct rv = bs` (fn th => PURE_REWRITE_TAC [th]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH bs)] s t` by metis_tac[window_phase_strong_result] >>
  `mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
   eval_operand out t = SOME (n2w (LENGTH bs))` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  qpat_assum `enc ct rv = bs` (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]
QED

Theorem abi_encode_values_source_window:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v sb mem) /\
  bs = enc (vyper_to_abi_type env ty) av /\ cap = val_footprint tv v /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH bs <= s.vs_alloca_next /\
  (0 < LENGTH bs ==> ?p. dst = Var p /\ ptr_covers G tn p s (LENGTH bs)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH bs) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
    eval_operand out t = SOME (n2w (LENGTH bs)) /\
    window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH bs)] s t /\ abi_encode_exec_frame func s t /\
    op_taint tn' out = {} /\ (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH bs <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_values_plan_window_input >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  mp_tac abi_encode_values_source_window_input >>
  impl_tac >-
    (qpat_x_assum `bs = _` SUBST_ALL_TAC >>
     qpat_x_assum `cap = _` SUBST_ALL_TAC >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_encode_values_typed_layout:
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  (~is_dynamic (vyper_to_abi_type env ty) ==>
    type_memory_size tv = static_length (vyper_to_abi_type env ty)) ==>
  abi_encoder_layout_valid (vyper_to_abi_type env ty) av
Proof
  rw[abi_encoder_layout_valid_def] >>
  drule_all (cj 1 vyper_to_abi_static_enc_length) >> simp[]
QED

Theorem abi_encode_values_static_footprint:
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  val_footprint tv v = type_memory_size tv
Proof
  strip_tac >> CCONTR_TAC >> drule_all abi_source_non_nominal_forms >>
  disch_then strip_assume_tac >>
  gvs[vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def]
QED

(* The materialized row covers the bytes the recursive encoder can read,
   even when a bounded bytes literal occupies less than its nominal size. *)
Theorem abi_encode_values_memory_operand:
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_val_rel cx ty v src s /\ ptr_val_ok cx ty v src G tn s /\
  expr_store_bound cx ty v src s ==>
  ?w. eval_operand src s = SOME w /\ op_taint tn src = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
    (0 < val_footprint tv v ==>
      w2n w + val_footprint tv v <= s.vs_alloca_next /\
      ?p. src = Var p /\ ptr_covers G tn p s (val_footprint tv v))
Proof
  simp[expr_val_rel_def, ptr_val_ok_def, ptr_mem_ok_def, expr_store_bound_def] >>
  strip_tac >> qexists_tac `w` >> simp[] >>
  strip_tac >>
  `val_footprint tv v <= val_store_size tv v` by simp[val_footprint_le_store_size] >>
  conj_tac >- (res_tac >> decide_tac) >>
  `val_store_size tv v <> 0 /\ val_footprint tv v <> 0` by decide_tac >>
  `w2n w + val_store_size tv v <= s.vs_alloca_next` by metis_tac[] >>
  `?p b n. src = Var p /\ FLOOKUP G p = SOME (b,n) /\ b <= w2n w /\
    w2n w + val_store_size tv v <= b + n` by metis_tac[] >>
  qexists_tac `p` >> fs[ptr_covers_def, eval_operand_def] >> decide_tac
QED

(* The real source footprint avoids any registered allocation outside its
   ownership interval, including an older output allocation and newer scratch. *)
Theorem abi_encode_values_source_separation:
  stmt_state_rel H ctx func ce cx ee s /\
  expr_val_at ce cx ty sa sb ee v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME w /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce ee.scopes x /\
  (inst.inst_id < sa.cs_next_id \/ sb.cs_next_id <= inst.inst_id) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  0 < val_footprint tv v ==>
  venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,n)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> ~(b <= i /\ i < b+n)` by
    (gen_tac >> strip_tac >>
     qspecl_then [`ctx`,`func`,`ce`,`cx`,`ty`,`sa`,`sb`,`ee`,`v`,`src`,
       `s`,`tv`,`w`,`inst`,`x`,`b`,`n`,`i`] mp_tac expr_val_at_alloca_disjoint >>
     disch_then irule >> asm_rewrite_tac[]) >>
  simp[venomMemDefsTheory.regions_disjoint_def] >>
  qpat_assum `!i. w2n w <= i /\ _ ==> _` (fn th =>
    MAP_EVERY (fn q => qspec_then q mp_tac th) [`b`, `w2n w`]) >>
  decide_tac
QED

(* Unwrapped sources and argument snapshots have different allocation
   intervals. Either interval excludes the already registered destination. *)
Theorem abi_encode_values_source_destination:
  stmt_state_rel H ctx func ce cx ee s /\
  expr_val_at ce cx ty sa sb ee v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME w /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce ee.scopes x /\
  (inst.inst_id < sa.cs_next_id \/ sb.cs_next_id <= inst.inst_id) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  b <= d /\ d + len <= b + n ==>
  venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (d,len)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `val_footprint tv v = 0`
  >- simp[venomMemDefsTheory.regions_disjoint_def] >>
  `0 < val_footprint tv v` by decide_tac >>
  drule_all abi_encode_values_source_separation >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_encode_values_memory_source:
  stmt_state_rel H ctx func ce cx ee s /\
  expr_val_at ce cx ty sa sb ee v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  expr_val_rel cx ty v src s /\ ptr_val_ok cx ty v src G tn s /\
  expr_store_bound cx ty v src s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce ee.scopes x /\
  (inst.inst_id < sa.cs_next_id \/ sb.cs_next_id <= inst.inst_id) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  b <= d /\ d + len <= b + n ==>
  ?w. eval_operand src s = SOME w /\ op_taint tn src = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
    (0 < val_footprint tv v ==>
      w2n w + val_footprint tv v <= s.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (d,len) /\
      ?p. src = Var p /\ ptr_covers G tn p s (val_footprint tv v))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_values_memory_operand >> strip_tac >>
  drule_all abi_encode_values_source_destination >> disch_tac >>
  qexists_tac `w` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disch_tac >> qpat_assum `0 < val_footprint tv v ==> _` (drule_then strip_assume_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac `p` >> simp[]
QED

Theorem abi_encode_values_scratch_separation:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func ce cx ee s /\ local_ptrs_reserved ce st /\
  expr_val_at ce cx ty sa sb ee v src s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand src s = SOME (n2w q) /\
  (0 < val_footprint tv v ==> q + val_footprint tv v <= s.vs_alloca_next) /\
  sb.cs_next_id <= st.cs_next_id /\
  FLOOKUP s.vs_allocas parent = SOME (b,sz) /\ parent < st.cs_next_id /\
  b <= d /\ d + n <= b + sz ==>
  !inst r len. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (r,len) ==>
    len = 32 /\
    (0 < val_footprint tv v ==>
      venomMemDefs$regions_disjoint (q,val_footprint tv v) (r,len)) /\
    venomMemDefs$regions_disjoint (d,n) (r,len)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?x. inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [x] /\
    not_local_ptr ce ee.scopes x` by
    (mp_tac (Q.INST [`ready` |-> `st`, `body_end` |-> `en`, `earlier` |-> `st`,
       `obs` |-> `func`, `i` |-> `inst`, `scopes` |-> `ee.scopes`]
         (SPEC_ALL abi_encode_compiled_scratch_site)) >>
     simp[]) >>
  `len = 32` by
    (`32 < dimword (:256)` by
       (irule vyperArithTheory.lt_dimword_256 >> qexists_tac `64` >> simp[]) >>
     drule stmt_state_rel_alloca_size >>
     disch_then (qspecl_then [`inst`,`32w:bytes32`,`r`,`len`] mp_tac) >> simp[]) >>
  `st.cs_next_id <= inst.inst_id` by fs[frag_ids_def] >>
  `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
  `venomMemDefs$regions_disjoint (b,sz) (r,len)` by
    (`parent <> inst.inst_id` by decide_tac >>
     metis_tac[alloca_site_registered_disjoint]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (strip_tac >>
      `q < dimword (:256)` by (drule_all stmt_state_rel_alloca_room >> strip_tac >>
        drule alloca_room_next_lt >> decide_tac) >>
      `sb.cs_next_id <= inst.inst_id` by decide_tac >>
      `venomMemDefs$regions_disjoint (w2n (n2w q : bytes32),val_footprint tv v) (r,len)` by
        (irule abi_encode_values_source_separation >>
         qpat_assum `stmt_state_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `MEM inst (fn_insts func)` (irule_at Any) >>
         qexists_tac `x` >> asm_rewrite_tac[]) >>
      `w2n (n2w q : bytes32) = q` by
        (pure_rewrite_tac [w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
      qpat_assum `w2n (n2w q : bytes32) = q` (fn addr =>
        qpat_assum `len = 32` (fn sz_eq =>
          qpat_assum `venomMemDefs$regions_disjoint (w2n (n2w q : bytes32),_) _`
            (ACCEPT_TAC o REWRITE_RULE [addr, sz_eq])))) >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Identity unwraps keep their original ownership interval. Newly copied
   sources have the interval of the actual unwrap, which follows the buffer. *)
Theorem abi_encode_values_unwrap_source_cuts:
  unwrap_value ce saved st = (src,en) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ p.ptr_location <> LocMemory)) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_at ce cx ty sa sb ee raw saved s /\
  (!p. saved = LocatedValue ty p /\ p.ptr_location <> LocMemory ==>
    expr_val_at ce cx ty st en ee v src s) /\
  ~is_word_type ty ==>
  (src = vv_operand saved /\ en = st /\ expr_val_at ce cx ty sa sb ee v src s) \/
  expr_val_at ce cx ty st en ee v src s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `saved`
  >- (disj1_tac >> gvs[unwrap_value_def, comp_return_def, vv_at_def,
      contextTheory.vv_operand_def]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (disj1_tac >> gvs[unwrap_value_def, comp_return_def, vv_at_def,
      contextTheory.vv_operand_def, expr_val_at_def] >> metis_tac[]) >>
  disj2_tac >> gvs[]
QED
