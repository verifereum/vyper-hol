Theory typedCopyTupleFieldsMem
Ancestors
  typedCopyFieldStepMem typedCopyFieldsPathMem typedNormalizeFields
  typedNormalizeFrame typedBytesArrayMem externalReturnNormalizeMem
  abiDecoderFrame context compileEnv emitHelper venomInst exprLoweringProps
  memContinuation venomState valueEncodingProps fragGasPathMem

Theorem fields_residual_index[local]:
  head::tail = DROP i xs ==>
  i < LENGTH xs /\ head = EL i xs /\ tail = DROP (SUC i) xs /\
  SUM (MAP f (TAKE (SUC i) xs)) = SUM (MAP f (TAKE i xs)) + f head
Proof
  strip_tac >>
  `i < LENGTH xs` by
    (qpat_assum `head::tail = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[listTheory.LENGTH_DROP] >> decide_tac) >>
  `head = EL i xs` by
    (qpat_assum `head::tail = _` (mp_tac o Q.AP_TERM `HD`) >>
     simp[listTheory.HD_DROP]) >>
  simp[] >> conj_tac
  >- (qpat_assum `head::tail = _` (mp_tac o Q.AP_TERM `DROP 1`) >>
      simp[rich_listTheory.DROP_DROP, arithmeticTheory.ADD1]) >>
  drule normalize_prefix_step >> simp[]
QED

Theorem fields_runtime_advance[local]:
  sa.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= se.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u) /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
    vs_prev_bb := s.vs_prev_bb|>) = s /\
  (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  eval_operand dst u = SOME b /\ eval_operand src u = SOME a /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sc x) ==>
  sa.cs_next_var <= se.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
  (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
    vs_prev_bb := s.vs_prev_bb|>) = s /\
  eval_operand dst v = SOME b /\ eval_operand src v = SOME a /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at se x)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
        vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
      qpat_x_assum `u with <|vs_vars := _; vs_memory := _;
        vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
      simp_tac (srw_ss()) [venom_state_component_equality]) >>
  `!x. dst = Var x \/ src = Var x ==> not_fresh_at se x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     qpat_x_assum `!x. dst = Var x \/ src = Var x ==> _` drule >>
     disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  simp[] >> Cases_on `dst` >> Cases_on `src` >>
  gvs[eval_operand_def, venom_state_component_equality] >> metis_tac[]
QED

Theorem normalize_indexed_field_child_path_mem[local]:
  i < N /\ dt = EL i DT /\ st = EL i ST /\
  d i = b + doff /\ h i = a + soff /\
  d (SUC i) <= s.vs_alloca_next /\ h (SUC i) <= s.vs_alloca_next /\
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa se fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ Src i s.vs_memory /\
  (!sd se dp sp u.
    i < N /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i ST) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    Src i u.vs_memory ==>
    ?v. gas_path_mem ctx fn u 0 (OK v) /\ Dst i v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) ==>
  ?v. gas_path_mem ctx fn s 0 (OK v) /\ Dst i v.vs_memory /\
    ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
    v.vs_inst_idx = LENGTH se.cs_current_insts /\
    abi_decode_footprint_frame [(d i,type_memory_bytes ce dt)] s v /\
    (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
    sa.cs_next_var <= se.cs_next_var /\
    (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >> irule normalize_field_child_path_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_with_byte_offset src _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_with_byte_offset dst _ _ = _`)) >>
  qexistsl_tac [`Src i`, `n2w b`, `n2w a`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
  `compile_store_memory_typed ce dp (EL i DT) sp (EL i ST) sd = ((),se)` by metis_tac[] >>
  qpat_x_assum `!sd se dp sp u. _`
    (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `u` mp_tac) >>
  simp[wordsTheory.word_add_n2w] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

Theorem normalize_tuple_fields_path_mem:
  LENGTH DT = N /\ LENGTH ST = N /\
  (!i. d i = b + d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (!i. h i = a + s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST))) /\
  abi_footprint_disjoint (h 0) (h N - h 0) [(d 0,d N - d 0)] /\
  d N <= s.vs_alloca_next /\ h N <= s.vs_alloca_next /\
  d N < dimword (:256) /\ h N < dimword (:256) /\
  (!i m m'. i < N /\
    mem_bytes_at (h i) (h (SUC i) - h i) m' =
      mem_bytes_at (h i) (h (SUC i) - h i) m /\ Src i m ==> Src i m') /\
  (!i m m'. i < N /\
    mem_bytes_at (d i) (d (SUC i) - d i) m' =
      mem_bytes_at (d i) (d (SUC i) - d i) m /\ Dst i m ==> Dst i m') /\
  (!i. i < N ==> Src i s.vs_memory) /\
  (!i sd se dp sp u.
    i < N /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i ST) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    Src i u.vs_memory ==>
    ?v. gas_path_mem ctx fn u 0 (OK v) /\ Dst i v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_typed_copy_fields ce dst src DT ST d0 s0 sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!i. i < N ==> Dst i t.vs_memory) /\
    abi_decode_footprint_frame [(d 0,d N - d 0)] s t /\
    mem_bytes_at (h 0) (h N - h 0) t.vs_memory =
      mem_bytes_at (h 0) (h N - h 0) s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    sa.cs_next_var <= sb.cs_next_var /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >>
  qabbrev_tac `Inv = \dt st doff soff sc u.
    ?i. i <= N /\ dt = DROP i DT /\ st = DROP i ST /\
      doff = d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT)) /\
      soff = s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST)) /\
      ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\ fn_has_code sc sb fn /\
      compile_typed_copy_fields ce dst src dt st doff soff sc = ((),sb) /\
      eval_operand dst u = SOME (n2w b) /\ eval_operand src u = SOME (n2w a) /\
      (!x. dst = Var x \/ src = Var x ==> not_fresh_at sc x) /\
      sa.cs_next_var <= sc.cs_next_var /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
        vs_prev_bb := s.vs_prev_bb|>) = s /\
      abi_decode_footprint_frame [(d 0,d i - d 0)] s u /\
      mem_bytes_at (h 0) (h N - h 0) u.vs_memory =
        mem_bytes_at (h 0) (h N - h 0) s.vs_memory /\
      (!j. j < i ==> Dst j u.vs_memory) /\
      (!j. j < N ==> Src j u.vs_memory)` >>
  `Inv DT ST d0 s0 sa s` by
    (simp[Abbr `Inv`] >> qexists_tac `0` >>
     simp[abi_decode_footprint_frame_def, venom_state_component_equality] >>
     asm_rewrite_tac[]) >>
  qsuff_tac `?t. gas_path_mem ctx fn s 0 (OK t) /\
    Inv [] [] (d0 + SUM (MAP (type_memory_bytes ce) DT))
      (s0 + SUM (MAP (type_memory_bytes ce) ST)) sb t`
  >- (strip_tac >> qexists_tac `t` >>
      qpat_x_assum `Inv DT ST _ _ _ _` kall_tac >>
      qpat_x_assum `!i sd se dp sp u. _` kall_tac >>
      qpat_x_assum `!i. d i = _` kall_tac >>
      qpat_x_assum `!i. h i = _` kall_tac >>
      qpat_x_assum `Inv [] [] _ _ sb t` mp_tac >>
      simp[Abbr `Inv`, listTheory.DROP_EQ_NIL] >> strip_tac >>
      `i = N` by decide_tac >> gvs[]) >>
  irule normalize_fields_sequence_path_mem >>
  conj_tac >- (simp[Abbr `Inv`] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`dst`, `sa`, `src`] >> simp[] >>
  rpt gen_tac >> strip_tac >> suspend "field_step"
QED

Resume normalize_tuple_fields_path_mem[field_step]:
  qpat_x_assum `Inv DT ST _ _ _ _` kall_tac >>
  qpat_x_assum `Inv (dt::dts) _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `Inv`] >> strip_tac >>
  `i < N /\ dt = EL i DT /\ st = EL i ST /\
   dts = DROP (SUC i) DT /\ sts = DROP (SUC i) ST /\
   SUM (MAP (type_memory_bytes ce) (TAKE (SUC i) DT)) =
     SUM (MAP (type_memory_bytes ce) (TAKE i DT)) + type_memory_bytes ce dt /\
   SUM (MAP (type_memory_bytes ce) (TAKE (SUC i) ST)) =
     SUM (MAP (type_memory_bytes ce) (TAKE i ST)) + type_memory_bytes ce st` by
    metis_tac[fields_residual_index] >>
  `compile_typed_copy_fields ce dst src dts sts
    (doff + type_memory_bytes ce dt) (soff + type_memory_bytes ce st) se = ((),sb)` by
    (qpat_assum `compile_typed_copy_fields _ _ _ (_::_) _ _ _ _ = _`
       (strip_assume_tac o MATCH_MP normalize_fields_cons_states) >>
     metis_tac[pairTheory.PAIR_EQ]) >>
  drule_all normalize_fields_suffix_code >> strip_tac >>
  `cs_extends sd se /\ cs_extends se sb` by
    metis_tac[ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  imp_res_tac normalize_byte_offset_straight >>
  `cs_extends sa' se` by metis_tac[cs_extends_trans] >>
  suspend "indexed_child"
QED

Resume normalize_tuple_fields_path_mem[indexed_child]:
  `!j k. j <= k /\ k <= N ==> d j <= d k /\ h j <= h k` by
    (simp[] >> metis_tac[normalize_prefix_mono]) >>
  `d (SUC i) = d i + type_memory_bytes ce dt /\
   h (SUC i) = h i + type_memory_bytes ce st` by simp[] >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  `d (SUC i) <= s'.vs_alloca_next /\ h (SUC i) <= s'.vs_alloca_next` by
    (`SUC i <= N` by decide_tac >>
     qpat_assum `!j k. _` (qspecl_then [`SUC i`, `N`] mp_tac) >>
     (impl_tac >- decide_tac) >> strip_tac >> decide_tac) >>
  `d i = b + doff /\ h i = a + soff` by
    (qpat_assum `!i. d i = _` (qspec_then `i` mp_tac) >>
     qpat_assum `!i. h i = _` (qspec_then `i` mp_tac) >>
     qpat_assum `doff = _` mp_tac >> qpat_assum `soff = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC]) >>
  qpat_assum `!i sd se dp sp u. _` (qspec_then `i` assume_tac) >>
  qpat_assum `compile_store_memory_typed ce dp dt sp st sd = _`
    (mp_then (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`) mp_tac
      (Q.INST [`Src` |-> `Src`, `Dst` |-> `Dst`, `i` |-> `i`, `s` |-> `s'`]
        (SPEC_ALL normalize_indexed_field_child_path_mem))) >>
  disch_then (fn th => qpat_assum `compile_with_byte_offset src soff sc = _`
    (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `compile_with_byte_offset dst doff sa' = _`
    (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac th)) >>
  disch_then (mp_tac o Q.INST [`s''` |-> `s'`] o SPEC_ALL) >>
  (impl_tac >- (asm_rewrite_tac [] >>
    qpat_assum `!j. j < N ==> Src j s'.vs_memory` irule >>
    first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  suspend "prefix_endpoint"
QED

Resume normalize_tuple_fields_path_mem[prefix_endpoint]:
  `d (SUC i) - d i = type_memory_bytes ce dt` by decide_tac >>
  `abi_decode_footprint_frame [(d i,d (SUC i) - d i)] s' v` by
    metis_tac[] >>
  drule_all normalize_fields_prefix_frame >> strip_tac >>
  `s' with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
     vs_prev_bb := s.vs_prev_bb|> = s` by
    (qpat_assum `s' with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  drule_all fields_runtime_advance >> strip_tac >>
  qpat_x_assum `!i. d i = _` kall_tac >>
  qpat_x_assum `!i. h i = _` kall_tac >>
  qexists_tac `v` >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `SUC i` >>
  asm_rewrite_tac [] >>
  conj_tac >- decide_tac >>
  pure_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
  qpat_assum `v with <|vs_vars := s.vs_vars; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
  simp_tac (srw_ss()) [venom_state_component_equality] >>
  metis_tac[]
QED

Finalise normalize_tuple_fields_path_mem
