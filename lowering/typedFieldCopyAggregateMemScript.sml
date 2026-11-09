Theory typedFieldCopyAggregateMem
Ancestors
  typedFieldCopyCuts typedFieldCopyPathsMem typedArrayCopyPathsMem
  typedNormalizeFields fragGasPathMem abiDecoderFrame venomState
  context compileEnv venomInst venomExecSemantics valueEncodingProps words
  exprLoweringProps

Theorem normalize_fields_prefix_path_mem[local]:
  (!j k. j <= k /\ k <= N ==> d j <= d k /\ h j <= h k) /\
  abi_footprint_disjoint (h 0) (h N - h 0) [(d 0,d N - d 0)] /\
  (!j m m'. j < N /\
    mem_bytes_at (h j) (h (SUC j) - h j) m' =
      mem_bytes_at (h j) (h (SUC j) - h j) m /\ Src j m ==> Src j m') /\
  (!j m m'. j < N /\
    mem_bytes_at (d j) (d (SUC j) - d j) m' =
      mem_bytes_at (d j) (d (SUC j) - d j) m /\ Dst j m ==> Dst j m') /\
  (!j. j < N ==> Src j s.vs_memory) /\ RunInv 0 s /\ ~s.vs_halted /\
  (!i u. i < N /\ RunInv i u /\ ~u.vs_halted /\ Src i u.vs_memory ==>
    ?n v. gas_path_mem ctx fn u n (OK v) /\ RunInv (SUC i) v /\
      ~v.vs_halted /\ Dst i v.vs_memory /\
      abi_decode_footprint_frame [(d i,d (SUC i) - d i)] u v) ==>
  ?n t. gas_path_mem ctx fn s n (OK t) /\ RunInv N t /\ ~t.vs_halted /\
    (!j. j < N ==> Dst j t.vs_memory) /\
    abi_decode_footprint_frame [(d 0,d N - d 0)] s t /\
    mem_bytes_at (h 0) (h N - h 0) t.vs_memory =
      mem_bytes_at (h 0) (h N - h 0) s.vs_memory
Proof
  strip_tac >>
  qabbrev_tac `Inv = \i u. RunInv i u /\ ~u.vs_halted /\
    (!j. j < N ==> Src j u.vs_memory) /\
    (!j. j < i ==> Dst j u.vs_memory) /\
    abi_decode_footprint_frame [(d 0,d i - d 0)] s u /\
    mem_bytes_at (h 0) (h N - h 0) u.vs_memory =
      mem_bytes_at (h 0) (h N - h 0) s.vs_memory` >>
  `Inv 0 s` by
    simp[Abbr `Inv`, abi_decode_footprint_frame_def] >>
  `!i u. Inv i u /\ i < N ==>
    ?n v. gas_path_mem ctx fn u n (OK v) /\ Inv (SUC i) v /\ ~v.vs_halted` by
    (rpt gen_tac >> simp[Abbr `Inv`] >> strip_tac >>
     `Src i u.vs_memory` by metis_tac[] >>
     qpat_x_assum `!i u. i < N /\ RunInv i u /\ _ ==> _` drule_all >> strip_tac >>
     drule_all normalize_fields_prefix_frame >> strip_tac >>
     qexistsl_tac [`n`, `v`] >> simp[]) >>
  `?n t. gas_path_mem ctx fn s n (OK t) /\ Inv N t /\ ~t.vs_halted` by
    (irule gas_path_mem_finite_iteration >> simp[] >>
     qexists_tac `0` >> simp[]) >>
  goal_assum (drule_at Any) >> gvs[Abbr `Inv`] >> metis_tac[]
QED

Theorem normalize_tuple_fields_memory_path_mem:
  LENGTH DT = N /\ LENGTH ST = N /\
  (!i. d i = b + d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (!i. h i = a + s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST))) /\
  abi_footprint_disjoint (h 0) (h N - h 0) [(d 0,d N - d 0)] /\
  d N <= s.vs_alloca_next /\ h N <= s.vs_alloca_next /\
  d N < dimword (:256) /\ h N < dimword (:256) /\
  (!i. i < N ==> val_wf (TS i) (VS i) /\
    type_memory_size (TS i) <= h (SUC i) - h i) /\
  (!i. i < N ==> val_wf (TD i) (VD i) /\
    type_memory_size (TD i) <= d (SUC i) - d i) /\
  (!i. i < N ==> val_in_memory (TS i) (VS i) (h i) s.vs_memory) /\
  (!i sd se dp sp u.
    i < N /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i ST) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    val_in_memory (TS i) (VS i) (h i) u.vs_memory ==>
    ?n v. gas_path_mem ctx fn u n (OK v) /\
      val_in_memory (TD i) (VD i) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_typed_copy_fields ce dst src DT ST d0 s0 sa = ((),sb) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?n t. gas_path_mem ctx fn s n (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!i. i < N ==> val_in_memory (TD i) (VD i) (d i) t.vs_memory) /\
    abi_decode_footprint_frame [(d 0,d N - d 0)] s t /\
    mem_bytes_at (h 0) (h N - h 0) t.vs_memory =
      mem_bytes_at (h 0) (h N - h 0) s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    sa.cs_next_var <= sb.cs_next_var /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >> drule_all normalize_fields_compiler_cuts >> strip_tac >>
  qabbrev_tac `RunInv = \i u.
    u.vs_current_bb = (C i).cs_current_bb /\
    u.vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    sa.cs_next_var <= (C i).cs_next_var /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s` >>
  `!j k. j <= k /\ k <= N ==> d j <= d k /\ h j <= h k` by
    (rpt strip_tac >> simp[] >>
     metis_tac[normalize_prefix_mono, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  `RunInv 0 s` by simp[Abbr `RunInv`, venom_state_component_equality] >>
  `!i u. i < N /\ RunInv i u /\ ~u.vs_halted /\
    val_in_memory (TS i) (VS i) (h i) u.vs_memory ==>
    ?n v. gas_path_mem ctx fn u n (OK v) /\ RunInv (SUC i) v /\
      ~v.vs_halted /\ val_in_memory (TD i) (VD i) (d i) v.vs_memory /\
      abi_decode_footprint_frame [(d i,d (SUC i) - d i)] u v` by
    suspend "cut_step" >>
  `?n t. gas_path_mem ctx fn s n (OK t) /\ RunInv N t /\ ~t.vs_halted /\
    (!j. j < N ==> val_in_memory (TD j) (VD j) (d j) t.vs_memory) /\
    abi_decode_footprint_frame [(d 0,d N - d 0)] s t /\
    mem_bytes_at (h 0) (h N - h 0) t.vs_memory =
      mem_bytes_at (h 0) (h N - h 0) s.vs_memory` by
    suspend "prefix_fold" >>
  qexistsl_tac [`n`, `t`] >> gvs[Abbr `RunInv`]
QED

Resume normalize_tuple_fields_memory_path_mem[cut_step]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i. i < N ==> compile_with_byte_offset _ _ _ = _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `RunInv i u` mp_tac >>
  simp_tac bool_ss [Abbr `RunInv`] >> strip_tac >>
  `eval_operand dst u = SOME (n2w b) /\ eval_operand src u = SOME (n2w a)` by
    (`u.vs_labels = s.vs_labels` by
       (qpat_x_assum `_ = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     Cases_on `dst` >> Cases_on `src` >>
     fs[eval_operand_def] >> metis_tac[]) >>
  `!x. dst = Var x \/ src = Var x ==> not_fresh_at (C i) x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `d (SUC i) - d i = type_memory_bytes ce (EL i DT) /\
   h (SUC i) - h i = type_memory_bytes ce (EL i ST)` by
    (simp[normalize_prefix_step]) >>
  `d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next` by
    (`u.vs_alloca_next = s.vs_alloca_next` by
       gvs[venom_state_component_equality] >>
     qpat_assum `!j k. j <= k /\ k <= N ==> _`
       (qspecl_then [`SUC i`, `N`] mp_tac) >>
     (impl_tac >- decide_tac) >> strip_tac >> decide_tac) >>
  `!w. eval_operand (DP i) w = SOME (n2w b +
      n2w (d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT)))) /\
    eval_operand (SP i) w = SOME (n2w a +
      n2w (s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST)))) /\
    (!x. DP i = Var x \/ SP i = Var x ==> not_fresh_at (B i) x) /\
    fn_has_code (B i) (C (SUC i)) fn /\
    (emitted_blocks (B i) (C (SUC i)) <> [] ==>
      ?bb. lookup_block (C (SUC i)).cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~w.vs_halted /\
    w.vs_current_bb = (B i).cs_current_bb /\
    w.vs_inst_idx = LENGTH (B i).cs_current_insts /\
    w.vs_alloca_next = u.vs_alloca_next /\
    val_in_memory (TS i) (VS i) (h i) w.vs_memory ==>
    ?n v. gas_path_mem ctx fn w n (OK v) /\
      val_in_memory (TD i) (VD i) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = (C (SUC i)).cs_current_bb /\
      v.vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] w v /\
      (!x. not_fresh_at (B i) x ==> lookup_var x v = lookup_var x w) /\
      (B i).cs_next_var <= (C (SUC i)).cs_next_var /\
      (v with <|vs_vars := w.vs_vars; vs_memory := w.vs_memory;
        vs_current_bb := w.vs_current_bb; vs_inst_idx := w.vs_inst_idx;
        vs_prev_bb := w.vs_prev_bb|>) = w` by suspend "child_callback" >>
  drule_all normalize_field_child_path_mem >> strip_tac >>
  qexistsl_tac [`n`, `v`] >> simp[] >>
  suspend "cut_frame"
QED

Resume normalize_tuple_fields_memory_path_mem[child_callback]:
  rpt strip_tac >>
  qpat_x_assum `!i sd se dp sp u. _` irule >>
  asm_simp_tac bool_ss [] >>
  metis_tac[GSYM wordsTheory.word_add_n2w, arithmeticTheory.ADD_ASSOC]
QED

Resume normalize_tuple_fields_memory_path_mem[cut_frame]:
  reverse conj_tac
  >- (qpat_x_assum `abi_decode_footprint_frame _ u v` mp_tac >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at (C i) x` by
        (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  qpat_x_assum `_ = u` mp_tac >>
  qpat_x_assum `_ = s` mp_tac >>
  simp[venom_state_component_equality]
QED

Resume normalize_tuple_fields_memory_path_mem[prefix_fold]:
  qpat_x_assum `!i. d i = _` kall_tac >>
  qpat_x_assum `!i. h i = _` kall_tac >>
  irule (BETA_RULE (Q.INST
    [`Src` |-> `\j m. val_in_memory (TS j) (VS j) (h j) m`,
     `Dst` |-> `\j m. val_in_memory (TD j) (VD j) (d j) m`]
    normalize_fields_prefix_path_mem)) >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i < N ==> val_wf (TD i) _ /\ _` drule >> strip_tac >>
      irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
      qexistsl_tac [`d (SUC j) - d j`, `m`] >> simp[]) >>
  qexistsl_tac [`TS`, `VS`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < N ==> val_wf (TS i) _ /\ _` drule >> strip_tac >>
  irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
  qexistsl_tac [`h (SUC j) - h j`, `m`] >> simp[]
QED

Finalise normalize_tuple_fields_memory_path_mem

Theorem normalize_nominal_struct_fields_memory_path_mem:
  DT = MAP (FST o SND) fields /\ LENGTH fields = N /\
  (!name ty sz. MEM (name,ty,sz) fields ==>
    ALOOKUP src_fields name = SOME (ty,sz) /\ sz = type_memory_bytes ce ty) /\
  (!i. d i = b + d0 + SUM (MAP (SND o SND) (TAKE i fields))) /\
  (!i. h i = a + s0 + SUM (MAP (SND o SND) (TAKE i fields))) /\
  abi_footprint_disjoint (h 0) (h N - h 0) [(d 0,d N - d 0)] /\
  d N <= s.vs_alloca_next /\ h N <= s.vs_alloca_next /\
  d N < dimword (:256) /\ h N < dimword (:256) /\
  (!i. i < N ==> val_wf (TS i) (VS i) /\
    type_memory_size (TS i) <= h (SUC i) - h i) /\
  (!i. i < N ==> val_wf (TD i) (VD i) /\
    type_memory_size (TD i) <= d (SUC i) - d i) /\
  (!i. i < N ==> val_in_memory (TS i) (VS i) (h i) s.vs_memory) /\
  (!i sd se dp sp u.
    i < N /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i DT) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    val_in_memory (TS i) (VS i) (h i) u.vs_memory ==>
    ?n v. gas_path_mem ctx fn u n (OK v) /\ val_in_memory (TD i) (VD i) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_struct_typed_copy ce dst src fields src_fields d0 s0 sa = ((),sb) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?n t. gas_path_mem ctx fn s n (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!i. i < N ==> val_in_memory (TD i) (VD i) (d i) t.vs_memory) /\
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
  `compile_typed_copy_fields ce dst src DT DT d0 s0 sa = ((),sb)` by
    (drule normalize_struct_as_fields >> simp[] >> metis_tac[]) >>
  `!i. SUM (MAP (SND o SND) (TAKE i fields)) =
    SUM (MAP (type_memory_bytes ce) (TAKE i DT))` by
    (gen_tac >> asm_rewrite_tac[] >>
     irule normalize_struct_prefix_sizes >> metis_tac[]) >>
  irule normalize_tuple_fields_memory_path_mem >>
  asm_simp_tac bool_ss [] >>
  qexistsl_tac [`DT`, `DT`, `TS`, `VS`, `a`, `b`, `ce`, `d0`, `dst`, `s0`, `src`] >>
  gvs[listTheory.LENGTH_MAP] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!i sd se dp sp u. _` mp_tac >> simp[]
QED
