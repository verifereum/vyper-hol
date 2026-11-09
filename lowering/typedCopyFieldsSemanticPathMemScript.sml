(* Representation reconstruction at the counted field traversal endpoint. *)
Theory typedCopyFieldsSemanticPathMem
Ancestors
  typedCopyTupleFieldsMem typedNormalizeTupleSemanticMem
  typedNormalizeStructSemanticMem typedNormalizeFields valueEncodingProps
  typedNormalizeFieldRepresentation typedNormalizeFrame typedMemoryCopy
  exprLoweringProps tupleMemoryLayout list rich_list arithmetic words venomState
  venomExecSemantics abiDecoderFrame tupleTypedLoad valueEncodingProofs
  typedNormalizeLayout

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
    ?v. gas_path_mem ctx fn u 0 (OK v) /\
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
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
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
  ho_match_mp_tac (Q.INST [`Src` |-> `\i m. val_in_memory (TS i) (VS i) (h i) m`]
    normalize_tuple_fields_path_mem) >>
  simp_tac bool_ss [] >>
  ntac 9 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i < N ==> val_wf (TS i) _ /\ _` drule >> strip_tac >>
      irule val_in_memory_mem_agree >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`h (SUC i) - h i`,`m`] >> asm_rewrite_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i < N ==> val_wf (TD i) _ /\ _` drule >> strip_tac >>
      irule val_in_memory_mem_agree >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`d (SUC i) - d i`,`m`] >> asm_rewrite_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `!i sd se dp sp u. _` mp_tac >> simp_tac bool_ss []) >>
  rpt conj_tac >> asm_rewrite_tac[] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem normalize_tuple_semantic_path_mem:
  LENGTH DT = LENGTH ST /\ LENGTH DT = LENGTH dtvs /\
  LENGTH ST = LENGTH stvs /\ LENGTH vs = LENGTH DT /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) DT dtvs /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) ST stvs /\
  EVERY2 val_wf stvs vs /\ EVERY2 val_wf dtvs vs /\
  (!i. d i = b + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (!i. h i = a + SUM (MAP (type_memory_bytes ce) (TAKE i ST))) /\
  (h (LENGTH DT) <= b \/ d (LENGTH DT) <= a) /\
  d (LENGTH DT) <= s.vs_alloca_next /\ h (LENGTH DT) <= s.vs_alloca_next /\
  d (LENGTH DT) < dimword (:256) /\ h (LENGTH DT) < dimword (:256) /\
  tuple_in_memory vs stvs a s.vs_memory /\
  (!i sd se dp sp u.
    i < LENGTH DT /\
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
    d i + type_memory_size (EL i dtvs) < dimword (:256) /\
    h i + type_memory_size (EL i stvs) < dimword (:256) /\
    (h i + type_memory_size (EL i stvs) <= d i \/
      d i + type_memory_size (EL i dtvs) <= h i) /\
    val_in_memory (EL i stvs) (EL i vs) (h i) u.vs_memory ==>
    ?v. gas_path_mem ctx fn u 0 (OK v) /\
      val_in_memory (EL i dtvs) (EL i vs) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      (!p k. p+k <= d i \/ d i+type_memory_size (EL i dtvs) <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_typed_copy_fields ce dst src DT ST 0 0 sa = ((),sb) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tuple_in_memory vs dtvs b t.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_size_list dtvs <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!i sd se dp sp u. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Child ==> _` >> disch_tac >>
  mp_tac (Q.INST [`TS` |-> `\i. EL i stvs`, `TD` |-> `\i. EL i dtvs`,
    `VS` |-> `\i. EL i vs`, `VD` |-> `\i. EL i vs`,
    `N` |-> `LENGTH DT`, `d0` |-> `0`, `s0` |-> `0`]
    normalize_tuple_fields_memory_path_mem) >>
  (impl_tac >- (simp_tac bool_ss [] >>
    (conj_tac >- metis_tac[]) >>
    ntac 2 (conj_tac >- simp[ADD_CLAUSES]) >>
    (conj_tac >- (gvs[abi_footprint_disjoint_def] >> decide_tac)) >>
    ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- suspend "source_sizes") >>
    (conj_tac >- suspend "dest_sizes") >>
    (conj_tac >- suspend "source") >>
    (conj_tac >- suspend "child") >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `t` >>
  qpat_x_assum `Child` kall_tac >> qpat_x_assum `Abbrev (Child = _)` kall_tac >>
  simp[] >> conj_tac >- suspend "reconstruct" >>
  suspend "frame"
QED
Resume normalize_tuple_semantic_path_mem[source_sizes]:
  gen_tac >> disch_tac >> conj_tac
  >- (gvs[LIST_REL_EL_EQN]) >>
  `i < LENGTH ST` by simp[] >>
  qpat_assum `i < LENGTH ST`
    (mp_then Any (qspec_then `type_memory_bytes ce` assume_tac) normalize_prefix_step) >>
  gvs[LIST_REL_EL_EQN]
QED
Resume normalize_tuple_semantic_path_mem[dest_sizes]:
  gen_tac >> disch_tac >> conj_tac
  >- (gvs[LIST_REL_EL_EQN]) >>
  drule normalize_prefix_step >>
  disch_then (qspec_then `type_memory_bytes ce` assume_tac) >>
  gvs[LIST_REL_EL_EQN]
QED
Resume normalize_tuple_semantic_path_mem[source]:
  rpt strip_tac >> drule tuple_in_memory_EL >>
  disch_then (qspec_then `i` mp_tac) >>
  drule tuple_prefix_sizes >> disch_then (qspec_then `i` assume_tac) >> simp[]
QED
Resume normalize_tuple_semantic_path_mem[child]:
  rpt gen_tac >> strip_tac >>
  `d i + type_memory_size (EL i dtvs) = d (SUC i) /\
   d (SUC i) <= d (LENGTH DT) /\ b <= d i` by
    (irule normalize_tuple_child_interval >> conj_tac >- simp[] >>
     qexists_tac `ce` >> simp[]) >>
  `h i + type_memory_size (EL i stvs) = h (SUC i) /\
   h (SUC i) <= h (LENGTH ST) /\ a <= h i` by
    (irule normalize_tuple_child_interval >> conj_tac >- simp[] >>
     qexists_tac `ce` >> simp[]) >>
  `d i + type_memory_size (EL i dtvs) < dimword (:256) /\
   h i + type_memory_size (EL i stvs) < dimword (:256) /\
   (h i + type_memory_size (EL i stvs) <= d i \/
    d i + type_memory_size (EL i dtvs) <= h i)` by
    (`h (LENGTH ST) = h (LENGTH DT)` by metis_tac[] >> decide_tac) >>
  qpat_x_assum `Child` mp_tac >> simp_tac bool_ss [Abbr `Child`] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `u` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `v` >> simp[] >>
  `type_memory_bytes ce (EL i DT) = type_memory_size (EL i dtvs)` by
    (gvs[LIST_REL_EL_EQN]) >>
  rpt conj_tac >>
  (all_tac >>~- ([`abi_decode_footprint_frame _ _ _`],
    irule normalize_copy_window_frame >> simp[] >>
    gvs[venom_state_component_equality] >> metis_tac[ADD_COMM])) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  mp_tac (CONJUNCT1 ci_mono_typed_memory_family) >>
  simp[ci_mono_def] >> metis_tac[pairTheory.SND]
QED
Resume normalize_tuple_semantic_path_mem[reconstruct]:
  irule normalize_tuple_compiler_offsets >>
  conj_tac >- simp[] >> qexistsl_tac [`ce`, `DT`] >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!i. i < LENGTH DT ==> val_in_memory _ _ _ _`
    (qspec_then `j` mp_tac) >> simp[]
QED
Resume normalize_tuple_semantic_path_mem[frame]:
  qpat_assum `LIST_REL _ DT dtvs` (mp_then Any
    (qspec_then `LENGTH DT` assume_tac) tuple_prefix_sizes) >>
  `SUM (MAP (type_memory_bytes ce) DT) = type_memory_size_list dtvs` by
    (gvs[type_memory_size_list_sum, TAKE_LENGTH_TOO_LONG]) >>
  qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
  simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[ADD_COMM, GSYM type_memory_size_list_sum]
QED
Finalise normalize_tuple_semantic_path_mem

Theorem normalize_struct_semantic_path_mem:
  DT = MAP (FST o SND) fields /\ LENGTH DT = LENGTH tvs /\
  LENGTH vs = LENGTH DT /\ LENGTH names = LENGTH DT /\
  (!name ty sz. MEM (name,ty,sz) fields ==>
    ALOOKUP src_fields name = SOME (ty,sz) /\ sz = type_memory_bytes ce ty) /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) DT tvs /\
  EVERY2 val_wf tvs vs /\
  (!i. d i = b + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (!i. h i = a + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (h (LENGTH DT) <= b \/ d (LENGTH DT) <= a) /\
  d (LENGTH DT) <= s.vs_alloca_next /\ h (LENGTH DT) <= s.vs_alloca_next /\
  d (LENGTH DT) < dimword (:256) /\ h (LENGTH DT) < dimword (:256) /\
  fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) a s.vs_memory /\
  (!i sd se dp sp u.
    i < LENGTH DT /\
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
    d i + type_memory_size (EL i tvs) < dimword (:256) /\
    h i + type_memory_size (EL i tvs) < dimword (:256) /\
    (h i + type_memory_size (EL i tvs) <= d i \/
      d i + type_memory_size (EL i tvs) <= h i) /\
    val_in_memory (EL i tvs) (EL i vs) (h i) u.vs_memory ==>
    ?v. gas_path_mem ctx fn u 0 (OK v) /\
      val_in_memory (EL i tvs) (EL i vs) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      (!p k. p+k <= d i \/ d i+type_memory_size (EL i tvs) <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_struct_typed_copy ce dst src fields src_fields 0 0 sa = ((),sb) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) b t.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_size_list tvs <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >>
  `compile_typed_copy_fields ce dst src DT DT 0 0 sa = ((),sb)` by
    (drule normalize_struct_as_fields >>
     disch_then (qspecl_then [`src`,`dst`,`0`,`0`] mp_tac) >> simp[] >> metis_tac[]) >>
  `LENGTH names = LENGTH vs /\ LENGTH names = LENGTH tvs` by metis_tac[] >>
  `tuple_in_memory vs tvs a s.vs_memory` by
    (gvs[fields_in_memory_tuple, MAP_ZIP]) >>
  pure_rewrite_tac[fields_in_memory_tuple] >>
  `MAP SND (ZIP (names,vs)) = vs` by simp[MAP_ZIP] >>
  `MAP SND (ZIP (names,tvs)) = tvs` by simp[MAP_ZIP] >>
  qpat_x_assum `MAP SND (ZIP (names,vs)) = vs` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `MAP SND (ZIP (names,tvs)) = tvs` (fn th => rewrite_tac[th]) >>
  irule normalize_tuple_semantic_path_mem >>
  simp[] >>
  qexistsl_tac [`DT`, `DT`, `a`, `ce`, `d`, `dst`, `h`, `src`, `tvs`] >>
  gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
