Theory typedNormalizeFields
Ancestors
  typedNormalizeFrame typedBytesArrayMem externalReturnNormalizeMem abiDecoderFrame
  context compileEnv emitHelper venomInst exprLoweringProps memContinuation venomState
  valueEncodingProps typedNormalizeContinuation typedNormalizeEntryBoundary

(* Offsets are straight-line, even when the child they precede has a CFG. *)
Theorem normalize_byte_offset_straight:
  compile_with_byte_offset op off sa = (out,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  Cases_on `off = 0`
  >- simp[compile_with_byte_offset_def, comp_return_def, emitted_insts_def,
          cs_extends_refl] >>
  simp[compile_with_byte_offset_def, emit_op_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1, mk_inst_def,
      is_terminator_def, rich_listTheory.IS_PREFIX_APPEND, cs_extends_def]
QED

Theorem normalize_byte_offset_cont[local]:
  compile_with_byte_offset op off sa = (out,sb) /\
  eval_operand op s = SOME a /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. out = Var x ==> not_fresh_at sb x) /\
  ?t. mem_cont_sim ctx fn s t /\
      eval_operand out t = SOME (a + n2w off) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  drule_all normalize_byte_offset_run >> strip_tac >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >> simp[] >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (drule_all normalize_byte_offset_straight >> strip_tac >>
      irule typed_bytes_child_seq_cont >> simp[] >>
      qexists_tac `sa` >> simp[] >>
      drule normalize_byte_offset_mem_ok >> simp[]) >>
  drule_all normalize_byte_offset_straight >> strip_tac >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def]
QED

(* Expose the actual recursive child's compiler states; in particular the
   tail starts at the child's returned state, not at either offset state. *)
Theorem normalize_fields_cons_states:
  compile_typed_copy_fields ce dst src (dt::dts) (st::sts) doff soff sa =
    ((),sb) ==>
  ?dp sc sp sd se.
    compile_with_byte_offset dst doff sa = (dp,sc) /\
    compile_with_byte_offset src soff sc = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
    compile_typed_copy_fields ce dst src dts sts
      (doff + type_memory_bytes ce dt) (soff + type_memory_bytes ce st) se =
      ((),sb)
Proof
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  strip_tac >> metis_tac[pairTheory.PAIR, oneTheory.one]
QED

(* I carries the complete source and completed destination prefix.  The
   callback covers the two offset instructions followed by an arbitrary
   recursive child CFG.  No fixed fresh-counter increments are imposed. *)
Theorem normalize_fields_sequence[local]:
  (!dt st dts sts doff soff sa dp sc sp sd se s.
    Inv (dt::dts) (st::sts) doff soff sa s /\
    compile_with_byte_offset dst doff sa = (dp,sc) /\
    compile_with_byte_offset src soff sc = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
    ?t. mem_cont_sim ctx fn s t /\
        Inv dts sts (doff + type_memory_bytes ce dt)
          (soff + type_memory_bytes ce st) se t) ==>
  !dts sts doff soff sa sb s.
    LENGTH dts = LENGTH sts /\ Inv dts sts doff soff sa s /\
    compile_typed_copy_fields ce dst src dts sts doff soff sa = ((),sb) ==>
    ?t. mem_cont_sim ctx fn s t /\
        Inv [] [] (doff + SUM (MAP (type_memory_bytes ce) dts))
          (soff + SUM (MAP (type_memory_bytes ce) sts)) sb t
Proof
  disch_then (mk_asm "field_step") >> Induct_on `dts`
  >- (rpt gen_tac >> simp[Once compile_store_memory_typed_def,
        comp_return_def] >> strip_tac >> gvs[] >>
      qexists_tac `s` >> simp[mem_cont_sim_refl]) >>
  pop_assum (mk_asm "fields_ih") >>
  rpt gen_tac >> Cases_on `sts` >- simp[] >>
  strip_tac >> drule normalize_fields_cons_states >> strip_tac >>
  asm "field_step" drule_all >> strip_tac >>
  fs[listTheory.LENGTH] >>
  asm_x "fields_ih" drule_all >> strip_tac >>
  rename1 `Inv [] [] _ _ sb u` >> qexists_tac `u` >>
  conj_tac >- (irule mem_cont_sim_trans >> metis_tac[]) >>
  qpat_x_assum `Inv [] [] _ _ sb u` mp_tac >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem normalize_struct_cons_states[local]:
  ALOOKUP src_fields name = SOME (st,ssz) /\
  compile_struct_typed_copy ce dst src ((name,dt,dsz)::rest)
    src_fields doff soff sa = ((),sb) ==>
  ?dp sc sp sd se.
    compile_with_byte_offset dst doff sa = (dp,sc) /\
    compile_with_byte_offset src soff sc = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
    compile_struct_typed_copy ce dst src rest src_fields
      (doff + dsz) (soff + ssz) se = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> fs[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> fs[] >> pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
  strip_tac >> metis_tac[pairTheory.PAIR, oneTheory.one]
QED

(* Lookup stays explicit here.  The nominal-identity consumer must justify
   it using distinct names, rather than silently taking the fallback type. *)
Theorem normalize_struct_sequence[local]:
  (!name dt dsz rest doff soff sa dp sc sp sd se s st ssz.
    Inv ((name,dt,dsz)::rest) doff soff sa s /\
    ALOOKUP src_fields name = SOME (st,ssz) /\
    compile_with_byte_offset dst doff sa = (dp,sc) /\
    compile_with_byte_offset src soff sc = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
    ?t. mem_cont_sim ctx fn s t /\
        Inv rest (doff + dsz) (soff + ssz) se t) /\
  (!name dt dsz. MEM (name,dt,dsz) fields ==>
    ALOOKUP src_fields name = SOME (dt,dsz)) ==>
  !doff soff sa sb s.
    Inv fields doff soff sa s /\
    compile_struct_typed_copy ce dst src fields src_fields doff soff sa = ((),sb) ==>
    ?t. mem_cont_sim ctx fn s t /\
        Inv [] (doff + SUM (MAP (SND o SND) fields))
          (soff + SUM (MAP (SND o SND) fields)) sb t
Proof
  Induct_on `fields`
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once compile_store_memory_typed_def, comp_return_def] >>
      strip_tac >> gvs[] >> qexists_tac `s` >> simp[mem_cont_sim_refl]) >>
  pop_assum (mk_asm "struct_ih") >>
  gen_tac >> PairCases_on `h` >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "struct_step") assume_tac) >>
  rpt gen_tac >> strip_tac >>
  rename1 `Inv ((name,dt,dsz)::fields) doff soff sa s` >>
  `ALOOKUP src_fields name = SOME (dt,dsz)` by metis_tac[listTheory.MEM] >>
  drule_all normalize_struct_cons_states >> strip_tac >>
  asm "struct_step" drule_all >> strip_tac >>
  asm_x "struct_ih" mp_tac >>
  (impl_tac >- (conj_tac >- (asm "struct_step" ACCEPT_TAC) >>
     metis_tac[listTheory.MEM])) >>
  disch_then drule_all >> strip_tac >>
  rename1 `Inv [] _ _ sb u` >> qexists_tac `u` >>
  conj_tac >- (irule mem_cont_sim_trans >> metis_tac[]) >>
  qpat_x_assum `Inv [] _ _ sb u` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [listTheory.MAP, listTheory.SUM, combinTheory.o_THM,
     AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem normalize_field_offsets_cont[local]:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sd fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sa.cs_next_var <= sd.cs_next_var /\
  (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
  ?u. mem_cont_sim ctx fn s u /\
      eval_operand dp u = SOME (d + n2w doff) /\
      eval_operand sp u = SOME (p + n2w soff) /\
      ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
      u.vs_inst_idx = LENGTH sd.cs_current_insts /\
      (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> imp_res_tac normalize_byte_offset_straight >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_byte_offset_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `compile_with_byte_offset dst doff sa = _` kall_tac >>
  `eval_operand src t = SOME p` by
    (Cases_on `src` >> gvs[eval_operand_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `!x. src = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all normalize_byte_offset_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `mem_cont_sim ctx fn t u` >>
  `eval_operand dp u = SOME (d + n2w doff)` by
    (Cases_on `dp` >> gvs[eval_operand_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  conj_tac >- decide_tac >>
  conj_tac >- (rpt strip_tac >> gvs[not_fresh_at_def] >>
    metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexists_tac `u` >> simp[] >>
  conj_tac >- (irule mem_cont_sim_trans >> metis_tac[]) >>
  gvs[venom_state_component_equality]
QED

(* Only the recursive child is a semantic premise; offsets are executed here. *)
Theorem normalize_field_child_cont[local]:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  (emitted_blocks sa se <> [] ==>
    ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa se fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  Src s.vs_memory /\
  (!u. eval_operand dp u = SOME (d + n2w doff) /\
    eval_operand sp u = SOME (p + n2w soff) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    u.vs_alloca_next = s.vs_alloca_next /\ Src u.vs_memory ==>
    ?v. mem_cont_sim ctx fn u v /\ D v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame fp u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) ==>
  ?v. mem_cont_sim ctx fn s v /\ D v.vs_memory /\
    ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
    v.vs_inst_idx = LENGTH se.cs_current_insts /\
    abi_decode_footprint_frame fp s v /\
    (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
    sa.cs_next_var <= se.cs_next_var /\
    (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >>
  `cs_extends sd se` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `dp`, `dt`, `sp`, `st`, `sd`] mp_tac) >>
     simp[ci_mono_def]) >>
  imp_res_tac normalize_byte_offset_straight >>
  `cs_extends sa sd` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sd fn /\ fn_has_code sd se fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all normalize_field_offsets_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  `emitted_blocks sd se = emitted_blocks sa se` by
    gvs[fragExecTheory.emitted_blocks_def] >>
  `Src u.vs_memory` by metis_tac[] >>
  qpat_x_assum `!u. _ ==> ?v. _` (qspec_then `u` mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexists_tac `v` >> simp[] >>
  conj_tac >- (irule mem_cont_sim_trans >> metis_tac[]) >>
  conj_tac >- gvs[abi_decode_footprint_frame_def, venom_state_component_equality] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sd x` by
      (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  gvs[venom_state_component_equality]
QED

(* The memory part of the indexed completed-prefix invariant.  d and h are
   the absolute destination/source prefix-sum endpoints at the call site. *)
Theorem normalize_fields_prefix_frame:
  i < N /\
  (!j k. j <= k /\ k <= N ==> d j <= d k /\ h j <= h k) /\
  abi_footprint_disjoint (h 0) (h N - h 0) [(d 0,d N - d 0)] /\
  (!j m m'. j < N /\
    mem_bytes_at (h j) (h (SUC j) - h j) m' =
      mem_bytes_at (h j) (h (SUC j) - h j) m /\ Src j m ==> Src j m') /\
  (!j m m'. j < N /\
    mem_bytes_at (d j) (d (SUC j) - d j) m' =
      mem_bytes_at (d j) (d (SUC j) - d j) m /\ Dst j m ==> Dst j m') /\
  (!j. j < N ==> Src j u.vs_memory) /\
  (!j. j < i ==> Dst j u.vs_memory) /\ Dst i v.vs_memory /\
  abi_decode_footprint_frame [(d 0,d i - d 0)] s u /\
  abi_decode_footprint_frame [(d i,d (SUC i) - d i)] u v ==>
  (!j. j < N ==> Src j v.vs_memory) /\
  (!j. j < SUC i ==> Dst j v.vs_memory) /\
  abi_decode_footprint_frame [(d 0,d (SUC i) - d 0)] s v /\
  mem_bytes_at (h 0) (h N - h 0) v.vs_memory =
    mem_bytes_at (h 0) (h N - h 0) u.vs_memory
Proof
  strip_tac >>
  `!j k. j <= k /\ k <= N ==> d j <= d k` by metis_tac[] >>
  `!j k. j <= k /\ k <= N ==> h j <= h k` by metis_tac[] >>
  `!j. j < N ==> abi_footprint_disjoint (h j) (h (SUC j) - h j)
      [(d i,d (SUC i) - d i)]` by
    (simp[abi_footprint_disjoint_def] >> rpt strip_tac >>
     `h 0 <= h j /\ h j <= h (SUC j) /\ h (SUC j) <= h N /\ d 0 <= d i /\
      d (SUC i) <= d N /\ d i <= d (SUC i)` by
       (rpt conj_tac >> first_assum irule >> decide_tac) >>
     `h 0 <= h N /\ d 0 <= d N` by
       (conj_tac >> first_assum irule >> decide_tac) >>
     qpat_x_assum `abi_footprint_disjoint _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_footprint_disjoint_def] >> decide_tac) >>
  conj_tac >- (rpt strip_tac >>
    `mem_bytes_at (h j) (h (SUC j) - h j) v.vs_memory =
      mem_bytes_at (h j) (h (SUC j) - h j) u.vs_memory` by
        (irule abi_decode_footprint_frame_slice >> metis_tac[]) >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> Cases_on `j = i` >- gvs[] >>
    `j < i` by decide_tac >>
    `abi_footprint_disjoint (d j) (d (SUC j) - d j)
      [(d i,d (SUC i) - d i)]` by
      (simp[abi_footprint_disjoint_def] >>
       `d j <= d (SUC j) /\ d (SUC j) <= d i` by
         (conj_tac >> first_assum irule >> decide_tac) >> decide_tac) >>
    `mem_bytes_at (d j) (d (SUC j) - d j) v.vs_memory =
      mem_bytes_at (d j) (d (SUC j) - d j) u.vs_memory` by
        (irule abi_decode_footprint_frame_slice >> metis_tac[]) >>
    `j < N` by decide_tac >> `Dst j u.vs_memory` by metis_tac[] >>
    qpat_x_assum `!j m m'. _ ==> Dst j m'` irule >>
    simp[] >> qexists_tac `u.vs_memory` >> simp[]) >>
  `d 0 <= d i /\ d i <= d (SUC i) /\ d (SUC i) <= d N /\
   h 0 <= h N` by (rpt conj_tac >> first_assum irule >> decide_tac) >>
  conj_tac
  >- (irule abi_decode_footprint_frame_trans >> qexists_tac `u` >>
      conj_tac >> irule abi_decode_footprint_frame_weaken >>
      goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
      simp[] >> decide_tac) >>
  irule abi_decode_footprint_frame_slice >>
  qexists_tac `[(d i,d (SUC i) - d i)]` >> simp[] >>
  qpat_x_assum `abi_footprint_disjoint _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_footprint_disjoint_def] >> decide_tac
QED

(* Prefix arithmetic shared by the concrete tuple and nominal-layout folds. *)
Theorem normalize_prefix_step:
  i < LENGTH xs ==>
  SUM (MAP f (TAKE (SUC i) xs)) =
    SUM (MAP f (TAKE i xs)) + f (EL i xs)
Proof
  strip_tac >> simp[rich_listTheory.TAKE_SUC_BY_TAKE,
    rich_listTheory.SNOC_APPEND, listTheory.MAP_APPEND, listTheory.SUM_APPEND]
QED

Theorem normalize_prefix_mono:
  !xs j k. j <= k ==> SUM (MAP f (TAKE j xs)) <= SUM (MAP f (TAKE k xs))
Proof
  Induct_on `xs` >- simp[] >> rpt gen_tac >>
  Cases_on `j` >- simp[] >> Cases_on `k` >> simp[]
QED

Theorem normalize_fields_suffix_code:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
  compile_typed_copy_fields ce dst src dts sts
    (doff + type_memory_bytes ce dt) (soff + type_memory_bytes ce st) se = ((),sb) /\
  fn_has_code sa sb fn ==>
  fn_has_code sa se fn /\ fn_has_code se sb fn
Proof
  strip_tac >>
  `cs_extends sd se` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `cs_extends se sb` by
    metis_tac[cj 2 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  imp_res_tac normalize_byte_offset_straight >>
  `cs_extends sa se` by metis_tac[cs_extends_trans] >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED

Theorem normalize_tuple_fields_run[local]:
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
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    Src i u.vs_memory ==>
    ?v. mem_cont_sim ctx fn u v /\ Dst i v.vs_memory /\
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
  ?t. mem_cont_sim ctx fn s t /\
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
      (!j. j < N ==> Src j u.vs_memory) /\
      (emitted_blocks sc sb <> [] ==>
        ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
          phi_prefix_length bb.bb_instructions = 0)` >>
  `Inv DT ST d0 s0 sa s` by
    (simp[Abbr `Inv`] >> qexists_tac `0` >>
     simp[abi_decode_footprint_frame_def, venom_state_component_equality] >>
     asm_rewrite_tac[]) >>
  qsuff_tac `?t. mem_cont_sim ctx fn s t /\
    Inv [] [] (d0 + SUM (MAP (type_memory_bytes ce) DT))
      (s0 + SUM (MAP (type_memory_bytes ce) ST)) sb t`
  >- (strip_tac >> qexists_tac `t` >>
      qpat_x_assum `Inv DT ST _ _ _ _` kall_tac >>
      qpat_x_assum `!i sd se dp sp u. _` kall_tac >>
      qpat_x_assum `!i. d i = _` kall_tac >>
      qpat_x_assum `!i. h i = _` kall_tac >>
      qpat_x_assum `Inv [] [] _ _ sb t` mp_tac >>
      simp[Abbr `Inv`, listTheory.DROP_EQ_NIL] >> strip_tac >>
      `i = N` by decide_tac >>
      qpat_x_assum `i = N` SUBST_ALL_TAC >> asm_rewrite_tac[]) >>
  irule normalize_fields_sequence >>
  conj_tac >- simp[] >> qexistsl_tac [`dst`, `sa`, `src`] >>
  simp[] >> rpt gen_tac >> strip_tac >> suspend "tuple_step"
QED

Resume normalize_tuple_fields_run[tuple_step]:
  qpat_x_assum `Inv DT ST _ _ _ _` kall_tac >>
  qpat_x_assum `Inv (_::_) (_::_) _ _ _ _` mp_tac >>
  simp[Abbr `Inv`, NoAsms] >> strip_tac >>
  drule normalize_fields_cons_states >>
  disch_then (qx_choose_then `dp1` (qx_choose_then `sc1`
    (qx_choose_then `sp1` (qx_choose_then `sd1`
      (qx_choose_then `se1` strip_assume_tac))))) >>
  `dp1 = dp /\ sc1 = sc /\ sp1 = sp /\ sd1 = sd /\ se1 = se` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `dp1 = dp` SUBST_ALL_TAC >>
  qpat_x_assum `sc1 = sc` SUBST_ALL_TAC >>
  qpat_x_assum `sp1 = sp` SUBST_ALL_TAC >>
  qpat_x_assum `sd1 = sd` SUBST_ALL_TAC >>
  qpat_x_assum `se1 = se` SUBST_ALL_TAC >>
  drule_all normalize_fields_suffix_code >> strip_tac >>
  `cs_extends sd se /\ cs_extends se sb` by
    metis_tac[ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  imp_res_tac normalize_byte_offset_straight >>
  `cs_extends sa' se` by metis_tac[cs_extends_trans] >>
  `emitted_blocks sa' se = emitted_blocks sd se` by
    simp[fragExecTheory.emitted_blocks_def] >>
  `(emitted_blocks se sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)` by
    (strip_tac >>
     qpat_x_assum `emitted_blocks sa' sb <> [] ==> _` irule >>
     qpat_assum `cs_extends sa' se` mp_tac >>
     qpat_assum `cs_extends se sb` mp_tac >>
     qpat_x_assum `emitted_blocks se sb <> []` mp_tac >>
     simp_tac (srw_ss()) [cs_extends_def, fragExecTheory.emitted_blocks_def,
       listTheory.LENGTH_APPEND, rich_listTheory.TAKE_LENGTH_APPEND] >>
     rpt strip_tac >> gvs[listTheory.LENGTH_APPEND] >> decide_tac) >>
  `(emitted_blocks sa' se <> [] ==>
    ?entry. lookup_block se.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0)` by
    (strip_tac >> irule normalize_fields_conditional_suffix_entry >>
     goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ se = _`)) >>
     qexists_tac `sa'` >> simp[] >>
     metis_tac[normalize_typed_changed_prefix_zero]) >>
  suspend "tuple_indices"
QED

Resume normalize_tuple_fields_run[tuple_indices]:
  `i < N` by
    (qpat_assum `dt::dts = DROP i DT` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[listTheory.LENGTH_DROP] >> decide_tac) >>
  `dt = EL i DT /\ st = EL i ST` by
    (conj_tac
     >- (qpat_assum `dt::dts = DROP i DT` (mp_tac o Q.AP_TERM `HD`) >>
         simp[listTheory.HD_DROP]) >>
     qpat_assum `st::sts = DROP i ST` (mp_tac o Q.AP_TERM `HD`) >>
     simp[listTheory.HD_DROP]) >>
  `dts = DROP (SUC i) DT /\ sts = DROP (SUC i) ST` by
    (conj_tac
     >- (qpat_assum `dt::dts = DROP i DT` (mp_tac o Q.AP_TERM `DROP 1`) >>
         simp[rich_listTheory.DROP_DROP, arithmeticTheory.ADD1]) >>
     qpat_assum `st::sts = DROP i ST` (mp_tac o Q.AP_TERM `DROP 1`) >>
     simp[rich_listTheory.DROP_DROP, arithmeticTheory.ADD1]) >>
  suspend "tuple_execute"
QED

Resume normalize_tuple_fields_run[tuple_execute]:
  `!j k. j <= k /\ k <= N ==> d j <= d k /\ h j <= h k` by
    (simp[] >> metis_tac[normalize_prefix_mono]) >>
  `d (SUC i) = d i + type_memory_bytes ce dt /\
   h (SUC i) = h i + type_memory_bytes ce st` by
    (conj_tac
     >- (qpat_assum `!i. d i = _` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `dt = EL i DT` (fn th => pure_rewrite_tac[th]) >>
         pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> ntac 2 AP_TERM_TAC >>
         irule normalize_prefix_step >> simp[]) >>
     qpat_assum `!i. h i = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `st = EL i ST` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> ntac 2 AP_TERM_TAC >>
     irule normalize_prefix_step >> simp[]) >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `s' with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
       vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  qsuff_tac `?v. mem_cont_sim ctx fn s' v /\ Dst i v.vs_memory /\
    ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
    v.vs_inst_idx = LENGTH se.cs_current_insts /\
    abi_decode_footprint_frame [(d i,type_memory_bytes ce dt)] s' v /\
    (!x. not_fresh_at sa' x ==> lookup_var x v = lookup_var x s') /\
    sa'.cs_next_var <= se.cs_next_var /\
    (v with <|vs_vars := s'.vs_vars; vs_memory := s'.vs_memory;
      vs_current_bb := s'.vs_current_bb; vs_inst_idx := s'.vs_inst_idx;
      vs_prev_bb := s'.vs_prev_bb|>) = s'`
  >- suspend "tuple_preserve" >>
  suspend "tuple_adapter"
QED

Resume normalize_tuple_fields_run[tuple_adapter]:
  irule normalize_field_child_cont >>
  conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_with_byte_offset _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_with_byte_offset _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_operand _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_operand _ _ = _`)) >>
  qexists_tac `Src i` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  suspend "tuple_child"
QED

Resume normalize_tuple_fields_run[tuple_child]:
  `n2w b + n2w doff = (n2w (d i):256 word) /\
   n2w a + n2w soff = (n2w (h i):256 word)` by
    (pure_rewrite_tac[wordsTheory.word_add_n2w] >> conj_tac
     >- (qpat_assum `!i. d i = _` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `doff = _` (fn th => pure_rewrite_tac[th]) >>
         simp_tac bool_ss [arithmeticTheory.ADD_ASSOC]) >>
     qpat_assum `!i. h i = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `soff = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [arithmeticTheory.ADD_ASSOC]) >>
  rpt strip_tac >>
  `d (SUC i) <= d N /\ h (SUC i) <= h N` by
    (qpat_x_assum `!j k. _` (qspecl_then [`SUC i`,`N`] mp_tac) >>
     impl_tac >- decide_tac >> strip_tac >> asm_rewrite_tac[]) >>
  `d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next` by
    (conj_tac >> decide_tac) >>
  qpat_x_assum `!i sd se dp sp u. _` (qspec_then `i` mp_tac) >>
  qpat_assum `dt = EL i DT` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `st = EL i ST` (fn th => pure_rewrite_tac[GSYM th]) >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `u` mp_tac) >>
  impl_tac >- (rpt conj_tac >> asm_rewrite_tac[] >> simp[]) >>
  strip_tac >> qexists_tac `v` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume normalize_tuple_fields_run[tuple_preserve]:
  strip_tac >> qexists_tac `v` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!i sd se dp sp u. _` kall_tac >>
  `d (SUC i) - d i = type_memory_bytes ce dt` by decide_tac >>
  `abi_decode_footprint_frame [(d i,d (SUC i) - d i)] s' v` by
    (qpat_assum `d (SUC i) - d i = _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `(!j. j < N ==> Src j v.vs_memory) /\
   (!j. j < SUC i ==> Dst j v.vs_memory) /\
   abi_decode_footprint_frame [(d 0,d (SUC i) - d 0)] s v /\
   mem_bytes_at (h 0) (h N - h 0) v.vs_memory =
     mem_bytes_at (h 0) (h N - h 0) s'.vs_memory` by
    (irule normalize_fields_prefix_frame >>
     goal_assum (drule_at (Pat `abi_decode_footprint_frame _ s' v`)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `SUC i` >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "tuple_prefix_offsets"
QED

Resume normalize_tuple_fields_run[tuple_prefix_offsets]:
  `i < LENGTH DT /\ i < LENGTH ST` by decide_tac >>
  conj_tac
  >- (qpat_assum `doff = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `dt = EL i DT` (fn th => pure_rewrite_tac[th]) >>
      simp_tac bool_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
      AP_TERM_TAC >> sym_tac >> irule normalize_prefix_step >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `soff = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `st = EL i ST` (fn th => pure_rewrite_tac[th]) >>
      simp_tac bool_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
      AP_TERM_TAC >> sym_tac >> irule normalize_prefix_step >>
      first_assum ACCEPT_TAC) >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "tuple_runtime"
QED

Resume normalize_tuple_fields_run[tuple_runtime]:
  `!x. not_fresh_at sa x ==> not_fresh_at sa' x` by
    (simp_tac (srw_ss()) [not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> impl_tac >- decide_tac >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s` by
    (rpt strip_tac >> metis_tac[]) >>
  `eval_operand dst v = SOME (n2w b) /\ eval_operand src v = SOME (n2w a)` by
    (qpat_assum `eval_operand dst s' = _` mp_tac >>
     qpat_assum `eval_operand src s' = _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa' x ==> lookup_var x v = _` mp_tac >>
     qpat_assum `!x. dst = Var x \/ src = Var x ==> not_fresh_at sa' x` mp_tac >>
     qpat_assum `v with <|vs_vars := _; vs_memory := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _|> = s'` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `dst` >> Cases_on `src` >>
     gvs[eval_operand_def, venom_state_component_equality]) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sa' x` by metis_tac[] >>
      qpat_x_assum `not_fresh_at sa' x` mp_tac >>
      simp_tac (srw_ss()) [not_fresh_at_def] >> rpt strip_tac >>
      first_x_assum (qspec_then `n` mp_tac) >>
      impl_tac >- decide_tac >> simp[]) >>
  conj_tac >- decide_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `v with <|vs_vars := _; vs_memory := _; vs_current_bb := _;
        vs_inst_idx := _; vs_prev_bb := _|> = s'` mp_tac >>
      qpat_assum `s' with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp_tac (srw_ss()) [venom_state_component_equality]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise normalize_tuple_fields_run

(* Nominal lookup plus stored-size agreement reduces the struct traversal to
   the same-type field traversal; names are justified, never erased by size. *)
Theorem normalize_struct_as_fields:
  !fields doff soff.
    (!name ty sz. MEM (name,ty,sz) fields ==>
      ALOOKUP src_fields name = SOME (ty,sz) /\ sz = type_memory_bytes ce ty) ==>
    compile_struct_typed_copy ce dst src fields src_fields doff soff =
      compile_typed_copy_fields ce dst src (MAP (FST o SND) fields)
        (MAP (FST o SND) fields) doff soff
Proof
  Induct_on `fields`
  >- (simp[Once compile_store_memory_typed_def] >>
      simp[Once compile_store_memory_typed_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `ALOOKUP src_fields h0 = SOME (h1,h2) /\ h2 = type_memory_bytes ce h1` by
    metis_tac[listTheory.MEM] >>
  `!doff soff. compile_struct_typed_copy ce dst src fields src_fields doff soff =
    compile_typed_copy_fields ce dst src (MAP (FST o SND) fields)
      (MAP (FST o SND) fields) doff soff` by
    (rpt gen_tac >> first_x_assum irule >> metis_tac[listTheory.MEM]) >>
  simp_tac (srw_ss()) [listTheory.MAP, combinTheory.o_THM] >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  asm_simp_tac (srw_ss()) [LET_THM]
QED

Theorem normalize_struct_prefix_sizes:
  !fields i.
    (!name ty sz. MEM (name,ty,sz) fields ==> sz = type_memory_bytes ce ty) ==>
    SUM (MAP (SND o SND) (TAKE i fields)) =
      SUM (MAP (type_memory_bytes ce) (TAKE i (MAP (FST o SND) fields)))
Proof
  Induct_on `fields` >- simp[] >> gen_tac >> PairCases_on `h` >>
  Cases_on `i` >- simp[] >>
  simp_tac (srw_ss()) [listTheory.TAKE_def, listTheory.MAP,
    listTheory.SUM, combinTheory.o_THM] >> strip_tac >>
  `h2 = type_memory_bytes ce h1` by metis_tac[listTheory.MEM] >>
  asm_rewrite_tac[] >> AP_TERM_TAC >> first_x_assum irule >>
  metis_tac[listTheory.MEM]
QED

Theorem normalize_nominal_struct_fields_run[local]:
  DT = MAP (FST o SND) fields /\ LENGTH fields = N /\
  (!name ty sz. MEM (name,ty,sz) fields ==>
    ALOOKUP src_fields name = SOME (ty,sz) /\ sz = type_memory_bytes ce ty) /\
  (!i. d i = b + d0 + SUM (MAP (SND o SND) (TAKE i fields))) /\
  (!i. h i = a + s0 + SUM (MAP (SND o SND) (TAKE i fields))) /\
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
    Src i u.vs_memory ==>
    ?v. mem_cont_sim ctx fn u v /\ Dst i v.vs_memory /\
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
  ?t. mem_cont_sim ctx fn s t /\
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
  `!doff soff. compile_struct_typed_copy ce dst src fields src_fields doff soff =
    compile_typed_copy_fields ce dst src DT DT doff soff` by
    (rpt gen_tac >> qpat_assum `DT = _` (fn th => pure_rewrite_tac[th]) >>
     irule normalize_struct_as_fields >> first_assum ACCEPT_TAC) >>
  `!i. SUM (MAP (SND o SND) (TAKE i fields)) =
    SUM (MAP (type_memory_bytes ce) (TAKE i DT))` by
    (gen_tac >> qpat_assum `DT = _` (fn th => pure_rewrite_tac[th]) >>
     irule normalize_struct_prefix_sizes >> metis_tac[]) >>
  `compile_typed_copy_fields ce dst src DT DT d0 s0 sa = ((),sb)` by
    metis_tac[] >>
  `LENGTH DT = N` by simp[] >>
  `(!i. d i = b + d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
   (!i. h i = a + s0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT)))` by
    (qpat_assum `!i. SUM (MAP (SND o SND) _) = _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  irule normalize_tuple_fields_run >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_operand _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_operand _ _ = _`)) >>
  qexists_tac `Src` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem normalize_tuple_fields_memory_run:
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
    ?v. mem_cont_sim ctx fn u v /\ val_in_memory (TD i) (VD i) (d i) v.vs_memory /\
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
  ?t. mem_cont_sim ctx fn s t /\
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
    normalize_tuple_fields_run) >>
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

Theorem normalize_nominal_struct_fields_memory_run:
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
    ?v. mem_cont_sim ctx fn u v /\ val_in_memory (TD i) (VD i) (d i) v.vs_memory /\
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
  ?t. mem_cont_sim ctx fn s t /\
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
    normalize_nominal_struct_fields_run) >>
  simp_tac bool_ss [] >>
  ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
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
