Theory typedNormalizeFields
Ancestors
  typedNormalizeFrame typedBytesArrayMem externalReturnNormalizeMem abiDecoderFrame
  context compileEnv emitHelper venomInst exprLoweringProps memContinuation venomState

(* Offsets are straight-line, even when the child they precede has a CFG. *)
Theorem normalize_byte_offset_straight[local]:
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
Theorem normalize_fields_cons_states[local]:
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
  fn_has_code sa se fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  Src s.vs_memory /\
  (!u. eval_operand dp u = SOME (d + n2w doff) /\
    eval_operand sp u = SOME (p + n2w soff) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\ ~u.vs_halted /\
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
  `Src u.vs_memory` by metis_tac[] >>
  qpat_x_assum `!u. _ ==> ?v. _` drule_all >> strip_tac >>
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
Theorem normalize_fields_prefix_frame[local]:
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
