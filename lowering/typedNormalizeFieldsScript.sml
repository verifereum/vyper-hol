Theory typedNormalizeFields
Ancestors
  typedNormalizeFrame typedBytesArrayMem externalReturnNormalizeMem
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

Theorem normalize_byte_offset_cont:
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
Theorem normalize_fields_sequence:
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

Theorem normalize_struct_cons_states:
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
Theorem normalize_struct_sequence:
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
