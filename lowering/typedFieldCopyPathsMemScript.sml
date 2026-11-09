Theory typedFieldCopyPathsMem
Ancestors
  typedNormalizeFrame typedNormalizeFields typedCopyOperationalPaths
  fragGasSeqMem fragGasPathMem fragExec context compileEnv emitHelper
  venomInst venomState rich_list list exprLoweringProps
  externalReturnNormalizeMem valueEncoding valueEncodingProps
  exprSimAggregateChildren valueCopyBytes exprSimProps valueCopy abiDecoderFrame

(* Lift a concrete compiler window, without allocation-history assumptions. *)
Theorem typed_copy_window_path_mem:
  fn_has_code sa sb fn /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK q ==>
  gas_path_mem ctx fn s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)))
    (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sa sb fn` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     goal_assum (drule_at Any) >>
     gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND]) >>
  `gas_path_mem ctx fn s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)))
    (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))` by
    (irule run_inst_seq_gas_path_mem >> goal_assum (drule_at Any) >> gvs[]) >>
  gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND]
QED

Theorem normalize_word_window_path_mem:
  is_word_type dst_ty /\ evaluate_type tenv dst_ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
  compile_store_memory_typed ce dst dst_ty src src_ty sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n p + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n q. gas_path_mem ctx fn s n
        (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (!a k. a + k <= w2n d \/ w2n d + 32 <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_word_copy_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all typed_copy_word_mem_ok >> simp[]) >>
  drule_all normalize_word_straight >> strip_tac >>
  drule_all typed_copy_window_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))`, `q`] >> simp[] >>
  conj_tac
  >- (drule_all val_in_memory_word_type >>
      simp[mem_word_at_eq_mload] >> strip_tac >>
      drule_all val_in_memory_word >>
      disch_then (qspecl_then [`w2n d`,
        `(mstore (w2n d) (mload (w2n p) s) s).vs_memory`] mp_tac) >>
      simp[mstore_mem_word_at_same]) >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem normalize_bytestring_window_path_mem:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size len /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n q. gas_path_mem ctx fn s n
        (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (!a k. a + k <= w2n d \/
          w2n d + (32 + 32 * word_size len) <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >> drule_all normalize_bytestring_window_run >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `mem_word_at (w2n p) s.vs_memory = n2w len` by
    gvs[mem_word_at_eq_mload] >>
  drule_all store_bytestring_run_exact >> strip_tac >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[IS_PREFIX_APPEND] >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
  fs[same_blocks_def] >>
  drule_all typed_copy_window_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))`, `q`] >>
  gvs[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem normalize_byte_offset_path_mem:
  compile_with_byte_offset op off sa = (out,sb) /\
  eval_operand op s = SOME a /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. out = Var x ==> not_fresh_at sb x) /\
  ?n t. gas_path_mem ctx fn s n (OK t) /\
      eval_operand out t = SOME (a + n2w off) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all normalize_byte_offset_run >> strip_tac >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >> simp[] >>
  drule_all normalize_byte_offset_straight >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule normalize_byte_offset_mem_ok >> simp[]) >>
  drule_all typed_copy_window_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))`,
    `q with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def]
QED

Theorem normalize_field_offsets_path_mem:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sd fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sa.cs_next_var <= sd.cs_next_var /\
  (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
  ?n u. gas_path_mem ctx fn s n (OK u) /\
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
    metis_tac[fn_has_code_split] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_byte_offset_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `compile_with_byte_offset dst doff sa = _` kall_tac >>
  `eval_operand src t = SOME p` by
    (Cases_on `src` >> gvs[eval_operand_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `!x. src = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all normalize_byte_offset_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx fn t n2 (OK u)` >>
  `eval_operand dp u = SOME (d + n2w doff)` by
    (Cases_on `dp` >> gvs[eval_operand_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  conj_tac >- decide_tac >>
  conj_tac >- (rpt strip_tac >> gvs[not_fresh_at_def] >>
    metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `gas_path_mem ctx fn s (n + n2) (OK u)` by
    (irule gas_path_mem_then >> metis_tac[]) >>
  qexistsl_tac [`n + n2`, `u`] >> simp[] >>
  gvs[venom_state_component_equality]
QED

(* The invariant carries source ownership and the completed destination prefix;
   the step callback returns these at the very endpoint reached by its path. *)
Theorem normalize_fields_sequence_path_mem:
  (!dt st dts sts doff soff sa dp sc sp sd se s.
    Inv (dt::dts) (st::sts) doff soff sa s /\
    compile_with_byte_offset dst doff sa = (dp,sc) /\
    compile_with_byte_offset src soff sc = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
    ?n t. gas_path_mem ctx fn s n (OK t) /\ ~t.vs_halted /\
        Inv dts sts (doff + type_memory_bytes ce dt)
          (soff + type_memory_bytes ce st) se t) ==>
  !dts sts doff soff sa sb s.
    LENGTH dts = LENGTH sts /\ Inv dts sts doff soff sa s /\ ~s.vs_halted /\
    compile_typed_copy_fields ce dst src dts sts doff soff sa = ((),sb) ==>
    ?n t. gas_path_mem ctx fn s n (OK t) /\ ~t.vs_halted /\
        Inv [] [] (doff + SUM (MAP (type_memory_bytes ce) dts))
          (soff + SUM (MAP (type_memory_bytes ce) sts)) sb t
Proof
  disch_then (mk_asm "field_step") >> Induct_on `dts`
  >- (rpt gen_tac >> simp[Once compile_store_memory_typed_def,
        comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`0`, `s`] >> simp[cj 1 gas_path_mem_rules]) >>
  pop_assum (mk_asm "fields_ih") >>
  rpt gen_tac >> Cases_on `sts` >- simp[] >>
  strip_tac >> drule normalize_fields_cons_states >> strip_tac >>
  asm "field_step" drule_all >> strip_tac >>
  fs[LENGTH] >>
  asm_x "fields_ih" drule_all >> strip_tac >>
  rename1 `Inv [] [] _ _ sb u` >>
  `?ngas. gas_path_mem ctx fn s ngas (OK u)` by
    metis_tac[gas_path_mem_then] >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `Inv [] [] _ _ sb u` mp_tac >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem normalize_struct_sequence_path_mem:
  (!name dt dsz rest doff soff sa dp sc sp sd se s st ssz.
    Inv ((name,dt,dsz)::rest) doff soff sa s /\
    ALOOKUP src_fields name = SOME (st,ssz) /\
    compile_with_byte_offset dst doff sa = (dp,sc) /\
    compile_with_byte_offset src soff sc = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
    ?n t. gas_path_mem ctx fn s n (OK t) /\ ~t.vs_halted /\
        Inv rest (doff + dsz) (soff + ssz) se t) /\
  (!name dt dsz. MEM (name,dt,dsz) fields ==>
    ALOOKUP src_fields name = SOME (dt,dsz)) ==>
  !doff soff sa sb s.
    Inv fields doff soff sa s /\ ~s.vs_halted /\
    compile_struct_typed_copy ce dst src fields src_fields doff soff sa = ((),sb) ==>
    ?n t. gas_path_mem ctx fn s n (OK t) /\ ~t.vs_halted /\
        Inv [] (doff + SUM (MAP (SND o SND) fields))
          (soff + SUM (MAP (SND o SND) fields)) sb t
Proof
  Induct_on `fields`
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once compile_store_memory_typed_def, comp_return_def] >>
      strip_tac >> gvs[] >> qexistsl_tac [`0`, `s`] >>
      simp[cj 1 gas_path_mem_rules]) >>
  pop_assum (mk_asm "struct_ih") >>
  gen_tac >> PairCases_on `h` >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "struct_step") assume_tac) >>
  rpt gen_tac >> strip_tac >>
  rename1 `Inv ((name,dt,dsz)::fields) doff soff sa s` >>
  `ALOOKUP src_fields name = SOME (dt,dsz)` by metis_tac[MEM] >>
  drule_all normalize_struct_cons_states >> strip_tac >>
  asm "struct_step" drule_all >> strip_tac >>
  asm_x "struct_ih" mp_tac >>
  (impl_tac >- (conj_tac >- (asm "struct_step" ACCEPT_TAC) >>
     metis_tac[MEM])) >>
  disch_then drule_all >> strip_tac >>
  rename1 `Inv [] _ _ sb u` >>
  `?ngas. gas_path_mem ctx fn s ngas (OK u)` by
    metis_tac[gas_path_mem_then] >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `Inv [] _ _ sb u` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [MAP, SUM, combinTheory.o_THM,
     AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem normalize_field_child_path_mem:
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
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ Src s.vs_memory /\
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
    ?n v. gas_path_mem ctx fn u n (OK v) /\ D v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame fp u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) ==>
  ?n v. gas_path_mem ctx fn s n (OK v) /\ D v.vs_memory /\
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
    metis_tac[fn_has_code_split] >>
  drule_all normalize_field_offsets_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  `emitted_blocks sd se = emitted_blocks sa se` by
    gvs[emitted_blocks_def] >>
  `Src u.vs_memory` by metis_tac[] >>
  qpat_x_assum `!u. _ ==> ?n v. _` (qspec_then `u` mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  rename1 `gas_path_mem ctx fn u n2 (OK v)` >>
  `gas_path_mem ctx fn s (n + n2) (OK v)` by
    (irule gas_path_mem_then >> metis_tac[]) >>
  qexistsl_tac [`n + n2`, `v`] >> simp[] >>
  conj_tac >- gvs[abi_decode_footprint_frame_def, venom_state_component_equality] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sd x` by
      (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  gvs[venom_state_component_equality]
QED
