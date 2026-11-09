Theory typedNormalizeFieldPathMem
Ancestors
  typedNormalizeFields stmtReasonLitFragMemory fragExec fragGasPathMem fragGasSeqMem typedNormalizeEntryBoundary
  externalReturnNormalizeMem abiDecoderFrame exprLoweringProps emitHelper compileEnv
  venomState venomInst context list rich_list arithmetic

Theorem normalize_byte_offset_no_gas[local]:
  compile_with_byte_offset op off sa = (out,sb) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
  simp[emit_op_def, emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]
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
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      eval_operand out t = SOME (a + n2w off) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all normalize_byte_offset_run >> strip_tac >>
  drule_all normalize_byte_offset_straight >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[normalize_byte_offset_mem_ok] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    metis_tac[normalize_byte_offset_no_gas] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
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
  ?u. gas_path_mem ctx fn s 0 (OK u) /\
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
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule_all normalize_byte_offset_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx fn t 0 (OK u)` >>
  `eval_operand dp u = SOME (d + n2w doff)` by
    (Cases_on `dp` >> gvs[eval_operand_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  conj_tac >- decide_tac >>
  conj_tac >- (rpt strip_tac >> gvs[not_fresh_at_def] >>
    metis_tac[LESS_EQ_TRANS]) >>
  qexists_tac `u` >> simp[] >>
  conj_tac >- metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  gvs[venom_state_component_equality]
QED

(* A traversal composes the child's actual finite witness, not a separately
   supplied semantic continuation endpoint. *)
Theorem normalize_fields_sequence_path_mem:
  (!dt st doff soff sc u. Inv dt st doff soff sc u ==> ~u.vs_halted) /\
  (!dt st dts sts doff soff sa dp sc sp sd se s.
    Inv (dt::dts) (st::sts) doff soff sa s /\
    compile_with_byte_offset dst doff sa = (dp,sc) /\
    compile_with_byte_offset src soff sc = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
    ?t g. gas_path_mem ctx fn s g (OK t) /\
        Inv dts sts (doff + type_memory_bytes ce dt)
          (soff + type_memory_bytes ce st) se t) ==>
  !dts sts doff soff sa sb s.
    LENGTH dts = LENGTH sts /\ Inv dts sts doff soff sa s /\
    compile_typed_copy_fields ce dst src dts sts doff soff sa = ((),sb) ==>
    ?t g. gas_path_mem ctx fn s g (OK t) /\
        Inv [] [] (doff + SUM (MAP (type_memory_bytes ce) dts))
          (soff + SUM (MAP (type_memory_bytes ce) sts)) sb t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "live") (mk_asm "field_step")) >>
  Induct_on `dts`
  >- (rpt gen_tac >> simp[Once compile_store_memory_typed_def,
        comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`s`, `0`] >> simp[] >>
      irule (cj 1 gas_path_mem_rules) >> asm "live" drule >> simp[]) >>
  pop_assum (mk_asm "fields_ih") >>
  rpt gen_tac >> Cases_on `sts` >- simp[] >>
  strip_tac >> drule normalize_fields_cons_states >> strip_tac >>
  asm "field_step" drule_all >> strip_tac >>
  fs[listTheory.LENGTH] >>
  asm_x "fields_ih" drule_all >> strip_tac >>
  rename1 `Inv [] [] _ _ sb u` >> qexists_tac `u` >>
  irule_at Any gas_path_mem_then >>
  goal_assum (drule_at (Pat `gas_path_mem _ _ s _ _`)) >>
  goal_assum (drule_at (Pat `gas_path_mem _ _ _ _ (OK u)`)) >>
  qpat_x_assum `Inv [] [] _ _ sb u` mp_tac >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Theorem normalize_field_child_path_mem:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa se fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ Src s.vs_memory /\
  (!u. eval_operand dp u = SOME (d + n2w doff) /\
    eval_operand sp u = SOME (p + n2w soff) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    phi_prefix_length sd.cs_current_insts = 0 /\ fn_has_code sd se fn /\
    (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    u.vs_alloca_next = s.vs_alloca_next /\ Src u.vs_memory ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\ D v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame fp u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) ==>
  ?v g. gas_path_mem ctx fn s g (OK v) /\ D v.vs_memory /\
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
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  imp_res_tac normalize_byte_offset_straight >>
  `cs_extends sa sd` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sd fn /\ fn_has_code sd se fn` by
    metis_tac[fn_has_code_split] >>
  `phi_prefix_length sd.cs_current_insts = 0` by
    metis_tac[typedNormalizeContinuationTheory.normalize_offset_prefix_zero] >>
  drule_all normalize_field_offsets_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  qpat_x_assum `!u. _ ==> ?v g. _` (qspec_then `u` mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexists_tac `v` >> irule_at Any gas_path_mem_then >>
  goal_assum (drule_at (Pat `gas_path_mem _ _ s _ _`)) >>
  goal_assum (drule_at (Pat `gas_path_mem _ _ u _ _`)) >>
  simp[] >>
  conj_tac >- gvs[abi_decode_footprint_frame_def, venom_state_component_equality] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sd x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  gvs[venom_state_component_equality]
QED

(* A residual field list determines both its index and the next offsets. *)
Theorem normalize_field_index_step[local]:
  LENGTH xs = N /\ i <= N /\ dt::dts = DROP i xs /\
  off = (offset0:num) + SUM (MAP f (TAKE i xs)) ==>
  i < N /\ dt = EL i xs /\ dts = DROP (SUC i) xs /\
  off + f dt = offset0 + SUM (MAP f (TAKE (SUC i) xs))
Proof
  strip_tac >>
  `i < LENGTH xs` by
    (qpat_assum `dt::dts = DROP i xs` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `dt = EL i xs /\ dts = DROP (SUC i) xs` by
    metis_tac[DROP_CONS_EL, listTheory.CONS_11] >>
  drule normalize_prefix_step >>
  disch_then (qspec_then `f` assume_tac) >>
  asm_rewrite_tac[ADD_ASSOC] >> decide_tac
QED

Theorem normalize_field_prefix_geometry[local]:
  LENGTH xs = N /\ i <= N /\ dt::dts = DROP i xs /\
  (!j. addr j = start + offset0 + SUM (MAP f (TAKE j xs))) ==>
  i < N /\ dt = EL i xs /\
  addr (SUC i) = addr i + f dt /\
  (!j k. j <= k /\ k <= N ==> addr j <= addr k)
Proof
  strip_tac >>
  `i < LENGTH xs` by
    (qpat_assum `dt::dts = DROP i xs` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `dt = EL i xs` by metis_tac[DROP_CONS_EL, listTheory.CONS_11] >>
  drule normalize_prefix_step >> disch_then (qspec_then `f` assume_tac) >>
  `i < N` by decide_tac >> simp[] >>
  rpt strip_tac >> irule normalize_prefix_mono >> simp[]
QED

(* Code containment and the terminal PHI certificate for one real child. *)
Theorem normalize_field_suffix_boundary[local]:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
  compile_typed_copy_fields ce dst src dts sts
    (doff + type_memory_bytes ce dt) (soff + type_memory_bytes ce st) se = ((),sb) /\
  phi_prefix_length sa.cs_current_insts = 0 /\ fn_has_code sa sb fn /\
  (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  fn_has_code sa se fn /\ fn_has_code se sb fn /\
  phi_prefix_length se.cs_current_insts = 0 /\
  (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule_all normalize_fields_suffix_code >> strip_tac >>
  `phi_prefix_length se.cs_current_insts = 0` by
    metis_tac[typedNormalizeContinuationTheory.normalize_typed_prefix_zero,
      typedNormalizeContinuationTheory.normalize_offset_prefix_zero] >>
  simp[] >> irule typedNormalizeContinuationTheory.normalize_fields_suffix_entry >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[]
QED
Theorem normalize_fields_tail_equation[local]:
  compile_typed_copy_fields ce dst src (dt::dts) (st::sts) doff soff sa = ((),sb) /\
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
  compile_typed_copy_fields ce dst src dts sts
    (doff + type_memory_bytes ce dt) (soff + type_memory_bytes ce st) se = ((),sb)
Proof
  strip_tac >> drule normalize_fields_cons_states >>
  strip_tac >> gvs[]
QED

(* Indexed bookkeeping is independent of field memory semantics. *)
Theorem normalize_fields_indexed_sequence_path_mem[local]:
  LENGTH DT = N /\ LENGTH ST = N /\ P 0 sa s /\
  (!i sc u. P i sc u ==> ~u.vs_halted) /\
  (!i dt dts st sts doff soff sc dp sc1 sp sd se u.
    i <= N /\ dt::dts = DROP i DT /\ st::sts = DROP i ST /\
    doff = d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT)) /\
    soff = s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST)) /\
    P i sc u /\
    compile_typed_copy_fields ce dst src (dt::dts) (st::sts) doff soff sc = ((),sb) /\
    compile_with_byte_offset dst doff sc = (dp,sc1) /\
    compile_with_byte_offset src soff sc1 = (sp,sd) /\
    compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\ P (SUC i) se v) /\
  compile_typed_copy_fields ce dst src DT ST d0 s0 sa = ((),sb) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ P N sb t
Proof
  strip_tac >>
  qabbrev_tac `Inv = \dt st doff soff sc u.
    ?i. i <= N /\ dt = DROP i DT /\ st = DROP i ST /\
      doff = d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT)) /\
      soff = s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST)) /\ P i sc u /\
      compile_typed_copy_fields ce dst src dt st doff soff sc = ((),sb)` >>
  qsuff_tac `?t g. gas_path_mem ctx fn s g (OK t) /\
    Inv [] [] (d0 + SUM (MAP (type_memory_bytes ce) DT))
      (s0 + SUM (MAP (type_memory_bytes ce) ST)) sb t`
  >- (strip_tac >> qexistsl_tac [`t`,`g`] >> simp[] >>
      qpat_x_assum `Inv [] [] _ _ _ _` mp_tac >>
      simp[Abbr `Inv`, DROP_EQ_NIL] >> strip_tac >>
      `i = N` by decide_tac >> gvs[]) >>
  irule normalize_fields_sequence_path_mem >>
  conj_tac >- (simp[Abbr `Inv`] >> metis_tac[]) >>
  conj_tac >- simp[] >> qexistsl_tac [`dst`,`sa`,`src`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `Inv (_::_) (_::_) _ _ _ _` mp_tac >>
      simp[Abbr `Inv`, NoAsms] >> strip_tac >>
      drule_all normalize_field_index_step >> strip_tac >>
      qpat_assum `LENGTH DT = N` (mp_then Any mp_tac normalize_field_index_step) >>
      disch_then drule_all >> strip_tac >>
      drule_all normalize_fields_tail_equation >> strip_tac >>
      qpat_assum `!i dt dts st sts doff soff sc dp sc1 sp sd se u. _`
        drule_all >> strip_tac >>
      qexistsl_tac [`v`,`g`] >> simp[] >> qexists_tac `SUC i` >>
      simp[] >> decide_tac) >>
  simp[Abbr `Inv`] >> qexists_tac `0` >> simp[]
QED

Theorem normalize_field_runtime_step[local]:
  sa.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= se.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sc x) /\
  eval_operand dst u = SOME dw /\ eval_operand src u = SOME sw /\
  (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
    vs_prev_bb := s.vs_prev_bb|>) = s ==>
  sa.cs_next_var <= se.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at se x) /\
  eval_operand dst v = SOME dw /\ eval_operand src v = SOME sw /\
  (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
    vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `(!x. dst = Var x \/ src = Var x ==> not_fresh_at se x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand dst v = SOME dw /\ eval_operand src v = SOME sw` by
    (Cases_on `dst` >> Cases_on `src` >>
     gvs[eval_operand_def, venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s` by metis_tac[] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  gvs[venom_state_component_equality]
QED

(* Align the native-word offset adapter with a bounded field callback. *)
Theorem normalize_field_bounded_child_path_mem[local]:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa se fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ Src s.vs_memory /\
  di = b + doff /\ hi = a + soff /\
  dend <= s.vs_alloca_next /\ hend <= s.vs_alloca_next /\
  (!u. eval_operand dp u = SOME (n2w di) /\
    eval_operand sp u = SOME (n2w hi) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    phi_prefix_length sd.cs_current_insts = 0 /\ fn_has_code sd se fn /\
    (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    dend <= u.vs_alloca_next /\ hend <= u.vs_alloca_next /\ Src u.vs_memory ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\ D v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame fp u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) ==>
  ?v g. gas_path_mem ctx fn s g (OK v) /\ D v.vs_memory /\
    ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
    v.vs_inst_idx = LENGTH se.cs_current_insts /\
    abi_decode_footprint_frame fp s v /\
    (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
    sa.cs_next_var <= se.cs_next_var /\
    (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >> irule normalize_field_child_path_mem >>
  asm_rewrite_tac[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_with_byte_offset _ _ sa = _`)) >>
  goal_assum (drule_at (Pat `compile_with_byte_offset _ _ sc = _`)) >>
  qexists_tac `Src` >> asm_rewrite_tac[] >>
  qexistsl_tac [`n2w b`,`n2w a`] >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  first_x_assum irule >> gvs[wordsTheory.word_add_n2w] >> first_assum ACCEPT_TAC
QED


(* The invariant is private; consumers only see its induction interface. *)
Theorem normalize_tuple_fields_certificate[local]:
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
    phi_prefix_length sd.cs_current_insts = 0 /\ fn_has_code sd se fn /\
    (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    Src i u.vs_memory ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\ Dst i v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_typed_copy_fields ce dst src DT ST d0 s0 sa = ((),sb) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?P. P 0 sa s /\
    (!i sc u. P i sc u ==> ~u.vs_halted) /\
    (!i dt dts st sts doff soff sc dp sc1 sp sd se u.
      i <= N /\ dt::dts = DROP i DT /\ st::sts = DROP i ST /\
      doff = d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT)) /\
      soff = s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST)) /\ P i sc u /\
      compile_typed_copy_fields ce dst src (dt::dts) (st::sts) doff soff sc = ((),sb) /\
      compile_with_byte_offset dst doff sc = (dp,sc1) /\
      compile_with_byte_offset src soff sc1 = (sp,sd) /\
      compile_store_memory_typed ce dp dt sp st sd = ((),se) ==>
      ?v g. gas_path_mem ctx fn u g (OK v) /\ P (SUC i) se v) /\
    (!t. P N sb t ==>
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
        vs_prev_bb := s.vs_prev_bb|>) = s)
Proof
  strip_tac >>
  qexists_tac `\i sc u.
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\ fn_has_code sc sb fn /\
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
    phi_prefix_length sc.cs_current_insts = 0` >>
  BETA_TAC >> conj_tac
  >- (simp[abi_decode_footprint_frame_def, venom_state_component_equality] >>
      asm_rewrite_tac[]) >>
  conj_tac >- (rpt strip_tac >> simp[]) >>
  reverse conj_tac >- (rpt strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >> suspend "step"
QED
Resume normalize_tuple_fields_certificate[step]:
  qpat_assum `LENGTH DT = N` (mp_then Any mp_tac normalize_field_prefix_geometry) >>
  disch_then drule_all >> strip_tac >>
  qpat_assum `LENGTH ST = N` (mp_then Any mp_tac normalize_field_prefix_geometry) >>
  disch_then drule_all >> strip_tac >>
  drule_all normalize_fields_tail_equation >> strip_tac >>
  `fn_has_code sc se fn /\ fn_has_code se sb fn /\
   phi_prefix_length se.cs_current_insts = 0 /\
   (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
     phi_prefix_length bb.bb_instructions = 0)` by
    (irule normalize_field_suffix_boundary >> asm_rewrite_tac[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by gvs[venom_state_component_equality] >>
  `d (SUC i) <= d N /\ h (SUC i) <= h N` by
    (conj_tac >> first_assum irule >> decide_tac) >>
  `d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next` by decide_tac >>
  qpat_assum `!i sd se dp sp u. _` (qspec_then `i` mp_tac) >>
  disch_then (qspecl_then [`sd`,`se`,`dp`,`sp`] mp_tac) >>
  qpat_assum `dt = EL i DT` (fn dth =>
    qpat_assum `st = EL i ST` (fn sth =>
      qpat_assum `compile_store_memory_typed ce dp dt sp st sd = _` (fn cth =>
        qpat_assum `i < N` (fn ith =>
          pure_rewrite_tac [GSYM dth, GSYM sth, cth, ith, REFL_CLAUSE, AND_CLAUSES])))) >> disch_tac >>
  `d i = b + doff /\ h i = a + soff` by simp[] >>
  `Src i u.vs_memory` by simp[] >>
  qpat_assum `!u. eval_operand dp u = _ /\ _ ==> _`
    (mp_then Any mp_tac normalize_field_bounded_child_path_mem) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`u`,`b`,`a`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >> strip_tac >>
  drule_all normalize_field_runtime_step >> strip_tac >>
  `(!j k. j <= k /\ k <= N ==> d j <= d k /\ h j <= h k)` by metis_tac[] >>
  `abi_decode_footprint_frame [(d i,d (SUC i) - d i)] u v` by
    (qpat_assum `d (SUC i) = _` (fn th => rewrite_tac[th]) >>
     simp_tac arith_ss [] >> first_assum ACCEPT_TAC) >>
  drule_all normalize_fields_prefix_frame >> strip_tac >>
  qexistsl_tac [`v`,`g`] >> asm_rewrite_tac[] >> simp[]
QED
Finalise normalize_tuple_fields_certificate

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
    phi_prefix_length sd.cs_current_insts = 0 /\ fn_has_code sd se fn /\
    (?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    Src i u.vs_memory ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\ Dst i v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_typed_copy_fields ce dst src DT ST d0 s0 sa = ((),sb) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\
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
  strip_tac >> mp_tac normalize_tuple_fields_certificate >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >> strip_tac >>
  qsuff_tac `?t g. gas_path_mem ctx fn s g (OK t) /\ P N sb t`
  >- (strip_tac >> qpat_x_assum `!t. P N sb t ==> _` drule >>
      strip_tac >> qexistsl_tac [`t`,`g`] >> simp[]) >>
  irule normalize_fields_indexed_sequence_path_mem >>
  conj_tac >- (metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `sa` >> simp[]
QED
