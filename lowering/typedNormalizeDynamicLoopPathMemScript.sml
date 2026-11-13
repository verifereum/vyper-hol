Theory typedNormalizeDynamicLoopPathMem
Ancestors
  typedNormalizeDynarray typedNormalizeLoop typedArrayBoundControlMem
  typedCopySarrayPathMem typedCopyControlPathMem typedCopyArrayEntryPathMem fragGasPathMem
  typedArrayLoopControlMem exprSimBopRestWordLoopPath fragGasSeqMem
  fragGasMode fragExecMem instMemFrontier memSafeRun
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  fragExec memContinuation typedNormalizeContinuation
  venomInst venomState venomExecSemantics venomExecProps venomMemProps
  valueEncoding valueEncodingDefs valueEncodingProps valueEncodingTyping
  valueEncodingProofs vyperTyping exprSimDefs exprSimProps loweringPosts
  typedMemoryCopy words arithmetic list rich_list

(* Unlike the fixed-array header, the bound is a live operand. *)
Theorem typed_array_bound_header_path_mem[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      [mk_inst id LT [Var ctr; bound] [cmp];
       mk_inst (id+1) ISZERO [Var cmp] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  eval_operand bound s = SOME (n2w n) /\ i <= n /\ n < dimword(:256) /\
  lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  gas_marked_path T ctx fn s 0
    (OK (jump_to (if i < n then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i n s)))
Proof
  strip_tac >>
  qabbrev_tac `bb = <|bb_label := hdr; bb_instructions :=
    [mk_inst id LT [Var ctr; bound] [cmp];
     mk_inst (id+1) ISZERO [Var cmp] [done];
     mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]|>` >>
  `gas_marked_path T ctx fn s 0
    (OK (typed_sa_header_state cmp done i n s with vs_inst_idx := 2))` by
    (mp_tac (Q.INST
      [`code` |-> `TAKE 2 bb.bb_instructions`,
       `t` |-> `typed_sa_header_state cmp done i n s`, `memory` |-> `T`]
      rest_word_sequence_marked) >>
     simp[Abbr `bb`, typed_sa_header_state_def, run_inst_seq_def,
       run_inst_seq_mem_ok_def, mk_inst_def, is_terminator_def,
       step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, below_frontier_no_ranges] >>
     disch_then irule >> simp[]) >>
  `gas_marked_path T ctx fn
    (typed_sa_header_state cmp done i n s with vs_inst_idx := 2) 0
    (OK (jump_to (if i < n then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i n s with vs_inst_idx := 2)))` by
    (irule rest_word_jump_marked >>
     conj_tac >- simp[typed_sa_header_state_def, update_var_def] >>
     qexistsl_tac [`bb`, `mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []`] >>
     simp[Abbr `bb`, typed_sa_header_state_def, update_var_def, get_instruction_def,
       mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `i < n` >> simp[bool_to_word_def]) >>
  drule_all gas_marked_path_then >> simp[jump_to_def]
QED

(* One header endpoint serves both the semantic and counted interfaces. *)
Theorem typed_dynarray_header_counted:
  s.vs_current_bb = hdr /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      [mk_inst id LT [Var ("%" ++ toString sm.cs_next_var); bound]
         ["%" ++ toString (sm.cs_next_var+1)];
       mk_inst (id+1) ISZERO [Var ("%" ++ toString (sm.cs_next_var+1))]
         ["%" ++ toString (sm.cs_next_var+2)];
       mk_inst (id+2) JNZ [Var ("%" ++ toString (sm.cs_next_var+2));
         Label exit_lbl; Label body_lbl] []]|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ("%" ++ toString sm.cs_next_var)) s = SOME (n2w i) /\
  eval_operand bound s = SOME (n2w n) /\ i <= n /\ n < dimword(:256) /\
  lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 ==>
  ?u. (counted ==> gas_marked_path T ctx fn s 0 (OK u)) /\
    mem_cont_sim ctx fn s u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if i < n then body_lbl else exit_lbl) /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x \/ x = "%" ++ toString sm.cs_next_var ==>
      lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  qpat_x_assum `s.vs_current_bb = hdr` (SUBST_ALL_TAC o SYM) >>
  drule_all typed_array_bound_header_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all typed_array_bound_header_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``n <= n+1 /\ n <= n+2``]
QED

Theorem typed_dynarray_header_successor_counted:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      [mk_inst hid LT [Var ("%" ++ toString sm.cs_next_var); bound]
         ["%" ++ toString (sm.cs_next_var+1)];
       mk_inst (hid+1) ISZERO [Var ("%" ++ toString (sm.cs_next_var+1))]
         ["%" ++ toString (sm.cs_next_var+2)];
       mk_inst (hid+2) JNZ [Var ("%" ++ toString (sm.cs_next_var+2));
         Label exit_lbl; Label sc.cs_current_bb] []]|> /\
  sc.cs_current_insts =
    [mk_inst id MUL [Var ("%" ++ toString sm.cs_next_var); Lit (n2w ss)]
       ["%" ++ toString (sm.cs_next_var+3)];
     mk_inst (id+1) MUL [Var ("%" ++ toString sm.cs_next_var); Lit (n2w ds)]
       ["%" ++ toString (sm.cs_next_var+4)];
     mk_inst (id+2) ADD [src; Var ("%" ++ toString (sm.cs_next_var+3))]
       ["%" ++ toString (sm.cs_next_var+5)];
     mk_inst (id+3) ADD [dst; Var ("%" ++ toString (sm.cs_next_var+4))]
       ["%" ++ toString (sm.cs_next_var+6)]] /\
  sc.cs_next_var = sm.cs_next_var+7 /\ ci_mono sc ec /\
  lookup_block sc.cs_current_bb fn.fn_blocks = SOME body_bb /\
  isPREFIX sc.cs_current_insts body_bb.bb_instructions /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := ec.cs_current_bb; bb_instructions := ec.cs_current_insts ++
      typed_sa_backedge_insts ec.cs_next_id ("%" ++ toString sm.cs_next_var)
        ("%" ++ toString ec.cs_next_var) hdr|> /\
  (!x. src = Var x \/ dst = Var x \/ bound = Var x ==> not_fresh_at sm x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ("%" ++ toString sm.cs_next_var)) s = SOME (n2w i) /\
  eval_operand bound s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ s.vs_current_bb = hdr /\
  i < n /\ n < dimword(:256) /\
  a+ss*n <= s.vs_alloca_next /\ b+ds*n <= s.vs_alloca_next /\
  (a+ss*n <= b \/ b+ds*n <= a) /\
  (!j addr m m'. j < n /\ mem_bytes_at addr ss m = mem_bytes_at addr ss m' ==>
    (Src j addr m <=> Src j addr m')) /\
  (!j addr m m'. j < n /\ mem_bytes_at addr ds m = mem_bytes_at addr ds m' ==>
    (D j addr m <=> D j addr m')) /\
  (!j. j < n ==> Src j (a+ss*j) s.vs_memory) /\
  (!j. j < i ==> D j (b+ds*j) s.vs_memory) /\
  (!j u. j < n /\ ~u.vs_halted /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand (Var ("%" ++ toString (sm.cs_next_var+5))) u = SOME (n2w (a+ss*j)) /\
    eval_operand (Var ("%" ++ toString (sm.cs_next_var+6))) u = SOME (n2w (b+ds*j)) /\
    a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
    Src j (a+ss*j) u.vs_memory ==>
    ?v. (counted ==> gas_marked_path T ctx fn u 0 (OK v)) /\
      mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. (counted ==> gas_marked_path T ctx fn s 0 (OK t)) /\
    mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sm.cs_next_var)) t = SOME (n2w (SUC i)) /\
    eval_operand bound t = SOME (n2w n) /\
    (!j. j < n ==> Src j (a+ss*j) t.vs_memory) /\
    (!j. j < SUC i ==> D j (b+ds*j) t.vs_memory) /\
    mem_bytes_at a (ss*n) t.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+ds*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `i <= n` by decide_tac >>
  `lookup_block (if i < n then sc.cs_current_bb else exit_lbl) fn.fn_blocks =
     SOME body_bb` by simp[] >>
  drule_all typed_dynarray_header_counted >>
  asm_rewrite_tac[] >>
  disch_then (qspecl_then [`ctx`, `counted`] strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME (n2w a) /\
   eval_operand dst u = SOME (n2w b) /\
   eval_operand (Var ("%" ++ toString sm.cs_next_var)) u = SOME (n2w i)` by
    suspend "operands" >>
  suspend "body"
QED
Resume typed_dynarray_header_successor_counted[operands]:
  qpat_x_assum `!x. not_fresh_at sm x \/ _ ==> _` mp_tac >>
  qpat_x_assum `!x. src = Var x \/ _ ==> _` mp_tac >>
  qpat_x_assum `eval_operand src s = _` mp_tac >>
  qpat_x_assum `eval_operand dst s = _` mp_tac >>
  qpat_x_assum `eval_operand (Var _) s = _` mp_tac >>
  qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]
QED
Resume typed_dynarray_header_successor_counted[body]:
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
   (!j. j < n ==> Src j (a+ss*j) u.vs_memory) /\
   (!j. j < i ==> D j (b+ds*j) u.vs_memory)` by asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac
    `lookup_block hdr fn.fn_blocks = SOME header_bb` >>
  `phi_prefix_length header_bb.bb_instructions = 0` by
    simp[Abbr `header_bb`, phi_prefix_length_def, mk_inst_def] >>
  Cases_on `counted`
  >- (rule_assum_tac (SIMP_RULE bool_ss [gas_marked_path_def]) >>
      `!j u. j < n /\ ~u.vs_halted /\
        u.vs_current_bb = sc.cs_current_bb /\
        u.vs_inst_idx = LENGTH sc.cs_current_insts /\
        eval_operand (Var ("%" ++ toString (sm.cs_next_var+5))) u = SOME (n2w (a+ss*j)) /\
        eval_operand (Var ("%" ++ toString (sm.cs_next_var+6))) u = SOME (n2w (b+ds*j)) /\
        a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
        Src j (a+ss*j) u.vs_memory ==>
        ?v. gas_path_mem ctx fn u 0 (OK v) /\ ~v.vs_halted /\
          v.vs_current_bb = ec.cs_current_bb /\
          v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
          (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
            mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
          (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
            vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
            vs_prev_bb := u.vs_prev_bb|>) = u /\
          (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)` by
        (map_every qx_gen_tac [`j`, `st`] >> strip_tac >>
         qpat_assum `!j u. _ ==> ?v. _`
           (qspecl_then [`j`, `st`] mp_tac) >>
         impl_tac >- asm_rewrite_tac[] >>
         strip_tac >> qexists_tac `v` >> asm_rewrite_tac[]) >>
      drule_all typed_sarray_body_successor_path_mem >> strip_tac >>
      `mem_cont_sim ctx fn u t` by
        (drule gas_path_mem_exec >>
         simp[mem_cont_sim_def, fragExecTheory.exit_result_def]) >>
      suspend "finish") >>
  rule_assum_tac (SIMP_RULE bool_ss []) >>
  drule_all typed_sarray_body_successor >> strip_tac >>
  suspend "finish"
QED
Resume typed_dynarray_header_successor_counted[finish]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `!j u. _ ==> ?v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  `(t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
     vs_prev_bb := s.vs_prev_bb|>) = s` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
       vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
     qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = s`
       mp_tac >> rpt (pop_assum kall_tac) >>
     simp[venom_state_component_equality] >> rpt strip_tac >> gvs[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `lookup_var x t = lookup_var x u` by metis_tac[] >>
     `lookup_var x u = lookup_var x s` by metis_tac[] >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
       vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand bound t = SOME (n2w n)` by
    (qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x t = _` mp_tac >>
     qpat_x_assum `!x. src = Var x \/ dst = Var x \/ bound = Var x ==> _` mp_tac >>
     qpat_x_assum `eval_operand bound s = _` mp_tac >>
     qpat_x_assum `t.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `bound` >> fs[eval_operand_def] >> metis_tac[]) >>
  qexists_tac `t` >>
  conj_tac >- (simp[gas_marked_path_def] >>
    drule_all gas_path_mem_then >> simp[]) >>
  conj_tac >- (irule mem_cont_sim_trans >> qexists_tac `u` >> simp[]) >>
  asm_rewrite_tac[] >> metis_tac[])
QED
Finalise typed_dynarray_header_successor_counted

Theorem typed_dynarray_header_iteration_counted:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      [mk_inst hid LT [Var ("%" ++ toString sm.cs_next_var); bound]
         ["%" ++ toString (sm.cs_next_var+1)];
       mk_inst (hid+1) ISZERO [Var ("%" ++ toString (sm.cs_next_var+1))]
         ["%" ++ toString (sm.cs_next_var+2)];
       mk_inst (hid+2) JNZ [Var ("%" ++ toString (sm.cs_next_var+2));
         Label exit_lbl; Label sc.cs_current_bb] []]|> /\
  sc.cs_current_insts =
    [mk_inst id MUL [Var ("%" ++ toString sm.cs_next_var); Lit (n2w ss)]
       ["%" ++ toString (sm.cs_next_var+3)];
     mk_inst (id+1) MUL [Var ("%" ++ toString sm.cs_next_var); Lit (n2w ds)]
       ["%" ++ toString (sm.cs_next_var+4)];
     mk_inst (id+2) ADD [src; Var ("%" ++ toString (sm.cs_next_var+3))]
       ["%" ++ toString (sm.cs_next_var+5)];
     mk_inst (id+3) ADD [dst; Var ("%" ++ toString (sm.cs_next_var+4))]
       ["%" ++ toString (sm.cs_next_var+6)]] /\
  sc.cs_next_var = sm.cs_next_var+7 /\ ci_mono sc ec /\
  lookup_block sc.cs_current_bb fn.fn_blocks = SOME body_bb /\
  isPREFIX sc.cs_current_insts body_bb.bb_instructions /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := ec.cs_current_bb; bb_instructions := ec.cs_current_insts ++
      typed_sa_backedge_insts ec.cs_next_id ("%" ++ toString sm.cs_next_var)
        ("%" ++ toString ec.cs_next_var) hdr|> /\
  (!x. src = Var x \/ dst = Var x \/ bound = Var x ==> not_fresh_at sm x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ("%" ++ toString sm.cs_next_var)) s = SOME (n2w i) /\
  eval_operand bound s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ s.vs_current_bb = hdr /\
  i <= n /\ n < dimword(:256) /\
  a+ss*n <= s.vs_alloca_next /\ b+ds*n <= s.vs_alloca_next /\
  (a+ss*n <= b \/ b+ds*n <= a) /\
  (!j addr m m'. j < n /\ mem_bytes_at addr ss m = mem_bytes_at addr ss m' ==>
    (Src j addr m <=> Src j addr m')) /\
  (!j addr m m'. j < n /\ mem_bytes_at addr ds m = mem_bytes_at addr ds m' ==>
    (D j addr m <=> D j addr m')) /\
  (!j. j < n ==> Src j (a+ss*j) s.vs_memory) /\
  (!j. j < i ==> D j (b+ds*j) s.vs_memory) /\
  (!j u. j < n /\ ~u.vs_halted /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand (Var ("%" ++ toString (sm.cs_next_var+5))) u = SOME (n2w (a+ss*j)) /\
    eval_operand (Var ("%" ++ toString (sm.cs_next_var+6))) u = SOME (n2w (b+ds*j)) /\
    a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
    Src j (a+ss*j) u.vs_memory ==>
    ?v. (counted ==> gas_marked_path T ctx fn u 0 (OK v)) /\
      mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. (counted ==> gas_marked_path T ctx fn s 0 (OK t)) /\
    mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sm.cs_next_var)) t = SOME (n2w n) /\
    eval_operand bound t = SOME (n2w n) /\
    (!j. j < n ==> Src j (a+ss*j) t.vs_memory) /\
    (!j. j < n ==> D j (b+ds*j) t.vs_memory) /\
    mem_bytes_at a (ss*n) t.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+ds*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Inv = \j u.
    (counted ==> gas_marked_path T ctx fn s 0 (OK u)) /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sm.cs_next_var)) u = SOME (n2w j) /\
    eval_operand bound u = SOME (n2w n) /\
    (!k. k < n ==> Src k (a+ss*k) u.vs_memory) /\
    (!k. k < j ==> D k (b+ds*k) u.vs_memory) /\
    mem_bytes_at a (ss*n) u.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+ds*n <= p ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s)` >>
  `Inv i s` by
    (simp_tac bool_ss [Abbr `Inv`] >> asm_rewrite_tac[] >>
     simp[venom_state_component_equality, gas_marked_path_def, gas_path_mem_rules]) >>
  `!j u. Inv j u /\ j < n ==>
     ?v. Inv (SUC j) v /\ mem_cont_sim ctx fn u v` by
    suspend "iteration_step" >>
  `?t. Inv n t /\ mem_cont_sim ctx fn s t` by
    (irule mem_cont_sim_finite_iteration >>
     qexistsl_tac [`n`, `i`, `Inv`] >> simp[] >>
     metis_tac[mem_cont_sim_refl]) >>
  qexists_tac `t` >>
  qpat_x_assum `Inv n t` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  strip_tac >> asm_rewrite_tac[]
QED
Resume typed_dynarray_header_iteration_counted[iteration_step]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Inv j u` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _;
      vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME (n2w a) /\ eval_operand dst u = SOME (n2w b)` by
    (qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x u = _` mp_tac >>
     qpat_x_assum `!x. src = Var x \/ _ ==> _` mp_tac >>
     qpat_x_assum `eval_operand src s = _` mp_tac >>
     qpat_x_assum `eval_operand dst s = _` mp_tac >>
     qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  `a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next` by simp[] >>
  drule_all typed_dynarray_header_successor_counted >> strip_tac >>
  qpat_x_assum `!j u. _ ==> ?v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  suspend "iteration_frame"
QED
Resume typed_dynarray_header_iteration_counted[iteration_frame]:
  qexists_tac `t` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (strip_tac >>
    qpat_x_assum `counted ==> gas_marked_path T ctx fn s 0 (OK u)`
      (mp_tac o SIMP_RULE bool_ss [gas_marked_path_def]) >>
    qpat_x_assum `counted ==> gas_marked_path T ctx fn u 0 (OK t)`
      (mp_tac o SIMP_RULE bool_ss [gas_marked_path_def]) >>
    asm_rewrite_tac[] >> rpt strip_tac >>
    simp[gas_marked_path_def] >> drule_all gas_path_mem_then >> simp[]) >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` mp_tac >>
      qpat_x_assum `!p k. _ ==> mem_bytes_at p k u.vs_memory = _` mp_tac >>
      rpt (pop_assum kall_tac) >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
        vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
      qpat_x_assum `u with <|vs_vars := _; vs_memory := _;
        vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `lookup_var x t = lookup_var x u` by metis_tac[] >>
  `lookup_var x u = lookup_var x s` by metis_tac[] >> simp[]
QED
Finalise typed_dynarray_header_iteration_counted

(* Compiler layout certificates relocated from typedNormalizeDynarrayLoop. *)
Theorem typed_dynarray_child_states:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?sc ec.
    compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+11))) dt
      (Var ("%" ++ toString (sa.cs_next_var+10))) st sc = ((),ec) /\
    sc.cs_current_bb = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    sc.cs_current_insts =
      [mk_inst (sa.cs_next_id+12) MUL
         [Var ("%" ++ toString (sa.cs_next_var+5)); Lit (n2w (type_memory_bytes ce st))]
         ["%" ++ toString (sa.cs_next_var+8)];
       mk_inst (sa.cs_next_id+13) MUL
         [Var ("%" ++ toString (sa.cs_next_var+5)); Lit (n2w (type_memory_bytes ce dt))]
         ["%" ++ toString (sa.cs_next_var+9)];
       mk_inst (sa.cs_next_id+14) ADD
         [Var ("%" ++ toString (sa.cs_next_var+3)); Var ("%" ++ toString (sa.cs_next_var+8))]
         ["%" ++ toString (sa.cs_next_var+10)];
       mk_inst (sa.cs_next_id+15) ADD
         [Var ("%" ++ toString (sa.cs_next_var+4)); Var ("%" ++ toString (sa.cs_next_var+9))]
         ["%" ++ toString (sa.cs_next_var+11)]] /\
    sc.cs_next_var = sa.cs_next_var+12 /\
    sc.cs_next_id = sa.cs_next_id+16 /\
    sc.cs_next_label = sa.cs_next_label+3 /\
    ci_mono sa sc /\ ci_mono sc ec /\ ci_mono ec sb /\
    fn_has_code sc ec fn /\ fn_has_code sa sc fn /\ fn_has_code ec sb fn /\
    lookup_block (fresh_label_output "typed_dyn_cond" sa.cs_next_label) fn.fn_blocks =
      SOME <|bb_label := fresh_label_output "typed_dyn_cond" sa.cs_next_label;
      bb_instructions :=
        [mk_inst (sa.cs_next_id+9) LT
           [Var ("%" ++ toString (sa.cs_next_var+5)); Var ("%" ++ toString sa.cs_next_var)]
           ["%" ++ toString (sa.cs_next_var+6)];
         mk_inst (sa.cs_next_id+10) ISZERO [Var ("%" ++ toString (sa.cs_next_var+6))]
           ["%" ++ toString (sa.cs_next_var+7)];
         mk_inst (sa.cs_next_id+11) JNZ
           [Var ("%" ++ toString (sa.cs_next_var+7));
            Label (fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2));
            Label (fresh_label_output "typed_dyn_body" (sa.cs_next_label+1))] []]|>
      /\
    (?initial. lookup_block sa.cs_current_bb fn.fn_blocks = SOME initial /\
      sc.cs_blocks = HD sc.cs_blocks :: initial :: sa.cs_blocks /\
      initial.bb_label = sa.cs_current_bb /\
      LENGTH initial.bb_instructions = LENGTH sa.cs_current_insts+9 /\
      DROP (LENGTH sa.cs_current_insts+7) initial.bb_instructions =
        [mk_inst (sa.cs_next_id+7) ASSIGN [Lit 0w]
           ["%" ++ toString (sa.cs_next_var+5)];
         mk_inst (sa.cs_next_id+8) JMP
           [Label (fresh_label_output "typed_dyn_cond" sa.cs_next_label)] []]) /\
    sb = ec with <|
      cs_next_var := ec.cs_next_var+1;
      cs_next_id := ec.cs_next_id+3;
      cs_current_bb := fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2);
      cs_current_insts := [];
      cs_blocks := <|bb_label := ec.cs_current_bb;
        bb_instructions := ec.cs_current_insts ++
          typed_sa_backedge_insts ec.cs_next_id
            ("%" ++ toString (sa.cs_next_var+5)) ("%" ++ toString ec.cs_next_var)
            (fresh_label_output "typed_dyn_cond" sa.cs_next_label)|> :: ec.cs_blocks|>
Proof
  strip_tac >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once compile_store_memory_typed_def, LET_THM] >> BETA_TAC >>
  ntac 7 (once_rewrite_tac[dyn_prefix_bind_op, dyn_prefix_bind_void] >>
          simp_tac (srw_ss()) [ADD_ASSOC, APPEND_ASSOC]) >>
  asm_rewrite_tac[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_op_def, emit_void_def, emit_inst_def, emit_def, new_block_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `compile_store_memory_typed ce _ dt _ st sc` >>
  pairarg_tac >> simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (out,ec)` >>
  Cases_on `out` >> gvs[] >>
  qmatch_asmsub_abbrev_tac `fn_has_code sa final fn` >>
  `ci_mono sa sc` by
    (simp_tac (srw_ss()) [Abbr `sc`, ci_mono_def, cs_extends_def] >>
     qmatch_goalsub_abbrev_tac `header::initial::sa.cs_blocks` >>
     qexists_tac `[header;initial]` >> simp[Abbr `initial`, IS_PREFIX_APPEND]) >>
  `ci_mono sc ec` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND]) >>
  `ci_mono ec final` by (suspend "suffix_mono") >>
  `fn_has_code sc ec fn /\ fn_has_code sa sc fn /\ fn_has_code ec final fn` by
    (suspend "code_split") >>
  qexistsl_tac [`sc`, `ec`] >> simp[] >>
  ntac 5 (conj_tac >- simp_tac (srw_ss()) [Abbr `sc`]) >>
  conj_tac
  >- (qpat_x_assum `fn_has_code sa sc fn` mp_tac >>
      simp[Abbr `sc`, fn_has_code_def, emitted_blocks_def,
           DISJ_IMP_THM, FORALL_AND_THM]) >>
  conj_tac >- suspend "initial_lookup" >>
  simp_tac bool_ss [Abbr `final`, typed_sa_backedge_insts_def,
    GSYM APPEND_ASSOC, APPEND]
QED
Resume typed_dynarray_child_states[suffix_mono]:
  simp_tac (srw_ss()) [Abbr `final`, ci_mono_def, cs_extends_def] >>
  qmatch_goalsub_abbrev_tac `backedge::ec.cs_blocks` >>
  qexists_tac `[backedge]` >> simp[Abbr `backedge`, IS_PREFIX_APPEND]
QED
Resume typed_dynarray_child_states[code_split]:
  `cs_extends sa sc /\ cs_extends sc ec /\ cs_extends ec final` by
    fs[ci_mono_def] >>
  `fn_has_code sc ec fn` by
    (irule fn_has_code_mid >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`final`, `sa`] >> simp[]) >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED
Resume typed_dynarray_child_states[initial_lookup]:
  qpat_x_assum `fn_has_code sa sc fn` mp_tac >>
  simp[Abbr `sc`, fn_has_code_def, emitted_blocks_def] >>
  qmatch_goalsub_abbrev_tac
    `<|bb_label := sa.cs_current_bb; bb_instructions := init_code|>` >>
  simp_tac bool_ss [DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  gvs[Abbr `init_code`, DROP_APPEND]
QED
Finalise typed_dynarray_child_states

Theorem typed_dynarray_child_block_code:
  fn_has_code sa sc fn /\ fn_has_code ec sb fn /\
  sc.cs_current_insts =
    [mk_inst i MUL os xs; mk_inst (i+1) MUL ot ys;
     mk_inst (i+2) ADD ou zs; mk_inst (i+3) ADD ov ws] /\
  sb.cs_blocks =
    <|bb_label := ec.cs_current_bb;
      bb_instructions := ec.cs_current_insts ++
        typed_sa_backedge_insts ec.cs_next_id ctr tmp cond|> :: ec.cs_blocks ==>
  ?body backedge.
    lookup_block sc.cs_current_bb fn.fn_blocks = SOME body /\
    isPREFIX sc.cs_current_insts body.bb_instructions /\
    phi_prefix_length body.bb_instructions = 0 /\
    lookup_block ec.cs_current_bb fn.fn_blocks = SOME backedge /\
    backedge.bb_instructions = ec.cs_current_insts ++
      typed_sa_backedge_insts ec.cs_next_id ctr tmp cond /\
    DROP (LENGTH ec.cs_current_insts) backedge.bb_instructions =
      typed_sa_backedge_insts ec.cs_next_id ctr tmp cond
Proof
  strip_tac >>
  qpat_x_assum `fn_has_code sa sc fn` mp_tac >>
  simp_tac bool_ss [fn_has_code_def] >> strip_tac >>
  qpat_x_assum `fn_has_code ec sb fn` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  strip_tac >>
  gvs[DROP_APPEND, IS_PREFIX_APPEND] >>
  gvs[phi_prefix_length_def, mk_inst_def]
QED

Theorem typed_dynarray_compiler_iteration_counted:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\ sm.cs_next_var = sa.cs_next_var+5 /\
  eval_operand (Var ("%" ++ toString (sa.cs_next_var+3))) s = SOME (n2w a) /\
  eval_operand (Var ("%" ++ toString (sa.cs_next_var+4))) s = SOME (n2w b) /\
  eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) s = SOME (n2w i) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
  i <= n /\ n < dimword(:256) /\
  a+type_memory_bytes ce st*n <= s.vs_alloca_next /\
  b+type_memory_bytes ce dt*n <= s.vs_alloca_next /\
  (a+type_memory_bytes ce st*n <= b \/ b+type_memory_bytes ce dt*n <= a) /\
  (!j addr m m'. j < n /\
    mem_bytes_at addr (type_memory_bytes ce st) m =
    mem_bytes_at addr (type_memory_bytes ce st) m' ==> (Src j addr m <=> Src j addr m')) /\
  (!j addr m m'. j < n /\
    mem_bytes_at addr (type_memory_bytes ce dt) m =
    mem_bytes_at addr (type_memory_bytes ce dt) m' ==> (D j addr m <=> D j addr m')) /\
  (!j. j < n ==> Src j (a+type_memory_bytes ce st*j) s.vs_memory) /\
  (!j. j < i ==> D j (b+type_memory_bytes ce dt*j) s.vs_memory) /\
  (!sc ec. compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+11))) dt
      (Var ("%" ++ toString (sa.cs_next_var+10))) st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+10)) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+11)) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) ==>
    !j u. j < n /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+10))) u =
        SOME (n2w (a+type_memory_bytes ce st*j)) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+11))) u =
        SOME (n2w (b+type_memory_bytes ce dt*j)) /\
      a+type_memory_bytes ce st*n <= u.vs_alloca_next /\
      b+type_memory_bytes ce dt*n <= u.vs_alloca_next /\
      Src j (a+type_memory_bytes ce st*j) u.vs_memory ==>
      ?v. (counted ==> gas_marked_path T ctx fn u 0 (OK v)) /\
        mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
        v.vs_current_bb = ec.cs_current_bb /\
        v.vs_inst_idx = LENGTH ec.cs_current_insts /\
        D j (b+type_memory_bytes ce dt*j) v.vs_memory /\
        (!p k. p+k <= b+type_memory_bytes ce dt*j \/
          b+type_memory_bytes ce dt*j+type_memory_bytes ce dt <= p ==>
          mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
        (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
          vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
          vs_prev_bb := u.vs_prev_bb|>) = u /\
        (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. (counted ==> gas_marked_path T ctx fn s 0 (OK t)) /\
    mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    t.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) t = SOME (n2w n) /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) t = SOME (n2w n) /\
    (!j. j < n ==> Src j (a+type_memory_bytes ce st*j) t.vs_memory) /\
    (!j. j < n ==> D j (b+type_memory_bytes ce dt*j) t.vs_memory) /\
    mem_bytes_at a (type_memory_bytes ce st*n) t.vs_memory =
      mem_bytes_at a (type_memory_bytes ce st*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_bytes ce dt*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_dynarray_child_states >> strip_tac >>
  `sb.cs_blocks =
    <|bb_label := ec.cs_current_bb; bb_instructions := ec.cs_current_insts ++
      typed_sa_backedge_insts ec.cs_next_id ("%" ++ toString (sa.cs_next_var+5))
        ("%" ++ toString ec.cs_next_var)
        (fresh_label_output "typed_dyn_cond" sa.cs_next_label)|> :: ec.cs_blocks` by simp[] >>
  `!k:num. (k+12)+1 = k+13 /\ (k+12)+2 = k+14 /\ (k+12)+3 = k+15` by decide_tac >>
  qpat_x_assum `!k:num. _` (fn offsets =>
    drule_all (SIMP_RULE (pure_ss ++ numSimps.REDUCE_ss) [offsets]
      (Q.INST [`i` |-> `sa.cs_next_id+12`] typed_dynarray_child_block_code))) >> strip_tac >>
  rename1 `lookup_block sc.cs_current_bb fn.fn_blocks = SOME body_bb` >>
  `phi_prefix_length sc.cs_current_insts = 0` by
    simp[phi_prefix_length_def, mk_inst_def] >>
  `not_fresh_at sc ("%" ++ toString (sa.cs_next_var+10)) /\
   not_fresh_at sc ("%" ++ toString (sa.cs_next_var+11))` by
    (simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
    phi_prefix_length entry.bb_instructions = 0` by
    (drule_all normalize_typed_backedge_entry >> simp[]) >>
  qpat_x_assum `!sc ec. _` (qspecl_then [`sc`, `ec`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> goal_assum (drule_at Any) >> simp[])) >>
  disch_then assume_tac >>
  `backedge.bb_label = ec.cs_current_bb` by metis_tac[lookup_block_label] >>
  qpat_assum `sm.cs_next_var = _` (fn th => rewrite_tac[GSYM th]) >>
  irule typed_dynarray_header_iteration_counted >>
  asm_rewrite_tac[] >>
  conj_tac >- (qexists_tac `i` >> simp[]) >>
  qexistsl_tac [`body_bb`, `Var ("%" ++ toString (sa.cs_next_var+4))`, `ec`,
    `fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2)`,
    `sa.cs_next_id+9`, `sa.cs_next_id+12`, `sc`,
    `Var ("%" ++ toString (sa.cs_next_var+3))`] >>
  asm_rewrite_tac[] >>
  simp_tac (pure_ss ++ numSimps.REDUCE_ss)
    [DECIDE ``!k:num. (k+5)+1=k+6 /\ (k+5)+2=k+7 /\ (k+5)+3=k+8 /\
      (k+5)+4=k+9 /\ (k+5)+5=k+10 /\ (k+5)+6=k+11 /\ (k+5)+7=k+12 /\
      (k+9)+1=k+10 /\ (k+9)+2=k+11 /\
      (k+12)+1=k+13 /\ (k+12)+2=k+14 /\ (k+12)+3=k+15``] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `Var _ = Var x` mp_tac >>
    simp[not_fresh_at_def] >> disch_then (SUBST1_TAC o SYM) >>
    simp[ASCIInumbersTheory.toString_inj]) >>
  gvs[basic_block_component_equality]
QED

Theorem typed_dynarray_initial_counted:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\ sm.cs_next_var = sa.cs_next_var+5 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts+7 ==>
  ?u. (counted ==> gas_marked_path T ctx fn s 0 (OK u)) /\
    mem_cont_sim ctx fn s u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    eval_operand (Var ("%" ++ toString sm.cs_next_var)) u = SOME 0w /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_dynarray_child_states >> strip_tac >>
  map_every (fn pat => rpt (qpat_x_assum pat kall_tac))
    [`compile_store_memory_typed _ _ _ _ _ _ = _`, `sb = _`,
     `sc.cs_current_insts = _`, `fn_has_code _ _ _`, `ci_mono _ _`,
     `sc.cs_next_var = _`, `sc.cs_next_id = _`, `sc.cs_next_label = _`,
     `sc.cs_blocks = _`] >>
  `initial.bb_instructions = TAKE (LENGTH sa.cs_current_insts+7) initial.bb_instructions ++
    [mk_inst (sa.cs_next_id+7) ASSIGN [Lit 0w] ["%" ++ toString (sa.cs_next_var+5)];
     mk_inst (sa.cs_next_id+8) JMP
       [Label (fresh_label_output "typed_dyn_cond" sa.cs_next_label)] []]` by
    metis_tac[TAKE_DROP] >>
  `gas_path_mem ctx fn s 0
    (OK (jump_to (fresh_label_output "typed_dyn_cond" sa.cs_next_label)
      (update_var ("%" ++ toString sm.cs_next_var) 0w s)))` by
    (irule typed_sa_initial_path_mem >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (goal_assum (drule_at Any) >> simp[phi_prefix_length_def, mk_inst_def]) >>
     qexistsl_tac [`initial`, `sa.cs_next_id+7`,
                  `TAKE (LENGTH sa.cs_current_insts+7) initial.bb_instructions`] >>
     conj_tac
     >- (qpat_assum `sm.cs_next_var = _` (fn th => pure_rewrite_tac[th]) >>
         pure_rewrite_tac[DECIDE ``!k:num. (k+7)+1=k+8``] >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `initial.bb_instructions = _` kall_tac >>
     simp[LENGTH_TAKE]) >>
  `mem_cont_sim ctx fn s
    (jump_to (fresh_label_output "typed_dyn_cond" sa.cs_next_label)
      (update_var ("%" ++ toString sm.cs_next_var) 0w s))` by
    (drule gas_path_mem_exec >> simp[mem_cont_sim_def, fragExecTheory.exit_result_def]) >>
  goal_assum (drule_at Any) >>
  simp[gas_marked_path_def, jump_to_def, update_var_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem typed_dynarray_exit_counted:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\ sm.cs_next_var = sa.cs_next_var+5 /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
  eval_operand (Var ("%" ++ toString sm.cs_next_var)) s = SOME (n2w n) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w n) /\
  n < dimword(:256) /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 ==>
  ?u. (counted ==> gas_marked_path T ctx fn s 0 (OK u)) /\
    mem_cont_sim ctx fn s u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_dynarray_child_states >> strip_tac >>
  `sb.cs_current_bb = fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2) /\
   sb.cs_current_insts = []` by simp[] >>
  map_every (fn pat => rpt (qpat_x_assum pat kall_tac))
    [`compile_store_memory_typed _ _ _ _ _ _ = _`, `sb = _`,
     `sc.cs_current_insts = _`, `fn_has_code _ _ _`, `ci_mono _ _`,
     `sc.cs_next_var = _`, `sc.cs_next_id = _`, `sc.cs_next_label = _`,
     `sc.cs_blocks = _`, `DROP _ _ = _`, `LENGTH initial.bb_instructions = _`,
     `lookup_block sa.cs_current_bb _ = _`, `initial.bb_label = _`] >>
  `lookup_block (if n < n then fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) else
      fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2)) fn.fn_blocks =
      SOME exit_bb` by gvs[] >>
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) s = SOME (n2w n)` by gvs[] >>
  `n <= n` by simp[] >>
  qpat_x_assum `s.vs_current_bb = _` (SUBST_ALL_TAC o SYM) >>
  drule_all (SIMP_RULE (pure_ss ++ numSimps.REDUCE_ss)
    [DECIDE ``!k:num. (k+9)+1=k+10 /\ (k+9)+2=k+11``]
    (Q.INST [`id` |-> `sa.cs_next_id+9`] typed_array_bound_header_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all (SIMP_RULE (pure_ss ++ numSimps.REDUCE_ss)
    [DECIDE ``!k:num. (k+9)+1=k+10 /\ (k+9)+2=k+11``]
    (Q.INST [`id` |-> `sa.cs_next_id+9`] typed_array_bound_header_path_mem)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``k+5 <= k+6 /\ k+5 <= k+7``]
QED

(* The same suffix witness carries the optional accumulated execution path. *)
Theorem typed_dynarray_suffix_counted:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\ sm.cs_next_var = sa.cs_next_var+5 /\
  eval_operand (Var ("%" ++ toString (sa.cs_next_var+3))) s = SOME (n2w a) /\
  eval_operand (Var ("%" ++ toString (sa.cs_next_var+4))) s = SOME (n2w b) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w n) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\ n < dimword(:256) /\
  a+type_memory_bytes ce st*n <= s.vs_alloca_next /\
  b+type_memory_bytes ce dt*n <= s.vs_alloca_next /\
  (a+type_memory_bytes ce st*n <= b \/ b+type_memory_bytes ce dt*n <= a) /\
  (!j addr m m'. j < n /\
    mem_bytes_at addr (type_memory_bytes ce st) m =
    mem_bytes_at addr (type_memory_bytes ce st) m' ==> (Src j addr m <=> Src j addr m')) /\
  (!j addr m m'. j < n /\
    mem_bytes_at addr (type_memory_bytes ce dt) m =
    mem_bytes_at addr (type_memory_bytes ce dt) m' ==> (D j addr m <=> D j addr m')) /\
  (!j. j < n ==> Src j (a+type_memory_bytes ce st*j) s.vs_memory) /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  (!sc ec. compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+11))) dt
      (Var ("%" ++ toString (sa.cs_next_var+10))) st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+10)) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+11)) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) ==>
    !j u. j < n /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+10))) u =
        SOME (n2w (a+type_memory_bytes ce st*j)) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+11))) u =
        SOME (n2w (b+type_memory_bytes ce dt*j)) /\
      a+type_memory_bytes ce st*n <= u.vs_alloca_next /\
      b+type_memory_bytes ce dt*n <= u.vs_alloca_next /\
      Src j (a+type_memory_bytes ce st*j) u.vs_memory ==>
      ?v. (counted ==> gas_marked_path T ctx fn u 0 (OK v)) /\
        mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
        v.vs_current_bb = ec.cs_current_bb /\
        v.vs_inst_idx = LENGTH ec.cs_current_insts /\
        D j (b+type_memory_bytes ce dt*j) v.vs_memory /\
        (!p k. p+k <= b+type_memory_bytes ce dt*j \/
          b+type_memory_bytes ce dt*j+type_memory_bytes ce dt <= p ==>
          mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
        (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
          vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
          vs_prev_bb := u.vs_prev_bb|>) = u /\
        (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. (counted ==> gas_marked_path T ctx fn s 0 (OK t)) /\
    mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!j. j < n ==> Src j (a+type_memory_bytes ce st*j) t.vs_memory) /\
    (!j. j < n ==> D j (b+type_memory_bytes ce dt*j) t.vs_memory) /\
    mem_bytes_at a (type_memory_bytes ce st*n) t.vs_memory =
      mem_bytes_at a (type_memory_bytes ce st*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_bytes ce dt*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!sc ec. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Callback ==> _` >> disch_tac >>
  drule_all (typed_dynarray_initial_counted |> SPEC_ALL) >>
  disch_then (qspecl_then [`ctx`, `counted`] (qx_choose_then `u` strip_assume_tac)) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+3))) u = SOME (n2w a) /\
   eval_operand (Var ("%" ++ toString (sa.cs_next_var+4))) u = SOME (n2w b) /\
   eval_operand (Var ("%" ++ toString sa.cs_next_var)) u = SOME (n2w n)` by
    suspend "operands" >>
  suspend "iterate"
QED
Resume typed_dynarray_suffix_counted[operands]:
  `not_fresh_at sm ("%" ++ toString (sa.cs_next_var+3)) /\
   not_fresh_at sm ("%" ++ toString (sa.cs_next_var+4)) /\
   not_fresh_at sm ("%" ++ toString sa.cs_next_var)` by
    (simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]) >>
  qpat_x_assum `!x. not_fresh_at sm x ==> lookup_var x u = _` mp_tac >>
  qpat_x_assum `eval_operand (Var ("%" ++ toString (sa.cs_next_var+3))) s = _` mp_tac >>
  qpat_x_assum `eval_operand (Var ("%" ++ toString (sa.cs_next_var+4))) s = _` mp_tac >>
  qpat_x_assum `eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = _` mp_tac >>
  fs[eval_operand_def] >> metis_tac[]
QED
Resume typed_dynarray_suffix_counted[iterate]:
  mp_tac (Q.INST [`s` |-> `u`, `i` |-> `0:num`]
    (SPEC_ALL typed_dynarray_compiler_iteration_counted)) >>
  (impl_tac >- (gvs[Abbr `Callback`, MULT_COMM] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  suspend "exit"
QED
Resume typed_dynarray_suffix_counted[exit]:
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`Abbrev (Callback = _)`, `Callback`,
     `!j addr m m'. _ ==> (Src j addr m = _)`,
     `!j addr m m'. _ ==> (D j addr m = _)`,
     `!j. j < n ==> Src j _ s.vs_memory`] >>
  `eval_operand (Var ("%" ++ toString sm.cs_next_var)) v = SOME (n2w n)` by gvs[] >>
  drule_all (typed_dynarray_exit_counted |> SPEC_ALL) >>
  disch_then (qspecl_then [`ctx`, `counted`] (qx_choose_then `t` strip_assume_tac)) >>
  `t.vs_memory = v.vs_memory` by
    (qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v`
       mp_tac >> simp[venom_state_component_equality]) >>
  qexists_tac `t` >>
  conj_tac >- (strip_tac >>
    `gas_marked_path T ctx fn s 0 (OK v)` by
      (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |>
        SIMP_RULE (srw_ss()) []) >> qexists_tac `u` >> simp[]) >>
    irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |>
      SIMP_RULE (srw_ss()) []) >> qexists_tac `v` >> simp[]) >>
  conj_tac >- metis_tac[mem_cont_sim_trans] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  suspend "frame"
QED
Resume typed_dynarray_suffix_counted[frame]:
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v` mp_tac >>
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
    vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED
Finalise typed_dynarray_suffix_counted

Theorem typed_dynarray_compiler_counted:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  w2n p = a /\ w2n d = b /\
  mload a s = n2w n /\ n <= cap /\ cap < dimword(:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  a+32+type_memory_bytes ce st*n <= s.vs_alloca_next /\
  b+32+type_memory_bytes ce dt*n <= s.vs_alloca_next /\
  (a+32+type_memory_bytes ce st*n <= b \/
   b+32+type_memory_bytes ce dt*n <= a) /\
  (!j addr m m'. j < n /\
    mem_bytes_at addr (type_memory_bytes ce st) m =
    mem_bytes_at addr (type_memory_bytes ce st) m' ==> (Src j addr m <=> Src j addr m')) /\
  (!j addr m m'. j < n /\
    mem_bytes_at addr (type_memory_bytes ce dt) m =
    mem_bytes_at addr (type_memory_bytes ce dt) m' ==> (D j addr m <=> D j addr m')) /\
  (!j. j < n ==> Src j (a+32+type_memory_bytes ce st*j) s.vs_memory) /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  (!sc ec. compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+11))) dt
      (Var ("%" ++ toString (sa.cs_next_var+10))) st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+10)) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+11)) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) ==>
    !j u. j < n /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+10))) u =
        SOME (n2w (a+32+type_memory_bytes ce st*j)) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+11))) u =
        SOME (n2w (b+32+type_memory_bytes ce dt*j)) /\
      a+32+type_memory_bytes ce st*n <= u.vs_alloca_next /\
      b+32+type_memory_bytes ce dt*n <= u.vs_alloca_next /\
      Src j (a+32+type_memory_bytes ce st*j) u.vs_memory ==>
      ?v. (counted ==> gas_marked_path T ctx fn u 0 (OK v)) /\
        mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
        v.vs_current_bb = ec.cs_current_bb /\
        v.vs_inst_idx = LENGTH ec.cs_current_insts /\
        D j (b+32+type_memory_bytes ce dt*j) v.vs_memory /\
        (!p k. p+k <= b+32+type_memory_bytes ce dt*j \/
          b+32+type_memory_bytes ce dt*j+type_memory_bytes ce dt <= p ==>
          mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
        (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
          vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
          vs_prev_bb := u.vs_prev_bb|>) = u /\
        (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. (counted ==> gas_marked_path T ctx fn s 0 (OK t)) /\
    mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!j. j < n ==> Src j (a+32+type_memory_bytes ce st*j) t.vs_memory) /\
    (!j. j < n ==> D j (b+32+type_memory_bytes ce dt*j) t.vs_memory) /\
    mem_bytes_at a (32+type_memory_bytes ce st*n) t.vs_memory =
      mem_bytes_at a (32+type_memory_bytes ce st*n) s.vs_memory /\
    mem_bytes_at b 32 t.vs_memory =
      mem_bytes_at b 32 (mstore b (n2w n) s).vs_memory /\
    mload b t = n2w n /\
    (!p k. p+k <= b \/ b+32+type_memory_bytes ce dt*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!sc ec. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Callback ==> _` >> disch_tac >>
  mp_tac (Q.INST [`sz` |-> `32+type_memory_bytes ce st*n`,
    `dz` |-> `32+type_memory_bytes ce dt*n`] typed_dynarray_prefix_path_mem) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `mem_cont_sim ctx fn s q` by
    (drule gas_path_mem_exec >>
     simp[mem_cont_sim_def, fragExecTheory.exit_result_def]) >>
  suspend "suffix"
QED
Resume typed_dynarray_compiler_counted[suffix]:
  `q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `!j. j < n ==> Src j (a+32+type_memory_bytes ce st*j) q.vs_memory` by
    suspend "source" >>
  mp_tac (Q.INST [`s` |-> `q`, `a` |-> `a+32`, `b` |-> `b+32`,
    `sm` |-> `sa with cs_next_var := sa.cs_next_var+5`]
    (SPEC_ALL typed_dynarray_suffix_counted)) >>
  (impl_tac >- (simp[Abbr `Callback`] >>
    qpat_x_assum `~(_ /\ _)` mp_tac >> simp[])) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  suspend "finish"
QED
Resume typed_dynarray_compiler_counted[source]:
  rpt strip_tac >>
  `mem_bytes_at (a+32+type_memory_bytes ce st*j) (type_memory_bytes ce st) q.vs_memory =
   mem_bytes_at (a+32+type_memory_bytes ce st*j) (type_memory_bytes ce st) s.vs_memory` by
    (`type_memory_bytes ce st*(j+1) <= type_memory_bytes ce st*n` by
       simp[LE_MULT_LCANCEL] >>
     `type_memory_bytes ce st*j+type_memory_bytes ce st <= type_memory_bytes ce st*n` by
       (qpat_x_assum `_*(j+1) <= _` mp_tac >>
        pure_rewrite_tac[LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = _` irule >>
     simp[] >> decide_tac) >>
  qpat_x_assum `Abbrev (Callback = _)` kall_tac >>
  qpat_x_assum `Callback` kall_tac >> metis_tac[]
QED
Resume typed_dynarray_compiler_counted[finish]:
  qpat_x_assum `Abbrev (Callback = _)` kall_tac >>
  qpat_x_assum `Callback` kall_tac >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`!j addr m m'. _ ==> (Src j addr m = _)`,
     `!j addr m m'. _ ==> (D j addr m = _)`] >>
  qexists_tac `t` >>
  conj_tac >- (strip_tac >>
    irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |>
      SIMP_RULE (srw_ss()) []) >> qexists_tac `q` >>
    simp[gas_marked_path_def]) >>
  conj_tac >- metis_tac[mem_cont_sim_trans] >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "whole_source" >>
  conj_asm1_tac >- suspend "length" >>
  conj_tac >- suspend "length_word" >>
  conj_tac >- suspend "exterior" >>
  conj_tac >- suspend "state" >>
  suspend "registers"
QED
Resume typed_dynarray_compiler_counted[whole_source]:
  `mem_bytes_at a (32+type_memory_bytes ce st*n) t.vs_memory =
   mem_bytes_at a (32+type_memory_bytes ce st*n) q.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` irule >> decide_tac) >>
  metis_tac[]
QED
Resume typed_dynarray_compiler_counted[length]:
  `mem_bytes_at b 32 t.vs_memory = mem_bytes_at b 32 q.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` irule >> simp[]) >>
  gvs[]
QED
Resume typed_dynarray_compiler_counted[length_word]:
  `mload b t = mload b (mstore b (n2w n) s)` by
    (qpat_x_assum `mem_bytes_at b 32 t.vs_memory = _` mp_tac >>
     pure_rewrite_tac[GSYM mem_word_at_eq_mload, mem_word_at_def, mem_bytes_at_def] >>
     disch_then SUBST1_TAC >> REFL_TAC) >>
  gvs[mload_mstore_same]
QED
Resume typed_dynarray_compiler_counted[exterior]:
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at p' k t.vs_memory = mem_bytes_at p' k q.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` irule >> decide_tac) >>
  `mem_bytes_at p' k q.vs_memory = mem_bytes_at p' k s.vs_memory` by
    (qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = _` irule >> simp[] >> decide_tac) >>
  metis_tac[]
QED
Resume typed_dynarray_compiler_counted[state]:
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = q` mp_tac >>
  qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED
Resume typed_dynarray_compiler_counted[registers]:
  rpt strip_tac >>
  `not_fresh_at (sa with cs_next_var := sa.cs_next_var+5) x` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED
Finalise typed_dynarray_compiler_counted

Theorem normalize_indexed_value_local:
  val_wf tv v /\
  mem_bytes_at a (type_memory_size tv) m =
    mem_bytes_at a (type_memory_size tv) m' ==>
  (val_in_memory tv v a m <=> val_in_memory tv v a m')
Proof
  strip_tac >> eq_tac >> strip_tac >>
  irule val_in_memory_mem_agree >> goal_assum (drule_at Any) >>
  qexists_tac `type_memory_size tv` >> simp[] >> metis_tac[]
QED

Theorem normalize_dynarray_semantic_counted:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  type_memory_bytes ce st = type_memory_size stv /\
  type_memory_bytes ce dt = type_memory_size dtv /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  scap <= cap /\ cap < dimword(:256) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  a + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  b + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next /\
  a + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword(:256) /\
  b + type_memory_size (ArrayTV dtv (Dynamic cap)) < dimword(:256) /\
  (a + type_memory_size (ArrayTV stv (Dynamic scap)) <= b \/
   b + type_memory_size (ArrayTV dtv (Dynamic cap)) <= a) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) a s.vs_memory /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  (!cv sp dp sc ec u sw dw.
    val_wf stv cv /\ val_wf dtv cv /\
    value_has_type stv cv /\ value_has_type dtv cv /\
    compile_store_memory_typed ce dp dt sp st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    (!x. sp = Var x \/ dp = Var x ==> not_fresh_at sc x) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand sp u = SOME sw /\ eval_operand dp u = SOME dw /\
    val_in_memory stv cv (w2n sw) u.vs_memory /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    w2n sw + type_memory_size stv < dimword(:256) /\
    w2n dw + type_memory_size dtv < dimword(:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size dtv <= w2n sw) ==>
    ?v. (counted ==> gas_marked_path T ctx fn u 0 (OK v)) /\
      mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\
      val_in_memory dtv cv (w2n dw) v.vs_memory /\
      (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. (counted ==> gas_marked_path T ctx fn s 0 (OK t)) /\
    mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) b t.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_size (ArrayTV dtv (Dynamic cap)) <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!cv sp dp sc ec u sw dw. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Child ==> _` >> disch_tac >>
  rename1 `val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vals))` >>
  `!i. i < LENGTH vals ==> val_wf stv (EL i vals) /\ val_wf dtv (EL i vals) /\
    value_has_type stv (EL i vals) /\ value_has_type dtv (EL i vals)` by
    (gvs[typed_copy_dynarray_wf,value_has_type_def,all_have_type_EVERY,EVERY_EL]) >>
  `LENGTH vals <= scap /\ LENGTH vals <= cap` by
    gvs[typed_copy_dynarray_wf] >>
  `a+32+type_memory_size stv*LENGTH vals <= a+type_memory_size stv*scap+32 /\
   b+32+type_memory_size dtv*LENGTH vals <= b+type_memory_size dtv*cap+32` by
    (simp[] >> conj_tac >> simp[LE_MULT_LCANCEL]) >>
  `a+32+type_memory_size stv*LENGTH vals <= s.vs_alloca_next /\
   b+32+type_memory_size dtv*LENGTH vals <= s.vs_alloca_next /\
   a+32+type_memory_size stv*LENGTH vals < dimword(:256) /\
   b+32+type_memory_size dtv*LENGTH vals < dimword(:256)` by
    (qpat_x_assum `Abbrev (Child = _)` kall_tac >>
     qpat_x_assum `Child` kall_tac >>
     rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >>
     qpat_x_assum `a+32+_ <= a+_+32` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >>
     qpat_x_assum `b+32+_ <= b+_+32` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >>
     rpt strip_tac >> once_rewrite_tac[MULT_COMM] >> decide_tac) >>
  mp_tac (Q.INST [`Src` |-> `\j p m. val_in_memory stv (EL j vals) p m`,
    `D` |-> `\j p m. val_in_memory dtv (EL j vals) p m`,
    `n` |-> `LENGTH (vals: value list)`, `p` |-> `n2w a`, `d` |-> `n2w b`]
    (SPEC_ALL typed_dynarray_compiler_counted)) >>
  (impl_tac >-
    (`a < dimword(:256) /\ b < dimword(:256)` by decide_tac >> simp[] >>
     (reverse (rpt CONJ_TAC) >- suspend "dyn_child") >>
     qpat_x_assum `Abbrev (Child = _)` kall_tac >> qpat_x_assum `Child` kall_tac >>
     gvs[type_memory_size_def,typed_copy_dynarray_representation,
       mem_word_at_eq_mload,MULT_COMM,ADD_COMM]
     >- (rpt gen_tac >> strip_tac >> irule normalize_indexed_value_local >> metis_tac[])
     >- (rpt gen_tac >> strip_tac >> irule normalize_indexed_value_local >> metis_tac[])
     >- (rpt gen_tac >> strip_tac >> irule normalize_indexed_value_local >> metis_tac[])
     >- (rpt gen_tac >> strip_tac >> irule normalize_indexed_value_local >> metis_tac[]) >>
     (`LENGTH vals * type_memory_size stv <= scap * type_memory_size stv /\
       LENGTH vals * type_memory_size dtv <= cap * type_memory_size dtv` by
        (conj_tac >> simp[LE_MULT_RCANCEL]) >>
      rpt (qpat_x_assum `_ <= _` mp_tac) >> decide_tac))) >>
  strip_tac >> qexists_tac `t` >>
  qpat_x_assum `Abbrev (Child = _)` kall_tac >> qpat_x_assum `Child` kall_tac >>
  simp[] >> suspend "dyn_finish"
QED
Resume normalize_dynarray_semantic_counted[dyn_child]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `j < LENGTH vals` >>
  `a+32+j*type_memory_size stv+type_memory_size stv <=
      a+32+LENGTH vals*type_memory_size stv /\
   b+32+j*type_memory_size dtv+type_memory_size dtv <=
      b+32+LENGTH vals*type_memory_size dtv` by
    metis_tac[typed_copy_array_subinterval] >>
  `a+32+type_memory_size stv*j < dimword(:256) /\
   b+32+type_memory_size dtv*j < dimword(:256)` by
    (fs[Once MULT_COMM] >> decide_tac) >>
  `(!x. Var ("%" ++ toString (sa.cs_next_var+10)) = Var x \/
          Var ("%" ++ toString (sa.cs_next_var+11)) = Var x ==>
      not_fresh_at sc x)` by (simp[] >> metis_tac[]) >>
  qpat_x_assum `Child` mp_tac >> simp[Abbr `Child`] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspec_then `EL j vals` mp_tac) >> simp[] >>
  (impl_tac >-
    (conj_tac >- (rpt strip_tac >> gvs[]) >>
     rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >>
     qpat_x_assum `a+32+_ <= a+_+32` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >>
     qpat_x_assum `b+32+_ <= b+_+32` (mp_tac o ONCE_REWRITE_RULE [MULT_COMM]) >>
     rpt strip_tac >> decide_tac)) >>
  strip_tac >> qexists_tac `v` >> simp[] >> first_assum ACCEPT_TAC
QED
Resume normalize_dynarray_semantic_counted[dyn_finish]:
  conj_tac
  >- (simp[typed_copy_dynarray_representation,mem_word_at_eq_mload] >>
      gvs[MULT_COMM,ADD_COMM]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >>
      `LENGTH vals * type_memory_size dtv <= cap * type_memory_size dtv` by
        simp[LE_MULT_RCANCEL] >>
      qpat_assum `type_memory_bytes ce dt = _` (fn th => pure_rewrite_tac[th]) >>
      pure_rewrite_tac[type_memory_size_def] >>
      rule_assum_tac (PURE_REWRITE_RULE [type_memory_size_def]) >>
      once_rewrite_tac[MULT_COMM] >>
      rpt (qpat_x_assum `_ <= _` mp_tac) >> decide_tac) >> gvs[]
QED
Finalise normalize_dynarray_semantic_counted

Theorem normalize_dynarray_semantic_mem_path:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  type_memory_bytes ce st = type_memory_size stv /\
  type_memory_bytes ce dt = type_memory_size dtv /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  scap <= cap /\ cap < dimword(:256) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  a + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  b + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next /\
  a + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword(:256) /\
  b + type_memory_size (ArrayTV dtv (Dynamic cap)) < dimword(:256) /\
  (a + type_memory_size (ArrayTV stv (Dynamic scap)) <= b \/
   b + type_memory_size (ArrayTV dtv (Dynamic cap)) <= a) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) a s.vs_memory /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  (!cv sp dp sc ec u sw dw.
    val_wf stv cv /\ val_wf dtv cv /\
    value_has_type stv cv /\ value_has_type dtv cv /\
    compile_store_memory_typed ce dp dt sp st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    (!x. sp = Var x \/ dp = Var x ==> not_fresh_at sc x) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand sp u = SOME sw /\ eval_operand dp u = SOME dw /\
    val_in_memory stv cv (w2n sw) u.vs_memory /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    w2n sw + type_memory_size stv < dimword(:256) /\
    w2n dw + type_memory_size dtv < dimword(:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size dtv <= w2n sw) ==>
    ?v. gas_marked_path T ctx fn u 0 (OK v) /\
      mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\
      val_in_memory dtv cv (w2n dw) v.vs_memory /\
      (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. gas_marked_path T ctx fn s 0 (OK t) /\
    mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) b t.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_size (ArrayTV dtv (Dynamic cap)) <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (normalize_dynarray_semantic_counted |> SPEC_ALL |>
    Q.INST [`counted` |-> `T`] |>
    PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES]) >> simp[]
QED
