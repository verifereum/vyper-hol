Theory typedCopyDynarrayPathMem
Ancestors
  typedNormalizeDynarrayLoop typedCopySarrayPathMem typedCopyControlPathMem
  typedCopyArrayEntryPathMem exprSimBopRestWordLoopPath fragGasSeqMem
  fragGasPathMem fragGasMode fragExecMem instMemFrontier memSafeRun
  typedArrayLoopControlMem context compileEnv emitHelper
  exprLoweringProps venomState venomExecSemantics venomInst words arithmetic list rich_list

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
  gas_path_mem ctx fn s 0
    (OK (jump_to (if i < n then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i n s)))
Proof
  strip_tac >>
  `gas_marked_path T ctx fn s 0
    (OK (typed_sa_header_state cmp done i n s with vs_inst_idx := 2))` by
    (mp_tac (Q.INST
       [`code` |-> `[mk_inst id LT [Var ctr; bound] [cmp];
                     mk_inst (id+1) ISZERO [Var cmp] [done]]`,
        `t` |-> `typed_sa_header_state cmp done i n s`, `memory` |-> `T`,
        `bb` |-> `<|bb_label := hdr; bb_instructions :=
          [mk_inst id LT [Var ctr; bound] [cmp];
           mk_inst (id+1) ISZERO [Var cmp] [done];
           mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]|>`]
       rest_word_sequence_marked) >>
     simp[] >> disch_then irule >>
     simp[run_inst_seq_def, run_inst_seq_mem_ok_def, mk_inst_def, is_terminator_def,
          step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
          eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, below_frontier_no_ranges,
          typed_sa_header_state_def]) >>
  `gas_marked_path T ctx fn
    (typed_sa_header_state cmp done i n s with vs_inst_idx := 2) 0
    (OK (jump_to (if i < n then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i n s with vs_inst_idx := 2)))` by
    (irule rest_word_jump_marked >>
     conj_tac >- simp[typed_sa_header_state_def, update_var_def] >>
     qexistsl_tac
       [`<|bb_label := hdr; bb_instructions :=
          [mk_inst id LT [Var ctr; bound] [cmp];
           mk_inst (id+1) ISZERO [Var cmp] [done];
           mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []]|>`,
        `mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []`] >>
     simp[typed_sa_header_state_def, update_var_def, get_instruction_def,
          mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `i < n` >> simp[bool_to_word_def]) >>
  drule_all gas_marked_path_then >> simp[gas_marked_path_def, jump_to_def]
QED

Theorem typed_dynarray_header_path_mem[local]:
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
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if i < n then body_lbl else exit_lbl) /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x \/ x = "%" ++ toString sm.cs_next_var ==>
      lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  qpat_x_assum `s.vs_current_bb = hdr` (SUBST_ALL_TAC o SYM) >>
  drule_all typed_array_bound_header_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >> goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``n <= n+1 /\ n <= n+2``]
QED

Theorem typed_dynarray_header_successor_path_mem[local]:
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
    ?v. gas_path_mem ctx fn u 0 (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ ~t.vs_halted /\
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
  drule_all typed_dynarray_header_path_mem >> asm_rewrite_tac[] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
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
Resume typed_dynarray_header_successor_path_mem[operands]:
  qpat_x_assum `!x. not_fresh_at sm x \/ _ ==> _` mp_tac >>
  qpat_x_assum `!x. src = Var x \/ _ ==> _` mp_tac >>
  qpat_x_assum `eval_operand src s = _` mp_tac >>
  qpat_x_assum `eval_operand dst s = _` mp_tac >>
  qpat_x_assum `eval_operand (Var _) s = _` mp_tac >>
  qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]
QED
Resume typed_dynarray_header_successor_path_mem[body]:
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
   (!j. j < n ==> Src j (a+ss*j) u.vs_memory) /\
   (!j. j < i ==> D j (b+ds*j) u.vs_memory)` by asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac
    `lookup_block hdr fn.fn_blocks = SOME header_bb` >>
  `phi_prefix_length header_bb.bb_instructions = 0` by
    simp[Abbr `header_bb`, phi_prefix_length_def, mk_inst_def] >>
  drule_all typed_sarray_body_successor_path_mem >> strip_tac >>
  qpat_x_assum `!j u. _ ==> ?v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  suspend "finish"
QED
Resume typed_dynarray_header_successor_path_mem[finish]:
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
  conj_tac >- (irule (SIMP_RULE arith_ss []
    (Q.INST [`n` |-> `0:num`, `m` |-> `0:num`] gas_path_mem_then)) >>
    qexists_tac `u` >> simp[]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
Finalise typed_dynarray_header_successor_path_mem

Theorem typed_dynarray_header_iteration_path_mem[local]:
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
    ?v. gas_path_mem ctx fn u 0 (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ ~t.vs_halted /\
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
     simp[venom_state_component_equality]) >>
  `!j u. Inv j u /\ j < n ==>
     ?v. Inv (SUC j) v /\ gas_path_mem ctx fn u 0 (OK v)` by
    suspend "iteration_step" >>
  `!k j u. j+k = n /\ Inv j u ==>
     ?t. Inv n t /\ gas_path_mem ctx fn u 0 (OK t)` by
    suspend "finite_iteration" >>
  `?t. Inv n t /\ gas_path_mem ctx fn s 0 (OK t)` by
    (first_x_assum (qspecl_then [`n-i`, `i`, `s`] mp_tac) >> simp[]) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `Inv n t` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  strip_tac >> first_assum ACCEPT_TAC
QED
Resume typed_dynarray_header_iteration_path_mem[finite_iteration]:
  `!j u. Inv j u ==> ~u.vs_halted` by simp[Abbr `Inv`] >>
  qpat_x_assum `!j u. Inv j u ==> ~u.vs_halted` mp_tac >>
  qpat_x_assum `!j u. Inv j u /\ j < n ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt disch_tac >>
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> qexists_tac `u` >> conj_tac
      >- first_assum ACCEPT_TAC >>
      irule (cj 1 gas_path_mem_rules) >> metis_tac[]) >>
  `j < n` by decide_tac >>
  qpat_x_assum `!j u. Inv j u /\ j < n ==> _` drule >>
  disch_then drule >> strip_tac >>
  first_x_assum (qspecl_then [`SUC j`, `v`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  qexists_tac `t` >> simp[] >> drule_all gas_path_mem_then >> simp[]
QED
Resume typed_dynarray_header_iteration_path_mem[iteration_step]:
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
  drule_all typed_dynarray_header_successor_path_mem >> strip_tac >>
  qpat_x_assum `!j u. _ ==> ?v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  qexists_tac `t` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
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
Finalise typed_dynarray_header_iteration_path_mem
