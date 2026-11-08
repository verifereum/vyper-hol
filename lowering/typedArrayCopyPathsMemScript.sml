(* Operational paths for the control and pointer portions of typed array copies. *)
Theory typedArrayCopyPathsMem
Ancestors
  typedCopyOperationalPaths typedArrayBoundControlMem typedArrayLoopLayoutMem typedArrayLoopControlMem
  typedNormalizeDynarrayLoop typedNormalizeDynarray venomExecProps
  valueEncoding valueEncodingProps venomMemProps
  fragGasSeqMem fragGasPathMem venomExecSemantics venomState venomInst
  emitHelperProps exprLoweringProps typedNormalizeLoop typedNormalizeContinuation compileEnv
  words arithmetic list rich_list

Theorem typed_array_bound_header_path_mem:
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
  ?count. gas_path_mem ctx fn s count
    (OK (jump_to (if i < n then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i n s)))
Proof
  strip_tac >>
  drule_all typed_array_bound_header_control >> disch_then assume_tac >>
  drule typed_array_bound_header_mem_safe >> disch_then assume_tac >>
  irule exec_block_no_phi_path_mem >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[mk_inst_def, jump_to_def, typed_sa_header_state_def, update_var_def]
QED

Theorem typed_sa_backedge_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ typed_sa_backedge_insts id ctr nv hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) /\
  lookup_block hdr fn.fn_blocks = SOME header_bb /\
  phi_prefix_length header_bb.bb_instructions = 0 ==>
  ?count. gas_path_mem ctx fn s count
    (OK (jump_to hdr (typed_sa_backedge_state ctr nv i s)))
Proof
  strip_tac >>
  drule_all typed_sa_backedge_control >> disch_then assume_tac >>
  drule_all typed_sa_backedge_mem_safe >> disch_then assume_tac >>
  irule exec_block_no_phi_path_mem >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[DROP_APPEND, typed_sa_backedge_insts_def, mk_inst_def, jump_to_def,
       typed_sa_backedge_state_def, update_var_def]
QED

Theorem typed_sa_pointer_path_mem:
  code =
    [mk_inst id MUL [Var ctr; Lit (n2w src_stride)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w dst_stride)] [dso];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var dso] [dp]] /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code bb.bb_instructions /\
  ALL_DISTINCT [so;dso;sp;dp] /\ ~MEM ctr [so;dso;sp;dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so;dso;sp;dp]) /\
  eval_operand src s = SOME (n2w source_base) /\
  eval_operand dst s = SOME (n2w dest_base) /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ u.vs_inst_idx = 4 /\
    eval_operand (Var sp) u = SOME (n2w (source_base + src_stride*i)) /\
    eval_operand (Var dp) u = SOME (n2w (dest_base + dst_stride*i)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. ~MEM x [so;dso;sp;dp] ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_sa_pointer_run >>
  disch_then (qspecl_then [`src_stride`, `id`, `dst_stride`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexists_tac `q with vs_inst_idx := 4` >> conj_tac
  >- (`gas_path_mem ctx fn s
         (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
         (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
        (irule run_inst_seq_gas_path_mem >>
         gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
      gvs[mk_inst_def]) >>
  fs[venom_state_component_equality, eval_operand_def, lookup_var_def]
QED

(* The recursive callback supplies its path and frame at one shared endpoint. *)
Theorem typed_array_pointer_child_path_mem:
  sc.cs_current_insts =
    [mk_inst id MUL [Var ctr; Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [dso];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var dso] [dp]] /\
  lookup_block sc.cs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX sc.cs_current_insts bb.bb_instructions /\
  ALL_DISTINCT [so;dso;sp;dp] /\ ~MEM ctr [so;dso;sp;dp] /\
  not_fresh_at sc ctr /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so;dso;sp;dp]) /\
  eval_operand src s = SOME (n2w a) /\
  eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ s.vs_current_bb = sc.cs_current_bb /\
  i < n /\ a+ss*n <= s.vs_alloca_next /\ b+ds*n <= s.vs_alloca_next /\
  Src i (a+ss*i) s.vs_memory /\
  (!j u. j < n /\ ~u.vs_halted /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand (Var sp) u = SOME (n2w (a+ss*j)) /\
    eval_operand (Var dp) u = SOME (n2w (b+ds*j)) /\
    a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
    Src j (a+ss*j) u.vs_memory ==>
    ?count v. gas_path_mem ctx fn u count (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\
      D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?count v. gas_path_mem ctx fn s count (OK v) /\ ~v.vs_halted /\
    v.vs_current_bb = ec.cs_current_bb /\
    v.vs_inst_idx = LENGTH ec.cs_current_insts /\
    eval_operand (Var ctr) v = SOME (n2w i) /\
    D i (b+ds*i) v.vs_memory /\
    (!p k. p+k <= b+ds*i \/ b+ds*i+ds <= p ==>
      mem_bytes_at p k v.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sc x /\ ~MEM x [so;dso;sp;dp] ==>
      lookup_var x v = lookup_var x s)
Proof
  strip_tac >>
  `?u. gas_path_mem ctx fn s 0 (OK u) /\ u.vs_inst_idx = 4 /\
    eval_operand (Var sp) u = SOME (n2w (a+ss*i)) /\
    eval_operand (Var dp) u = SOME (n2w (b+ds*i)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. ~MEM x [so;dso;sp;dp] ==> lookup_var x u = lookup_var x s)` by
    (irule typed_sa_pointer_path_mem >> simp[] >>
     qexistsl_tac [`ctr`, `dst`, `id`, `src`] >> gvs[] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qpat_x_assum `!j u. _` (qspecl_then [`i`, `u`] mp_tac) >>
  (impl_tac >- gvs[]) >>
  disch_then (qx_choose_then `ngas` (qx_choose_then `v` strip_assume_tac)) >>
  qexistsl_tac [`ngas`, `v`] >>
  conj_tac
  >- (drule_all gas_path_mem_then >> simp[]) >>
  simp[] >> conj_tac
  >- (gvs[eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem gas_path_mem_finite_iteration:
  !n i s.
    i <= n /\ Inv i s /\ ~s.vs_halted /\
    (!j u. Inv j u /\ j < n ==>
      ?count v. gas_path_mem ctx fn u count (OK v) /\ Inv (SUC j) v /\
        ~v.vs_halted) ==>
    ?count t. gas_path_mem ctx fn s count (OK t) /\ Inv n t /\ ~t.vs_halted
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> qexistsl_tac [`0`, `s`] >>
      simp[cj 1 gas_path_mem_rules]) >>
  Cases_on `i = SUC n`
  >- (gvs[] >> qexistsl_tac [`0`, `s`] >>
      simp[cj 1 gas_path_mem_rules]) >>
  `i <= n` by decide_tac >>
  `!j u. Inv j u /\ j < n ==>
    ?count v. gas_path_mem ctx fn u count (OK v) /\ Inv (SUC j) v /\
      ~v.vs_halted` by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!i s. i <= n /\ _ ==> _`
    (qspecl_then [`i`, `s`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `ngas` (qx_choose_then `t` strip_assume_tac)) >>
  `?m v. gas_path_mem ctx fn t m (OK v) /\ Inv (SUC n) v /\ ~v.vs_halted` by
    (qpat_assum `!j u. Inv j u /\ j < SUC n ==> _` irule >> simp[]) >>
  qexistsl_tac [`ngas+m`, `v`] >> reverse conj_tac >- simp[] >>
  irule gas_path_mem_then >> qexists_tac `t` >> simp[]
QED

Theorem typed_array_child_backedge_path_mem:
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := ec.cs_current_bb; bb_instructions := ec.cs_current_insts ++
      typed_sa_backedge_insts ec.cs_next_id ("%" ++ toString sa.cs_next_var)
        ("%" ++ toString ec.cs_next_var) hdr|> /\
  lookup_block hdr fn.fn_blocks = SOME header_bb /\
  phi_prefix_length header_bb.bb_instructions = 0 /\
  s.vs_current_bb = ec.cs_current_bb /\ s.vs_inst_idx = LENGTH ec.cs_current_insts /\
  ~s.vs_halted /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  i < n /\ n < dimword(:256) /\ sa.cs_next_var <= ec.cs_next_var ==>
  ?count t. gas_path_mem ctx fn s count (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) t = SOME (n2w (SUC i)) /\
    (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `?ngas. gas_path_mem ctx fn s ngas
    (OK (jump_to hdr (typed_sa_backedge_state ("%" ++ toString sa.cs_next_var)
      ("%" ++ toString ec.cs_next_var) i s)))` by
    (irule typed_sa_backedge_path_mem >> simp[] >>
     conj_tac >- (qexists_tac `n` >> simp[]) >>
     qexistsl_tac [`ec.cs_next_id`, `ec.cs_current_insts`] >> simp[]) >>
  goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_backedge_state_def, update_var_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[LESS_EQ_TRANS, LESS_EQ_REFL]
QED

Theorem typed_sarray_body_path_mem:
  sc.cs_current_insts =
    [mk_inst id MUL [Var ("%" ++ toString sa.cs_next_var); Lit (n2w ss)]
       ["%" ++ toString (sa.cs_next_var+3)];
     mk_inst (id+1) MUL [Var ("%" ++ toString sa.cs_next_var); Lit (n2w ds)]
       ["%" ++ toString (sa.cs_next_var+4)];
     mk_inst (id+2) ADD [src; Var ("%" ++ toString (sa.cs_next_var+3))]
       ["%" ++ toString (sa.cs_next_var+5)];
     mk_inst (id+3) ADD [dst; Var ("%" ++ toString (sa.cs_next_var+4))]
       ["%" ++ toString (sa.cs_next_var+6)]] /\
  sc.cs_next_var = sa.cs_next_var+7 /\ ci_mono sc ec /\
  lookup_block sc.cs_current_bb fn.fn_blocks = SOME body_bb /\
  isPREFIX sc.cs_current_insts body_bb.bb_instructions /\
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := ec.cs_current_bb; bb_instructions := ec.cs_current_insts ++
      typed_sa_backedge_insts ec.cs_next_id ("%" ++ toString sa.cs_next_var)
        ("%" ++ toString ec.cs_next_var) hdr|> /\
  lookup_block hdr fn.fn_blocks = SOME header_bb /\
  phi_prefix_length header_bb.bb_instructions = 0 /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ s.vs_current_bb = sc.cs_current_bb /\
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
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) u = SOME (n2w (a+ss*j)) /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+6))) u = SOME (n2w (b+ds*j)) /\
    a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
    Src j (a+ss*j) u.vs_memory ==>
    ?count v. gas_path_mem ctx fn u count (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?count t. gas_path_mem ctx fn s count (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) t = SOME (n2w (SUC i)) /\
    (!j. j < n ==> Src j (a+ss*j) t.vs_memory) /\
    (!j. j < SUC i ==> D j (b+ds*j) t.vs_memory) /\
    mem_bytes_at a (ss*n) t.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+ds*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_sarray_pointer_fresh >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `Src i (a+ss*i) s.vs_memory` by metis_tac[] >>
  drule_all typed_array_pointer_child_path_mem >>
  disch_then (qx_choose_then `ngas` (qx_choose_then `v` strip_assume_tac)) >>
  qpat_x_assum `!j u. _ ==> ?count v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  qpat_x_assum `isPREFIX _ _` kall_tac >>
  `sa.cs_next_var <= ec.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  drule_all typed_array_child_backedge_path_mem >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `mgas` (qx_choose_then `t` strip_assume_tac))) >>
  `t.vs_memory = v.vs_memory` by
    (qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _;
      vs_inst_idx := _; vs_prev_bb := _|> = v` mp_tac >>
     simp[venom_state_component_equality]) >>
  `mem_bytes_at a (ss*n) v.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
   (!p k. p+k <= b \/ b+ds*n <= p ==>
     mem_bytes_at p k v.vs_memory = mem_bytes_at p k s.vs_memory)` by
    (irule typed_array_child_exterior >> reverse conj_tac
     >- first_assum ACCEPT_TAC >> qexists_tac `i` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`ngas+mgas`, `t`] >>
  conj_tac >- (irule gas_path_mem_then >> qexists_tac `v` >> simp[]) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "memory_frame"
QED
Resume typed_sarray_body_path_mem[memory_frame]:
  qpat_x_assum `t.vs_memory = v.vs_memory` (fn th => pure_rewrite_tac[th]) >>
  conj_tac
  >- (match_mp_tac (Q.INST [`mem` |-> `s.vs_memory`] typed_array_local_source_frame) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (match_mp_tac (Q.INST [`mem` |-> `s.vs_memory`, `n` |-> `n`]
        typed_array_local_prefix_step) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
        vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
      qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _;
        vs_inst_idx := _; vs_prev_bb := _|> = v` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[venom_state_component_equality] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `lookup_var x t = lookup_var x v` by metis_tac[] >>
  `lookup_var x v = lookup_var x s` by metis_tac[] >> simp[]
QED
Finalise typed_sarray_body_path_mem

Theorem typed_array_bound_header_entry_path_mem:
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
  ?count u. gas_path_mem ctx fn s count (OK u) /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if i < n then body_lbl else exit_lbl) /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sm x \/ x = "%" ++ toString sm.cs_next_var ==>
      lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  qpat_x_assum `s.vs_current_bb = hdr` (SUBST_ALL_TAC o SYM) >>
  drule_all typed_array_bound_header_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
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
    ?count v. gas_path_mem ctx fn u count (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?count t. gas_path_mem ctx fn s count (OK t) /\ ~t.vs_halted /\
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
  drule_all typed_array_bound_header_entry_path_mem >> asm_rewrite_tac[] >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `ngas` (qx_choose_then `u` strip_assume_tac))) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME (n2w a) /\
   eval_operand dst u = SOME (n2w b) /\
   eval_operand (Var ("%" ++ toString sm.cs_next_var)) u = SOME (n2w i)` by
    suspend "operands" >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
   (!j. j < n ==> Src j (a+ss*j) u.vs_memory) /\
   (!j. j < i ==> D j (b+ds*j) u.vs_memory)` by asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `lookup_block hdr fn.fn_blocks = SOME header_bb` >>
  `phi_prefix_length header_bb.bb_instructions = 0` by
    simp[Abbr `header_bb`, phi_prefix_length_def, mk_inst_def] >>
  drule_all typed_sarray_body_path_mem >>
  disch_then (qx_choose_then `mgas` (qx_choose_then `t` strip_assume_tac)) >>
  qpat_x_assum `!j u. _ ==> ?count v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  suspend "finish"
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
  qexistsl_tac [`ngas+mgas`, `t`] >>
  conj_tac >- (irule gas_path_mem_then >> qexists_tac `u` >> simp[]) >>
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
    ?count v. gas_path_mem ctx fn u count (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?count t. gas_path_mem ctx fn s count (OK t) /\ ~t.vs_halted /\
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
     ?count v. gas_path_mem ctx fn u count (OK v) /\ Inv (SUC j) v /\ ~v.vs_halted` by
    suspend "iteration_step" >>
  `?count t. gas_path_mem ctx fn s count (OK t) /\ Inv n t /\ ~t.vs_halted` by
    (irule gas_path_mem_finite_iteration >>
     simp[] >> qexists_tac `i` >> simp[]) >>
  qpat_x_assum `gas_path_mem ctx fn s _ (OK t)`
    (fn th => irule_at (Pos hd) th) >>
  qpat_x_assum `Inv n t` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  strip_tac >> first_assum ACCEPT_TAC
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
  drule_all typed_dynarray_header_successor_path_mem >>
  disch_then (qx_choose_then `ngas` (qx_choose_then `t` strip_assume_tac)) >>
  qpat_x_assum `!j u. _ ==> ?count v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  suspend "iteration_frame"
QED
Resume typed_dynarray_header_iteration_path_mem[iteration_frame]:
  qexistsl_tac [`ngas`, `t`] >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
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

Theorem typed_dynarray_compiler_iteration_path_mem:
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
      ?count v. gas_path_mem ctx fn u count (OK v) /\ ~v.vs_halted /\
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
  ?count t. gas_path_mem ctx fn s count (OK t) /\ ~t.vs_halted /\
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
  irule typed_dynarray_header_iteration_path_mem >>
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

Theorem typed_sa_initial_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id ASSIGN [Lit 0w] [ctr]; mk_inst (id+1) JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  ?count. gas_path_mem ctx fn s count (OK (jump_to hdr (update_var ctr 0w s)))
Proof
  strip_tac >> drule_all typed_sa_initial_exec >> disch_then assume_tac >>
  irule exec_block_no_phi_path_mem >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[DROP_APPEND, mk_inst_def, jump_to_def, update_var_def]
QED

Theorem typed_dynarray_initial_path_mem[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\ sm.cs_next_var = sa.cs_next_var+5 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts+7 ==>
  ?count u. gas_path_mem ctx fn s count (OK u) /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
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
  `?count. gas_path_mem ctx fn s count
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
  goal_assum (drule_at Any) >>
  simp[jump_to_def, update_var_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem typed_dynarray_exit_path_mem[local]:
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
  ?count u. gas_path_mem ctx fn s count (OK u) /\ ~u.vs_halted /\
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
    (Q.INST [`id` |-> `sa.cs_next_id+9`] typed_array_bound_header_path_mem)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``k+5 <= k+6 /\ k+5 <= k+7``]
QED

Theorem typed_dynarray_suffix_path_mem:
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
      ?count v. gas_path_mem ctx fn u count (OK v) /\ ~v.vs_halted /\
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
  ?count t. gas_path_mem ctx fn s count (OK t) /\ ~t.vs_halted /\
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
  drule_all typed_dynarray_initial_path_mem >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `ngas` (qx_choose_then `u` strip_assume_tac))) >>
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
Resume typed_dynarray_suffix_path_mem[operands]:
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
Resume typed_dynarray_suffix_path_mem[iterate]:
  mp_tac (Q.INST [`s` |-> `u`, `i` |-> `0:num`] typed_dynarray_compiler_iteration_path_mem) >>
  (impl_tac >- (gvs[Abbr `Callback`, MULT_COMM] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `mgas` (qx_choose_then `v` strip_assume_tac)) >>
  suspend "exit"
QED
Resume typed_dynarray_suffix_path_mem[exit]:
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`Abbrev (Callback = _)`, `Callback`,
     `!j addr m m'. _ ==> (Src j addr m = _)`,
     `!j addr m m'. _ ==> (D j addr m = _)`,
     `!j. j < n ==> Src j _ s.vs_memory`] >>
  `eval_operand (Var ("%" ++ toString sm.cs_next_var)) v = SOME (n2w n)` by gvs[] >>
  drule_all typed_dynarray_exit_path_mem >>
  disch_then (qspec_then `ctx`
    (qx_choose_then `kgas` (qx_choose_then `t` strip_assume_tac))) >>
  `t.vs_memory = v.vs_memory` by
    (qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v`
       mp_tac >> simp[venom_state_component_equality]) >>
  qexistsl_tac [`ngas+(mgas+kgas)`, `t`] >>
  conj_tac
  >- (irule gas_path_mem_then >> qexists_tac `u` >> conj_tac
      >- first_assum ACCEPT_TAC >>
      irule gas_path_mem_then >> qexists_tac `v` >> simp[]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  suspend "frame"
QED
Resume typed_dynarray_suffix_path_mem[frame]:
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v` mp_tac >>
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
    vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED
Finalise typed_dynarray_suffix_path_mem

Theorem typed_dynarray_prefix_path_mem[local]:
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w n /\ n <= cap /\ cap < dimword(:256) /\
  32 <= sz /\ 32 <= dz /\
  w2n p+sz <= s.vs_alloca_next /\ w2n d+dz <= s.vs_alloca_next /\
  (w2n p+sz <= w2n d \/ w2n d+dz <= w2n p) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\ ~q.vs_halted /\
    q.vs_current_bb = sa.cs_current_bb /\
    q.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) q = SOME (n2w n) /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+3))) q =
      SOME (n2w (w2n p+32)) /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+4))) q =
      SOME (n2w (w2n d+32)) /\
    q.vs_memory = (mstore (w2n d) (n2w n) s).vs_memory /\
    mem_bytes_at (w2n p) sz q.vs_memory = mem_bytes_at (w2n p) sz s.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+32 <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_dynarray_compiler_prefix >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `sm` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `sm.cs_current_insts = _ ++ code` >>
  `ALL_DISTINCT ["%" ++ toString sa.cs_next_var;
    "%" ++ toString (sa.cs_next_var+1); "%" ++ toString (sa.cs_next_var+2);
    "%" ++ toString (sa.cs_next_var+3); "%" ++ toString (sa.cs_next_var+4)]` by
    simp[ASCIInumbersTheory.toString_inj] >>
  `!x. src = Var x \/ dst = Var x ==>
    ~MEM x ["%" ++ toString sa.cs_next_var;
    "%" ++ toString (sa.cs_next_var+1); "%" ++ toString (sa.cs_next_var+2);
    "%" ++ toString (sa.cs_next_var+3); "%" ++ toString (sa.cs_next_var+4)]` by
    (rpt gen_tac >> disch_tac >>
     `not_fresh_at sa x` by metis_tac[] >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]) >>
  suspend "run"
QED
Resume typed_dynarray_prefix_path_mem[run]:
  qpat_x_assum `Abbrev (code = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all typed_dynarray_prologue_window_run >> strip_tac >>
  `LENGTH code = 7 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0` by
    simp[mk_inst_def, is_terminator_def] >>
  qpat_x_assum `code = _` kall_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sa sm fn` mp_tac >>
     simp[fragExecTheory.fn_has_code_def] >> strip_tac >>
     goal_assum (drule_at Any) >>
     fs[IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `gas_path_mem ctx fn s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
    (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (irule run_inst_seq_gas_path_mem >> goal_assum (drule_at Any) >> gvs[]) >>
  `gas_path_mem ctx fn s 0 (OK (q with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    gvs[] >>
  suspend "finish"
QED
Resume typed_dynarray_prefix_path_mem[finish]:
  qexists_tac `q with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `x <> "%" ++ toString sa.cs_next_var /\
   x <> "%" ++ toString (sa.cs_next_var+1) /\
   x <> "%" ++ toString (sa.cs_next_var+2) /\
   x <> "%" ++ toString (sa.cs_next_var+3) /\
   x <> "%" ++ toString (sa.cs_next_var+4)` by
    (gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]) >>
  first_x_assum irule >> gvs[]
QED
Finalise typed_dynarray_prefix_path_mem

Theorem typed_dynarray_compiler_path_mem:
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
      ?count v. gas_path_mem ctx fn u count (OK v) /\ ~v.vs_halted /\
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
  ?count t. gas_path_mem ctx fn s count (OK t) /\ ~t.vs_halted /\
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
  suspend "suffix"
QED
Resume typed_dynarray_compiler_path_mem[suffix]:
  `q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `!j. j < n ==> Src j (a+32+type_memory_bytes ce st*j) q.vs_memory` by
    suspend "source" >>
  mp_tac (Q.INST [`s` |-> `q`, `a` |-> `a+32`, `b` |-> `b+32`,
    `sm` |-> `sa with cs_next_var := sa.cs_next_var+5`] typed_dynarray_suffix_path_mem) >>
  (impl_tac >- (simp[Abbr `Callback`] >>
    qpat_x_assum `~(_ /\ _)` mp_tac >> simp[])) >>
  disch_then (qx_choose_then `ngas` (qx_choose_then `t` strip_assume_tac)) >>
  suspend "finish"
QED
Resume typed_dynarray_compiler_path_mem[source]:
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
Resume typed_dynarray_compiler_path_mem[finish]:
  qpat_x_assum `Abbrev (Callback = _)` kall_tac >>
  qpat_x_assum `Callback` kall_tac >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`!j addr m m'. _ ==> (Src j addr m = _)`,
     `!j addr m m'. _ ==> (D j addr m = _)`] >>
  qexistsl_tac [`0+ngas`, `t`] >>
  conj_tac >- (irule gas_path_mem_then >> qexists_tac `q` >> simp[]) >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "whole_source" >>
  conj_asm1_tac >- suspend "length" >>
  conj_tac >- suspend "length_word" >>
  conj_tac >- suspend "exterior" >>
  conj_tac >- suspend "state" >>
  suspend "registers"
QED
Resume typed_dynarray_compiler_path_mem[whole_source]:
  `mem_bytes_at a (32+type_memory_bytes ce st*n) t.vs_memory =
   mem_bytes_at a (32+type_memory_bytes ce st*n) q.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` irule >> decide_tac) >>
  metis_tac[]
QED
Resume typed_dynarray_compiler_path_mem[length]:
  `mem_bytes_at b 32 t.vs_memory = mem_bytes_at b 32 q.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` irule >> simp[]) >>
  gvs[]
QED
Resume typed_dynarray_compiler_path_mem[length_word]:
  `mload b t = mload b (mstore b (n2w n) s)` by
    (qpat_x_assum `mem_bytes_at b 32 t.vs_memory = _` mp_tac >>
     pure_rewrite_tac[GSYM mem_word_at_eq_mload, mem_word_at_def, mem_bytes_at_def] >>
     disch_then SUBST1_TAC >> REFL_TAC) >>
  gvs[mload_mstore_same]
QED
Resume typed_dynarray_compiler_path_mem[exterior]:
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at p' k t.vs_memory = mem_bytes_at p' k q.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k t.vs_memory = _` irule >> decide_tac) >>
  `mem_bytes_at p' k q.vs_memory = mem_bytes_at p' k s.vs_memory` by
    (qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = _` irule >> simp[] >> decide_tac) >>
  metis_tac[]
QED
Resume typed_dynarray_compiler_path_mem[state]:
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = q` mp_tac >>
  qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED
Resume typed_dynarray_compiler_path_mem[registers]:
  rpt strip_tac >>
  `not_fresh_at (sa with cs_next_var := sa.cs_next_var+5) x` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED
Finalise typed_dynarray_compiler_path_mem
