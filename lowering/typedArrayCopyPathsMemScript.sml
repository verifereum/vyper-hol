(* Operational paths for the control and pointer portions of typed array copies. *)
Theory typedArrayCopyPathsMem
Ancestors
  typedCopyOperationalPaths typedArrayBoundControlMem typedArrayLoopLayoutMem typedArrayLoopControlMem
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
