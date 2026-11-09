(* Finite one-iteration paths with a same-endpoint element callback. *)
Theory typedArrayIterationPathMem
Ancestors
  typedArrayLoopPathMem typedArrayLoopLayoutMem typedNormalizeLoop
  typedArrayLoopControlMem
  fragGasSeqMem fragGasPathMem context compileEnv exprLoweringProps emitHelperProps
  venomInst venomState venomExecSemantics words arithmetic list rich_list

Theorem typed_sa_pointer_path_mem[local]:
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
  >- (`EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode) code /\
       FILTER (\j. j.inst_opcode = GAS) code = [] /\ LENGTH code = 4` by
        simp[mk_inst_def, is_terminator_def] >>
      `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
        (qpat_x_assum `s.vs_inst_idx = 0` (fn th => rewrite_tac[th, DROP_0]) >>
         first_assum ACCEPT_TAC) >>
      qpat_x_assum `code = _` SUBST_ALL_TAC >>
      drule_all run_inst_seq_gas_path_mem >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  fs[venom_state_component_equality, eval_operand_def, lookup_var_def]
QED

Theorem typed_array_pointer_child_path_mem[local]:
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
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ s.vs_current_bb = sc.cs_current_bb /\
  i < n /\ a+ss*n <= s.vs_alloca_next /\ b+ds*n <= s.vs_alloca_next /\
  Src i (a+ss*i) s.vs_memory /\
  (!j u. j < n /\ ~u.vs_halted /\
    u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand (Var sp) u = SOME (n2w (a+ss*j)) /\
    eval_operand (Var dp) u = SOME (n2w (b+ds*j)) /\
    a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
    Src j (a+ss*j) u.vs_memory ==>
    ?v g. gas_path_mem ctx fn u g (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\ v.vs_inst_idx = LENGTH ec.cs_current_insts /\
      D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?v g. gas_path_mem ctx fn s g (OK v) /\ ~v.vs_halted /\
    v.vs_current_bb = ec.cs_current_bb /\ v.vs_inst_idx = LENGTH ec.cs_current_insts /\
    eval_operand (Var ctr) v = SOME (n2w i) /\ D i (b+ds*i) v.vs_memory /\
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
  (impl_tac >- gvs[]) >> strip_tac >> qexistsl_tac [`v`, `g`] >>
  conj_tac >- metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  simp[] >> conj_tac >- (gvs[eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem typed_array_child_backedge_path_mem[local]:
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
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) t = SOME (n2w (SUC i)) /\
    (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `gas_path_mem ctx fn s 0
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

Theorem typed_sarray_body_successor_path_mem:
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
    ?v g. gas_path_mem ctx fn u g (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
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
  drule_all typed_array_pointer_child_path_mem >> strip_tac >>
  qpat_x_assum `!j u. _ ==> ?v g. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  qpat_x_assum `isPREFIX _ _` kall_tac >>
  `sa.cs_next_var <= ec.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  drule_all typed_array_child_backedge_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `t.vs_memory = v.vs_memory` by
    (qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _;
      vs_inst_idx := _; vs_prev_bb := _|> = v` mp_tac >>
     simp[venom_state_component_equality]) >>
  `mem_bytes_at a (ss*n) v.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
   (!p k. p+k <= b \/ b+ds*n <= p ==>
     mem_bytes_at p k v.vs_memory = mem_bytes_at p k s.vs_memory)` by
    (irule typed_array_child_exterior >> reverse conj_tac
     >- first_assum ACCEPT_TAC >> qexists_tac `i` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t`, `g`] >>
  conj_tac >- metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
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
  rpt strip_tac >> metis_tac[]
QED

Theorem typed_sarray_header_entry_path_mem[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var ==>
      lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_sarray_child_decompose >> strip_tac >>
  map_every (fn pat => rpt (qpat_x_assum pat kall_tac))
    [`compile_store_memory_typed _ _ _ _ _ _ = _`, `sb = _`,
     `sc.cs_current_insts = _`, `cs_extends _ _`, `fn_has_code _ _ _`,
     `ci_mono _ _`, `LENGTH sc.cs_current_insts = _`, `sc.cs_next_var = _`,
     `isPREFIX _ _`] >>
  `gas_path_mem ctx fn s 0
    (OK (jump_to (if i < ncount then fresh_label_output "typed_sa_body" (sa.cs_next_label+1)
              else fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
      (typed_sa_header_state ("%" ++ toString (sa.cs_next_var+1))
        ("%" ++ toString (sa.cs_next_var+2)) i ncount s)))` by
    (irule typed_sa_header_path_mem >> simp[] >>
     qexistsl_tac [`"%" ++ toString sa.cs_next_var`, `sa.cs_next_id+2`] >>
     simp[] >> metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  gvs[] >> goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``n <= n+1 /\ n <= n+2``]
QED

Theorem typed_sarray_header_successor_path_mem:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sb) /\
  fn_has_code sa sb fn /\
  sc.cs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
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
        ("%" ++ toString ec.cs_next_var)
        (fresh_label_output "typed_sa_cond" sa.cs_next_label)|> /\
  lookup_block (fresh_label_output "typed_sa_cond" sa.cs_next_label)
    fn.fn_blocks = SOME header_bb /\
  phi_prefix_length header_bb.bb_instructions = 0 /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
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
    ?v g. gas_path_mem ctx fn u g (OK v) /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    t.vs_inst_idx = 0 /\
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
  drule_all typed_sarray_header_entry_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME (n2w a) /\
   eval_operand dst u = SOME (n2w b) /\
   eval_operand (Var ("%" ++ toString sa.cs_next_var)) u = SOME (n2w i)` by
    (qpat_x_assum `!x. not_fresh_at sa x \/ _ ==> _` mp_tac >>
     qpat_x_assum `!x. src = Var x \/ _ ==> _` mp_tac >>
     ntac 3 (qpat_x_assum `eval_operand _ s = _` mp_tac) >>
     qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  `u.vs_current_bb = sc.cs_current_bb /\
   a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
   (!j. j < n ==> Src j (a+ss*j) u.vs_memory) /\
   (!j. j < i ==> D j (b+ds*j) u.vs_memory)` by asm_rewrite_tac[] >>
  drule_all typed_sarray_body_successor_path_mem >> strip_tac >>
  qpat_x_assum `!j u. _ ==> ?v g. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  qexistsl_tac [`t`, `g`] >>
  conj_tac >- metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `u.vs_memory = s.vs_memory`
        (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
        vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
      qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = s`
        mp_tac >>
      rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> metis_tac[]
QED
