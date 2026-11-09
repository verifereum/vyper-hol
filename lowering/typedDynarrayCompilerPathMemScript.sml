(* Finite memory-safe compiler control for dynamic-array normalization. *)
Theory typedDynarrayCompilerPathMem
Ancestors
  typedDynarrayIterationPathMem typedArrayCompilerPathMem typedNormalizeDynarrayLoop
  typedNormalizeLoop typedNormalizeContinuation fragGasPathMem
  venomExecSemantics venomExecProofs venomState venomInst compileEnv emitHelperProps
  exprLoweringProps words arithmetic list rich_list

Theorem typed_dynarray_initial_path_mem[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\ sm.cs_next_var = sa.cs_next_var+5 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts+7 ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
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
     asm_rewrite_tac[] >> conj_tac
     >- simp[phi_prefix_length_def, mk_inst_def] >>
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
  n < dimword(:256) ==>
  ?u g. gas_path_mem ctx fn s g (OK u) /\ ~u.vs_halted /\
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
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) s = SOME (n2w n)` by gvs[] >>
  `n <= n` by simp[] >>
  qpat_x_assum `s.vs_current_bb = _` (SUBST_ALL_TAC o SYM) >>
  `s.vs_current_bb = s.vs_current_bb` by simp[] >>
  drule_all (SIMP_RULE (pure_ss ++ numSimps.REDUCE_ss)
    [DECIDE ``!k:num. (k+9)+1=k+10 /\ (k+9)+2=k+11 /\
       (k+5)+1=k+6 /\ (k+5)+2=k+7``, combinTheory.K_THM,
     compile_state_accfupds, compile_state_accessors]
    (Q.INST [`id` |-> `sa.cs_next_id+9`,
      `sm` |-> `sa with cs_next_var := sa.cs_next_var+5`] typed_dynarray_header_path_mem)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`u`, `g`] >> gvs[] >>
  fs[not_fresh_at_def] >> metis_tac[]
QED

Theorem typed_dynarray_compiler_iteration_path_mem[local]:
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
      ?v g. gas_path_mem ctx fn u g (OK v) /\ ~v.vs_halted /\
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
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
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
  irule typed_dynarray_header_iteration_path_mem >> asm_rewrite_tac[] >>
  qpat_assum `ci_mono sc ec` (irule_at Any) >>
  qpat_assum `lookup_block sc.cs_current_bb _ = SOME body_bb` (irule_at Any) >>
  qexistsl_tac [`Var ("%" ++ toString (sa.cs_next_var+3))`,
    `sa.cs_next_id+12`, `i`, `sa.cs_next_id+9`,
    `fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2)`,
    `Var ("%" ++ toString (sa.cs_next_var+4))`] >>
  simp_tac (pure_ss ++ numSimps.REDUCE_ss)
    [DECIDE ``!k:num. (k+5)+1=k+6 /\ (k+5)+2=k+7 /\ (k+5)+3=k+8 /\
      (k+5)+4=k+9 /\ (k+5)+5=k+10 /\ (k+5)+6=k+11 /\ (k+5)+7=k+12 /\
      (k+9)+1=k+10 /\ (k+9)+2=k+11 /\
      (k+12)+1=k+13 /\ (k+12)+2=k+14 /\ (k+12)+3=k+15``] >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `Var _ = Var x` mp_tac >>
      simp[not_fresh_at_def] >> disch_then (SUBST1_TAC o SYM) >>
      simp[ASCIInumbersTheory.toString_inj]) >>
  qpat_x_assum `sb = _` kall_tac >> fs[basic_block_component_equality]
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
      ?v g. gas_path_mem ctx fn u g (OK v) /\ ~v.vs_halted /\
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
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
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
  disch_then (qspec_then `ctx` (qx_choose_then `u` strip_assume_tac)) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand (Var ("%" ++ toString (sa.cs_next_var+3))) u = SOME (n2w a) /\
   eval_operand (Var ("%" ++ toString (sa.cs_next_var+4))) u = SOME (n2w b) /\
   eval_operand (Var ("%" ++ toString sa.cs_next_var)) u = SOME (n2w n)` by
    (`not_fresh_at sm ("%" ++ toString (sa.cs_next_var+3)) /\
      not_fresh_at sm ("%" ++ toString (sa.cs_next_var+4)) /\
      not_fresh_at sm ("%" ++ toString sa.cs_next_var)` by
       (simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
        rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]) >>
     fs[eval_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `u`, `i` |-> `0:num`] typed_dynarray_compiler_iteration_path_mem) >>
  (impl_tac >- (gvs[Abbr `Callback`, MULT_COMM] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v` (qx_choose_then `g` strip_assume_tac)) >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`Abbrev (Callback = _)`, `Callback`,
     `!j addr m m'. _ ==> (Src j addr m = _)`,
     `!j addr m m'. _ ==> (D j addr m = _)`,
     `!j. j < n ==> Src j _ s.vs_memory`] >>
  `eval_operand (Var ("%" ++ toString sm.cs_next_var)) v = SOME (n2w n)` by gvs[] >>
  drule_all typed_dynarray_exit_path_mem >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` (qx_choose_then `h` strip_assume_tac))) >>
  `t.vs_memory = v.vs_memory` by
    (qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v`
       mp_tac >> simp[venom_state_component_equality]) >>
  qexistsl_tac [`t`, `g+h`] >>
  conj_tac >- metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- metis_tac[]) >> conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v` mp_tac >>
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
    vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED
