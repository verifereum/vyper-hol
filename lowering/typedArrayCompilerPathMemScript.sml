(* Compiler entry and exit paths for typed static-array normalization. *)
Theory typedArrayCompilerPathMem
Ancestors
  typedArrayFiniteIterationMem typedNormalizeLoop typedNormalizeContinuation typedArrayLoopPathMem
  typedArrayLoopControlMem fragGasPathMem instMemFrontier gasCount memSafeRun
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic
  emitHelperProps exprLoweringProps context compileEnv list rich_list

Theorem typed_sa_initial_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id ASSIGN [Lit 0w] [ctr]; mk_inst (id+1) JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  gas_path_mem ctx fn s 0 (OK (jump_to hdr (update_var ctr 0w s)))
Proof
  strip_tac >>
  `SUC (LENGTH prefix) - LENGTH prefix = 1` by decide_tac >>
  qabbrev_tac `u = (update_var ctr 0w s) with vs_inst_idx := SUC (LENGTH prefix)` >>
  `gas_path_mem_edge ctx fn s 0 (OK u)` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[get_instruction_def, rich_listTheory.EL_APPEND2, mk_inst_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure1_def,
       eval_operand_def, gas_count_step_def, mem_safe_step_non_invoke,
       below_frontier_no_ranges, inst_dload_in_section_def, is_terminator_def,
       Abbr `u`, update_var_def]) >>
  `gas_path_mem_edge ctx fn u 0 (OK (jump_to hdr u))` by
    (simp[gas_path_mem_edge_def, Abbr `u`, update_var_def] >> qexists_tac `0` >>
     simp[get_instruction_def, rich_listTheory.EL_APPEND2, mk_inst_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operand_def,
       gas_count_step_def, mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_def, is_terminator_def] >> metis_tac[]) >>
  `jump_to hdr u = jump_to hdr (update_var ctr 0w s)` by
    simp[Abbr `u`, jump_to_def, update_var_def] >>
  `~(jump_to hdr u).vs_halted` by simp[Abbr `u`, jump_to_def, update_var_def] >>
  metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED

Theorem typed_sarray_initial_path_mem[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) u = SOME 0w /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_sarray_child_decompose >> strip_tac >>
  map_every (fn pat => rpt (qpat_x_assum pat kall_tac))
    [`compile_store_memory_typed _ _ _ _ _ _ = _`, `sb = _`,
     `sc.cs_current_insts = _`, `cs_extends _ _`, `fn_has_code _ _ _`,
     `ci_mono _ _`, `LENGTH sc.cs_current_insts = _`, `sc.cs_next_var = _`,
     `isPREFIX _ _`] >>
  `gas_path_mem ctx fn s 0
    (OK (jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
      (update_var ("%" ++ toString sa.cs_next_var) 0w s)))` by
    (irule typed_sa_initial_path_mem >> simp[] >> conj_tac
     >- simp[typed_sa_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
     qexists_tac `sa.cs_next_id` >> simp[]) >>
  goal_assum (drule_at Any) >>
  simp[jump_to_def, update_var_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem typed_sarray_exit_path_mem[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w ncount) /\
  ncount < dimword(:256) ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_sarray_child_decompose >> strip_tac >>
  `sb.cs_current_bb = fresh_label_output "typed_sa_exit" (sa.cs_next_label+2) /\
   sb.cs_current_insts = []` by simp[] >>
  map_every (fn pat => rpt (qpat_x_assum pat kall_tac))
    [`compile_store_memory_typed _ _ _ _ _ _ = _`, `sb = _`,
     `sc.cs_current_insts = _`, `cs_extends _ _`, `fn_has_code _ _ _`,
     `ci_mono _ _`, `LENGTH sc.cs_current_insts = _`, `sc.cs_next_var = _`,
     `isPREFIX _ _`] >>
  `gas_path_mem ctx fn s 0
    (OK (jump_to (if ncount < ncount then fresh_label_output "typed_sa_body" (sa.cs_next_label+1)
              else fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
      (typed_sa_header_state ("%" ++ toString (sa.cs_next_var+1))
        ("%" ++ toString (sa.cs_next_var+2)) ncount ncount s)))` by
    (irule typed_sa_header_path_mem >> simp[] >>
     qexistsl_tac [`"%" ++ toString sa.cs_next_var`, `sa.cs_next_id+2`] >> simp[]) >>
  gvs[] >> goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``n <= n+1 /\ n <= n+2``]
QED

Theorem typed_sarray_compiler_iteration_path_mem[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
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
      (Var ("%" ++ toString (sa.cs_next_var+6))) dt
      (Var ("%" ++ toString (sa.cs_next_var+5))) st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+5)) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+6)) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) ==>
    !j u. j < n /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) u =
        SOME (n2w (a+type_memory_bytes ce st*j)) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+6))) u =
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
        (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u) /\
        LENGTH u.vs_memory <= LENGTH v.vs_memory) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    t.vs_inst_idx = 0 /\
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
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_sarray_child_decompose >> strip_tac >>
  `phi_prefix_length sc.cs_current_insts = 0` by
    simp[phi_prefix_length_def, mk_inst_def] >>
  `not_fresh_at sc ("%" ++ toString (sa.cs_next_var+5)) /\
   not_fresh_at sc ("%" ++ toString (sa.cs_next_var+6))` by
    (simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
    phi_prefix_length entry.bb_instructions = 0` by
    (drule_all normalize_typed_prefix_zero >> strip_tac >>
     goal_assum (drule_at Any) >>
     Cases_on `ec.cs_current_insts` >>
     fs[phi_prefix_length_def, typed_sa_backedge_insts_def, mk_inst_def] >>
     Cases_on `h.inst_opcode = PHI` >> fs[phi_prefix_length_def]) >>
  qpat_x_assum `!sc ec. _` (qspecl_then [`sc`, `ec`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> goal_assum (drule_at Any) >> simp[])) >>
  disch_then assume_tac >>
  irule typed_sarray_header_iteration_path_mem >>
  asm_rewrite_tac[] >>
  conj_tac >- simp[typed_sa_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
  conj_tac >- (qexists_tac `i` >> simp[]) >>
  qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `ci_mono sc ec` (irule_at Any) >>
  qpat_assum `lookup_block sc.cs_current_bb _ = SOME body_bb` (irule_at Any) >>
  qexists_tac `sa.cs_next_id+5` >>
  gvs[] >> asm_rewrite_tac[]
QED

Theorem typed_sarray_compiler_path_mem:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ n < dimword(:256) /\
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
      (Var ("%" ++ toString (sa.cs_next_var+6))) dt
      (Var ("%" ++ toString (sa.cs_next_var+5))) st sc = ((),ec) /\
    fn_has_code sc ec fn /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+5)) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+6)) /\
    phi_prefix_length sc.cs_current_insts = 0 /\
    (?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
      phi_prefix_length entry.bb_instructions = 0) ==>
    !j u. j < n /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) u =
        SOME (n2w (a+type_memory_bytes ce st*j)) /\
      eval_operand (Var ("%" ++ toString (sa.cs_next_var+6))) u =
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
        (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u) /\
        LENGTH u.vs_memory <= LENGTH v.vs_memory) ==>
  ?t g. gas_path_mem ctx fn s g (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!j. j < n ==> Src j (a+type_memory_bytes ce st*j) t.vs_memory) /\
    (!j. j < n ==> D j (b+type_memory_bytes ce dt*j) t.vs_memory) /\
    mem_bytes_at a (type_memory_bytes ce st*n) t.vs_memory =
      mem_bytes_at a (type_memory_bytes ce st*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_bytes ce dt*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!sc ec. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Callback ==> _` >> disch_tac >>
  drule_all typed_sarray_initial_path_mem >>
  disch_then (qspec_then `ctx` (qx_choose_then `u` strip_assume_tac)) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME (n2w a) /\ eval_operand dst u = SOME (n2w b)` by
    (Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `u`, `i` |-> `0:num`] typed_sarray_compiler_iteration_path_mem) >>
  (impl_tac >- (gvs[Abbr `Callback`, MULT_COMM] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v` (qx_choose_then `g` strip_assume_tac)) >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`Abbrev (Callback = _)`, `Callback`,
     `!j addr m m'. _ ==> (Src j addr m = _)`,
     `!j addr m m'. _ ==> (D j addr m = _)`,
     `!x. src = Var x \/ _ ==> _`,
     `!j. j < n ==> Src j _ s.vs_memory`] >>
  drule_all typed_sarray_exit_path_mem >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  `t.vs_memory = v.vs_memory` by
    (qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v`
       mp_tac >> simp[venom_state_component_equality]) >>
  qexistsl_tac [`t`, `g`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_mem ctx fn s 0 (OK u)` mp_tac >>
     qpat_x_assum `gas_path_mem ctx fn u g (OK v)` mp_tac >>
     qpat_x_assum `gas_path_mem ctx fn v 0 (OK t)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[gas_path_mem_then, ADD_CLAUSES]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v` mp_tac >>
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
    vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED
