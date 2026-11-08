(* Bounded finite memory-safe array iteration. *)
Theory typedArrayFiniteIterationMem
Ancestors
  typedArrayIterationPathMem fragGasPathMem context compileEnv exprLoweringProps
  venomState venomExecSemantics words arithmetic list

Theorem finite_array_path_iteration[local]:
  !remaining i s.
    i + remaining = n /\ Inv i s /\ (!j u. Inv j u ==> ~u.vs_halted) /\
    (!j u. Inv j u /\ j < n ==>
      ?v g. Inv (SUC j) v /\ gas_path_mem ctx fn u g (OK v)) ==>
    ?t g. Inv n t /\ gas_path_mem ctx fn s g (OK t)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> qexistsl_tac [`s`, `0`] >> metis_tac[gas_path_mem_rules]) >>
  `i < n` by decide_tac >>
  qpat_assum `!j u. Inv j u /\ j < n ==> _` (qspecl_then [`i`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!i s. i + remaining = n /\ _ ==> _`
    (qspecl_then [`SUC i`, `v`] mp_tac) >>
  (impl_tac >- (conj_tac >- decide_tac >> asm_rewrite_tac[])) >> strip_tac >>
  qexistsl_tac [`t`, `g+g'`] >> simp[] >>
  irule gas_path_mem_then >> qexists_tac `v` >> simp[]
QED

Theorem array_iteration_frame_trans[local]:
  (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
    vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
    vs_prev_bb := u.vs_prev_bb|>) = u /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
    vs_prev_bb := s.vs_prev_bb|>) = s ==>
  (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
    vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  simp[venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED

Theorem array_iteration_observations_trans[local]:
  mem_bytes_at a len v.vs_memory = mem_bytes_at a len u.vs_memory /\
  mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory /\
  (!p k. p+k <= b \/ hi <= p ==>
    mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
  (!p k. p+k <= b \/ hi <= p ==>
    mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
  (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x u) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  mem_bytes_at a len v.vs_memory = mem_bytes_at a len s.vs_memory /\
  (!p k. p+k <= b \/ hi <= p ==>
    mem_bytes_at p k v.vs_memory = mem_bytes_at p k s.vs_memory) /\
  (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s)
Proof
  strip_tac >> rpt conj_tac >> metis_tac[]
QED

Theorem typed_sarray_header_iteration_path_mem:
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
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) t = SOME (n2w n) /\
    (!j. j < n ==> Src j (a+ss*j) t.vs_memory) /\
    (!j. j < n ==> D j (b+ds*j) t.vs_memory) /\
    mem_bytes_at a (ss*n) t.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+ds*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Inv = \j u.
    ~u.vs_halted /\
    u.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    u.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) u = SOME (n2w j) /\
    (!k. k < n ==> Src k (a+ss*k) u.vs_memory) /\
    (!k. k < j ==> D k (b+ds*k) u.vs_memory) /\
    mem_bytes_at a (ss*n) u.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
    (!p k. p+k <= b \/ b+ds*n <= p ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)` >>
  `Inv i s` by (simp_tac bool_ss [Abbr `Inv`] >> asm_rewrite_tac[] >>
    simp[venom_state_component_equality]) >>
  `!j u. Inv j u /\ j < n ==>
     ?v g. Inv (SUC j) v /\ gas_path_mem ctx fn u g (OK v)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `Inv j u` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels` by
       (qpat_x_assum `u with <|vs_vars := _; vs_memory := _;
         vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     `eval_operand src u = SOME (n2w a) /\ eval_operand dst u = SOME (n2w b)` by
       (Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
     `a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next` by simp[] >>
     drule_all typed_sarray_header_successor_path_mem >> strip_tac >>
     qpat_x_assum `!j u. _ ==> ?v g. _` kall_tac >>
     qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
     drule_all array_iteration_observations_trans >> strip_tac >>
     qexistsl_tac [`t`, `g`] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp_tac bool_ss [] >> ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (irule array_iteration_frame_trans >> qexists_tac `u` >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  `?t g. Inv n t /\ gas_path_mem ctx fn s g (OK t)` by
    (irule finite_array_path_iteration >> conj_tac
     >- (rpt strip_tac >> gvs[Abbr `Inv`]) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`i`, `n-i`] >> simp[]) >>
  qexistsl_tac [`t`, `g`] >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `Inv n t` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  strip_tac >> first_assum ACCEPT_TAC
QED
