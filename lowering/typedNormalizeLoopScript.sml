Theory typedNormalizeLoop
Ancestors
  typedNormalizeFrame typedNormalizeContinuation typedArrayLoopControlMem typedArrayLoopLayoutMem memContinuation
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps fragExec
  venomInst venomState venomExecSemantics valueEncoding valueEncodingProps
  words arithmetic list rich_list

(* Keep the recursive child's exit state opaque: its current block and all
   ncounters determine the backedge, not the enclosing body's entry state. *)
Theorem typed_sarray_child_states[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  sc = sa with <|
    cs_next_var := sa.cs_next_var + 7;
    cs_next_id := sa.cs_next_id + 9;
    cs_next_label := sa.cs_next_label + 3;
    cs_current_bb := fresh_label_output "typed_sa_body" (sa.cs_next_label + 1);
    cs_current_insts :=
      [mk_inst (sa.cs_next_id+5) MUL
        [Var ("%" ++ toString sa.cs_next_var); Lit (n2w (type_memory_bytes ce st))]
        ["%" ++ toString (sa.cs_next_var+3)];
       mk_inst (sa.cs_next_id+6) MUL
        [Var ("%" ++ toString sa.cs_next_var); Lit (n2w (type_memory_bytes ce dt))]
        ["%" ++ toString (sa.cs_next_var+4)];
       mk_inst (sa.cs_next_id+7) ADD
        [src; Var ("%" ++ toString (sa.cs_next_var+3))]
        ["%" ++ toString (sa.cs_next_var+5)];
       mk_inst (sa.cs_next_id+8) ADD
        [dst; Var ("%" ++ toString (sa.cs_next_var+4))]
        ["%" ++ toString (sa.cs_next_var+6)]];
    cs_blocks :=
      <|bb_label := fresh_label_output "typed_sa_cond" sa.cs_next_label;
        bb_instructions := typed_sa_header_insts (sa.cs_next_id+2)
          ("%" ++ toString sa.cs_next_var) ("%" ++ toString (sa.cs_next_var+1))
          ("%" ++ toString (sa.cs_next_var+2)) ncount
          (fresh_label_output "typed_sa_body" (sa.cs_next_label+1))
          (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))|> ::
      <|bb_label := sa.cs_current_bb;
        bb_instructions := sa.cs_current_insts ++
          [mk_inst sa.cs_next_id ASSIGN [Lit 0w] ["%" ++ toString sa.cs_next_var];
           mk_inst (sa.cs_next_id+1) JMP
             [Label (fresh_label_output "typed_sa_cond" sa.cs_next_label)] []]|> ::
      sa.cs_blocks|> ==>
  cs_extends sa sc /\
  ?ec. compile_store_memory_typed ce
         (Var ("%" ++ toString (sa.cs_next_var+6))) dt
         (Var ("%" ++ toString (sa.cs_next_var+5))) st sc = ((),ec) /\
    cs_extends ec sb /\
    sb = ec with <|
      cs_next_var := ec.cs_next_var+1;
      cs_next_id := ec.cs_next_id+3;
      cs_current_bb := fresh_label_output "typed_sa_exit" (sa.cs_next_label+2);
      cs_current_insts := [];
      cs_blocks := <|bb_label := ec.cs_current_bb;
        bb_instructions := ec.cs_current_insts ++
          typed_sa_backedge_insts ec.cs_next_id
            ("%" ++ toString sa.cs_next_var) ("%" ++ toString ec.cs_next_var)
            (fresh_label_output "typed_sa_cond" sa.cs_next_label)|> :: ec.cs_blocks|>
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `sc = _` SUBST1_TAC >>
      simp[cs_extends_def] >>
      qmatch_goalsub_abbrev_tac `header::initial::sa.cs_blocks` >>
      qexists_tac `[header;initial]` >> simp[Abbr `initial`]) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM] >>
  qpat_x_assum `sc = _` (assume_tac o SYM) >>
  asm_simp_tac bool_ss [] >>
  simp [
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_label_def, fresh_var_def, fresh_id_def,
    emit_op_def, emit_void_def, emit_inst_def, emit_def, new_block_def, LET_THM] >>
  pairarg_tac >> simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (out,ec)` >>
  qexists_tac `ec` >>
  fs[typed_sa_header_insts_def, typed_sa_backedge_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  gvs[] >> simp[cs_extends_def] >>
  qmatch_goalsub_abbrev_tac `backedge::ec.cs_blocks` >>
  qexists_tac `[backedge]` >> simp[Abbr `backedge`]
QED

(* The entry arithmetic is independent of both element layouts and the
   recursive child's CFG.  Only its four fresh result registers change. *)
Theorem typed_sa_pointer_cont[local]:
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
  ?u. mem_cont_sim ctx fn s u /\ u.vs_inst_idx = 4 /\
    eval_operand (Var sp) u = SOME (n2w (source_base + src_stride*i)) /\
    eval_operand (Var dp) u = SOME (n2w (dest_base + dst_stride*i)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. ~MEM x [so;dso;sp;dp] ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_sa_pointer_run >>
  disch_then (qspecl_then [`src_stride`, `id`, `dst_stride`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexists_tac `q with vs_inst_idx := 4` >> conj_tac
  >- (`LENGTH code = 4` by simp[] >>
      qpat_x_assum `LENGTH code = 4` (fn th => once_rewrite_tac [GSYM th]) >>
      `EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode) code` by
        simp[mk_inst_def, is_terminator_def] >>
      irule typed_array_prefix_cont >> metis_tac[]) >>
  fs[venom_state_component_equality, eval_operand_def, lookup_var_def]
QED

Theorem typed_sarray_child_decompose[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?sc ec body_bb.
    lookup_block sc.cs_current_bb fn.fn_blocks = SOME body_bb /\
    isPREFIX sc.cs_current_insts body_bb.bb_instructions /\
    phi_prefix_length body_bb.bb_instructions = 0 /\
    compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+6))) dt
      (Var ("%" ++ toString (sa.cs_next_var+5))) st sc = ((),ec) /\
    cs_extends sa sc /\ cs_extends ec sb /\ fn_has_code sc ec fn /\
    fn_has_code sa sc fn /\ fn_has_code ec sb fn /\ ci_mono sc ec /\
    lookup_block ec.cs_current_bb fn.fn_blocks =
      SOME <|bb_label := ec.cs_current_bb;
        bb_instructions := ec.cs_current_insts ++
          typed_sa_backedge_insts ec.cs_next_id
            ("%" ++ toString sa.cs_next_var) ("%" ++ toString ec.cs_next_var)
            (fresh_label_output "typed_sa_cond" sa.cs_next_label)|> /\
    sb = ec with <|
      cs_next_var := ec.cs_next_var+1;
      cs_next_id := ec.cs_next_id+3;
      cs_current_bb := fresh_label_output "typed_sa_exit" (sa.cs_next_label+2);
      cs_current_insts := [];
      cs_blocks := <|bb_label := ec.cs_current_bb;
        bb_instructions := ec.cs_current_insts ++
          typed_sa_backedge_insts ec.cs_next_id
            ("%" ++ toString sa.cs_next_var) ("%" ++ toString ec.cs_next_var)
            (fresh_label_output "typed_sa_cond" sa.cs_next_label)|> :: ec.cs_blocks|> /\
    sc.cs_current_insts =
      [mk_inst (sa.cs_next_id+5) MUL
        [Var ("%" ++ toString sa.cs_next_var); Lit (n2w (type_memory_bytes ce st))]
        ["%" ++ toString (sa.cs_next_var+3)];
       mk_inst (sa.cs_next_id+6) MUL
        [Var ("%" ++ toString sa.cs_next_var); Lit (n2w (type_memory_bytes ce dt))]
        ["%" ++ toString (sa.cs_next_var+4)];
       mk_inst (sa.cs_next_id+7) ADD
        [src; Var ("%" ++ toString (sa.cs_next_var+3))]
        ["%" ++ toString (sa.cs_next_var+5)];
       mk_inst (sa.cs_next_id+8) ADD
        [dst; Var ("%" ++ toString (sa.cs_next_var+4))]
        ["%" ++ toString (sa.cs_next_var+6)]] /\
    lookup_block (fresh_label_output "typed_sa_cond" sa.cs_next_label) fn.fn_blocks =
      SOME <|bb_label := fresh_label_output "typed_sa_cond" sa.cs_next_label;
        bb_instructions := typed_sa_header_insts (sa.cs_next_id+2)
          ("%" ++ toString sa.cs_next_var) ("%" ++ toString (sa.cs_next_var+1))
          ("%" ++ toString (sa.cs_next_var+2)) ncount
          (fresh_label_output "typed_sa_body" (sa.cs_next_label+1))
          (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))|> /\
    lookup_block sa.cs_current_bb fn.fn_blocks =
      SOME <|bb_label := sa.cs_current_bb;
        bb_instructions := sa.cs_current_insts ++
          [mk_inst sa.cs_next_id ASSIGN [Lit 0w] ["%" ++ toString sa.cs_next_var];
           mk_inst (sa.cs_next_id+1) JMP
             [Label (fresh_label_output "typed_sa_cond" sa.cs_next_label)] []]|> /\
    sc.cs_next_var = sa.cs_next_var+7 /\
    sc.cs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
    LENGTH sc.cs_current_insts = 4
Proof
  strip_tac >> drule_at Any typed_sarray_child_states >>
  asm_simp_tac bool_ss [] >>
  qmatch_goalsub_abbrev_tac `cs_extends sa entry` >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `ci_mono entry ec` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     metis_tac[CONJUNCT1 ci_mono_typed_memory_family, pairTheory.SND]) >>
  `fn_has_code entry ec fn` by
    (irule fn_has_code_mid >> conj_tac
     >- fs[ci_mono_def] >>
     qexistsl_tac [`sb`, `sa`] >> simp[]) >>
  `cs_extends entry ec` by fs[ci_mono_def] >>
  `cs_extends entry sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa entry fn /\ fn_has_code ec sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `?body_bb. lookup_block entry.cs_current_bb fn.fn_blocks = SOME body_bb /\
    isPREFIX entry.cs_current_insts body_bb.bb_instructions` by
    (irule fn_has_code_start >> qexists_tac `ec` >> simp[]) >>
  `phi_prefix_length body_bb.bb_instructions = 0` by
    (qpat_x_assum `isPREFIX entry.cs_current_insts _` mp_tac >>
     Cases_on `body_bb.bb_instructions` >>
     simp[Abbr `entry`] >> strip_tac >>
     gvs[phi_prefix_length_def, mk_inst_def]) >>
  qexistsl_tac [`entry`, `ec`, `body_bb`] >> simp[Abbr `entry`] >>
  qpat_x_assum `fn_has_code sa entry fn` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def,
       DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `fn_has_code ec sb fn` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def]
QED

(* A child overwrites only its own destination slot.  Memory locality, not
   recursive knowledge of the enclosing prefix, transports earlier slots. *)
Theorem typed_sarray_emits_blocks:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  fn_has_code sa sb fn ==> emitted_blocks sa sb <> []
Proof
  strip_tac >> drule_all typed_sarray_child_decompose >> strip_tac >>
  `cs_extends sa ec` by
    (irule cs_extends_trans >> qexists_tac `sc` >> simp[] >>
     fs[ci_mono_def]) >>
  qpat_x_assum `cs_extends sa ec` mp_tac >>
  qpat_x_assum `sb = _` SUBST1_TAC >>
  simp_tac (srw_ss()) [cs_extends_def, emitted_blocks_def] >>
  strip_tac >> gvs[LENGTH_APPEND] >> decide_tac
QED

Theorem typed_array_local_prefix_step[local]:
  (!j a m m'. j < n /\ mem_bytes_at a stride m = mem_bytes_at a stride m' ==>
    (D j a m <=> D j a m')) /\
  (!j. j < i ==> D j ((addr:num)+stride*j) mem) /\
  D i (addr+stride*i) mem' /\ i < n /\
  (!a k. a+k <= addr+stride*i \/ addr+stride*i+stride <= a ==>
    mem_bytes_at a k mem' = mem_bytes_at a k mem) ==>
  !j. j < SUC i ==> D j (addr+stride*j) mem'
Proof
  rpt strip_tac >> Cases_on `j = i` >- gvs[] >>
  `j < i /\ j < n` by decide_tac >>
  `stride * (j+1) <= stride*i` by simp[LE_MULT_LCANCEL] >>
  `addr + stride*j + stride <= addr + stride*i` by
    (qpat_x_assum `stride * (j+1) <= stride*i` mp_tac >>
     pure_rewrite_tac [LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  `mem_bytes_at (addr+stride*j) stride mem' =
    mem_bytes_at (addr+stride*j) stride mem` by metis_tac[] >>
  metis_tac[]
QED

Theorem typed_array_local_source_frame[local]:
  (!j a m m'. j < n /\ mem_bytes_at a stride m = mem_bytes_at a stride m' ==>
    (Src j a m <=> Src j a m')) /\
  (!j. j < n ==> Src j (addr+stride*j) mem) /\
  mem_bytes_at addr (stride*n) mem' = mem_bytes_at addr (stride*n) mem ==>
  !j. j < n ==> Src j (addr+stride*j) mem'
Proof
  rpt strip_tac >>
  `stride * (j+1) <= stride*n` by simp[LE_MULT_LCANCEL] >>
  `stride*j + stride <= stride*n` by
    (qpat_x_assum `stride * (j+1) <= stride*n` mp_tac >>
     pure_rewrite_tac [LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  `mem_bytes_at (addr+stride*j) stride mem' =
    mem_bytes_at (addr+stride*j) stride mem` by
    (irule mem_bytes_at_translated_window >>
     qexists_tac `stride*n` >> simp[]) >>
  metis_tac[]
QED

Theorem typed_array_child_exterior[local]:
  i < n /\ (a+ss*n <= b \/ b+ds*n <= a) /\
  (!p k. p+k <= b+ds*i \/ b+ds*i+ds <= p ==>
    mem_bytes_at p k mem' = mem_bytes_at p k mem) ==>
  mem_bytes_at a (ss*n) mem' = mem_bytes_at a (ss*n) mem /\
  (!p k. p+k <= b \/ b+ds*n <= p ==>
    mem_bytes_at p k mem' = mem_bytes_at p k mem)
Proof
  strip_tac >>
  `ds * (i+1) <= ds*n` by simp[LE_MULT_LCANCEL] >>
  `b+ds*i+ds <= b+ds*n` by
    (qpat_x_assum `ds * (i+1) <= ds*n` mp_tac >>
     pure_rewrite_tac [LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  conj_tac >- (first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

(* The enclosing loop, rather than the element callback, executes the
   conditional edge.  This boundary is valid for arbitrary element types. *)
Theorem typed_sarray_header_cont[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) ==>
  ?u. mem_cont_sim ctx fn s u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
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
  `mem_cont_sim ctx fn s
    (jump_to (if i < ncount then fresh_label_output "typed_sa_body" (sa.cs_next_label+1)
              else fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
      (typed_sa_header_state ("%" ++ toString (sa.cs_next_var+1))
        ("%" ++ toString (sa.cs_next_var+2)) i ncount s))` by
    (irule typed_sa_header_sim >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`"%" ++ toString sa.cs_next_var`, `sa.cs_next_id+2`] >>
     simp[] >> metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  gvs[] >> goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``n <= n+1 /\ n <= n+2``]
QED

Theorem typed_sarray_exit_cont[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w ncount) /\
  ncount < dimword(:256) /\
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 ==>
  ?u. mem_cont_sim ctx fn s u /\ ~u.vs_halted /\
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
  `mem_cont_sim ctx fn s
    (jump_to (if ncount < ncount then fresh_label_output "typed_sa_body" (sa.cs_next_label+1)
              else fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
      (typed_sa_header_state ("%" ++ toString (sa.cs_next_var+1))
        ("%" ++ toString (sa.cs_next_var+2)) ncount ncount s))` by
    (irule typed_sa_header_sim >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`"%" ++ toString sa.cs_next_var`, `sa.cs_next_id+2`] >> simp[]) >>
  gvs[] >> goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``n <= n+1 /\ n <= n+2``]
QED

(* Only the recursive element copy is delegated.  The four enclosing pointer
   instructions execute here even when the child crosses arbitrary blocks. *)
Theorem typed_array_pointer_child_cont[local]:
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
    ?v. mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\
      D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?v. mem_cont_sim ctx fn s v /\ ~v.vs_halted /\
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
  `?u. mem_cont_sim ctx fn s u /\ u.vs_inst_idx = 4 /\
    eval_operand (Var sp) u = SOME (n2w (a+ss*i)) /\
    eval_operand (Var dp) u = SOME (n2w (b+ds*i)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. ~MEM x [so;dso;sp;dp] ==> lookup_var x u = lookup_var x s)` by
    (irule typed_sa_pointer_cont >> simp[] >>
     qexistsl_tac [`ctr`, `dst`, `id`, `src`] >> gvs[] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qpat_x_assum `!j u. _` (qspecl_then [`i`, `u`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >> qexists_tac `v` >>
  conj_tac >- (irule mem_cont_sim_trans >> qexists_tac `u` >> simp[]) >>
  simp[] >> conj_tac
  >- (gvs[eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

(* The returned child state, not its entry, chooses the backedge instruction
   IDs and temporary.  The counter update has no memory effect. *)
Theorem typed_array_child_backedge_cont[local]:
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
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) t = SOME (n2w (SUC i)) /\
    (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `mem_cont_sim ctx fn s
    (jump_to hdr (typed_sa_backedge_state ("%" ++ toString sa.cs_next_var)
      ("%" ++ toString ec.cs_next_var) i s))` by
    (irule typed_sa_backedge_sim >> simp[] >>
     conj_tac >- (qexists_tac `n` >> simp[]) >>
     qexistsl_tac [`ec.cs_next_id`, `ec.cs_current_insts`] >> simp[]) >>
  goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_backedge_state_def, update_var_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[LESS_EQ_TRANS, LESS_EQ_REFL]
QED

Theorem typed_sarray_pointer_fresh[local]:
  sc.cs_next_var = sa.cs_next_var+7 /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  let ctr = "%" ++ toString sa.cs_next_var;
      so = "%" ++ toString (sa.cs_next_var+3);
      dso = "%" ++ toString (sa.cs_next_var+4);
      sp = "%" ++ toString (sa.cs_next_var+5);
      dp = "%" ++ toString (sa.cs_next_var+6)
  in ALL_DISTINCT [so;dso;sp;dp] /\ ~MEM ctr [so;dso;sp;dp] /\
    not_fresh_at sc ctr /\
    (!x. src = Var x \/ dst = Var x ==> ~MEM x [so;dso;sp;dp]) /\
    (!x. not_fresh_at sa x ==> not_fresh_at sc x /\ ~MEM x [so;dso;sp;dp])
Proof
  simp[LET_THM] >> strip_tac >>
  simp[ASCIInumbersTheory.toString_inj, not_fresh_at_def]
  >- (rpt strip_tac >> `not_fresh_at sa x` by metis_tac[] >>
      gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``n <= n+3 /\ n <= n+4 /\ n <= n+5 /\ n <= n+6 /\ n <= n+7``]
QED


Theorem typed_sarray_body_successor:
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
    ?v. mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
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
  drule_all typed_array_pointer_child_cont >> strip_tac >>
  qpat_x_assum `!j u. _ ==> ?v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  qpat_x_assum `isPREFIX _ _` kall_tac >>
  `sa.cs_next_var <= ec.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  drule_all typed_array_child_backedge_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "body_finish"
QED

Resume typed_sarray_body_successor[body_finish]:

  `t.vs_memory = v.vs_memory` by
    (qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _;
      vs_inst_idx := _; vs_prev_bb := _|> = v` mp_tac >>
     simp[venom_state_component_equality]) >>
  `mem_bytes_at a (ss*n) v.vs_memory = mem_bytes_at a (ss*n) s.vs_memory /\
   (!p k. p+k <= b \/ b+ds*n <= p ==>
     mem_bytes_at p k v.vs_memory = mem_bytes_at p k s.vs_memory)` by
    (irule typed_array_child_exterior >> reverse conj_tac
     >- first_assum ACCEPT_TAC >> qexists_tac `i` >> asm_rewrite_tac[]) >>
  qexists_tac `t` >>
  conj_tac >- (irule mem_cont_sim_trans >> qexists_tac `v` >> simp[]) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "body_memory"
QED
Resume typed_sarray_body_successor[body_memory]:
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
Finalise typed_sarray_body_successor

(* Header-to-header step.  The recursive callback still owns only the child. *)
Theorem typed_sarray_header_successor[local]:
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
    ?v. mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
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
  drule_all typed_sarray_header_cont >>
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
  suspend "header_body"
QED
Resume typed_sarray_header_successor[header_body]:
  `u.vs_current_bb = sc.cs_current_bb /\
   a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next /\
   (!j. j < n ==> Src j (a+ss*j) u.vs_memory) /\
   (!j. j < i ==> D j (b+ds*j) u.vs_memory)` by
    (asm_rewrite_tac[]) >>
  drule_all typed_sarray_body_successor >> strip_tac >>
  qpat_x_assum `!j u. _ ==> ?v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  suspend "header_finish"
QED
Resume typed_sarray_header_successor[header_finish]:
  qexists_tac `t` >>
  conj_tac >- (irule mem_cont_sim_trans >> qexists_tac `u` >> simp[]) >>
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
  rpt strip_tac >>
  `lookup_var x t = lookup_var x u` by metis_tac[] >>
  `lookup_var x u = lookup_var x s` by metis_tac[] >> simp[]
QED
Finalise typed_sarray_header_successor

Theorem typed_sarray_header_iteration[local]:
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
    ?v. mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
      v.vs_current_bb = ec.cs_current_bb /\
      v.vs_inst_idx = LENGTH ec.cs_current_insts /\ D j (b+ds*j) v.vs_memory /\
      (!p k. p+k <= b+ds*j \/ b+ds*j+ds <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := sc.cs_current_bb; vs_inst_idx := LENGTH sc.cs_current_insts;
        vs_prev_bb := u.vs_prev_bb|>) = u /\
      (!x. not_fresh_at sc x ==> lookup_var x v = lookup_var x u)) ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
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
  `Inv i s` by
    (simp_tac bool_ss [Abbr `Inv`] >> asm_rewrite_tac[] >>
     simp[venom_state_component_equality]) >>
  `!j u. Inv j u /\ j < n ==>
     ?v. Inv (SUC j) v /\ mem_cont_sim ctx fn u v` by
    (suspend "iteration_step") >>
  `?t. Inv n t /\ mem_cont_sim ctx fn s t` by
    (irule mem_cont_sim_finite_iteration >>
     qexistsl_tac [`n`, `i`, `Inv`] >> simp[] >>
     metis_tac[mem_cont_sim_refl]) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `Inv n t` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  strip_tac >> first_assum ACCEPT_TAC
QED
Resume typed_sarray_header_iteration[iteration_step]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Inv j u` mp_tac >> simp_tac bool_ss [Abbr `Inv`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _;
      vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME (n2w a) /\ eval_operand dst u = SOME (n2w b)` by
    (qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` mp_tac >>
     qpat_x_assum `!x. src = Var x \/ _ ==> _` mp_tac >>
     qpat_x_assum `eval_operand src s = _` mp_tac >>
     qpat_x_assum `eval_operand dst s = _` mp_tac >>
     qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  `a+ss*n <= u.vs_alloca_next /\ b+ds*n <= u.vs_alloca_next` by simp[] >>
  drule_all typed_sarray_header_successor >> strip_tac >>
  qpat_x_assum `!j u. _ ==> ?v. _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  suspend "iteration_frame"
QED
Resume typed_sarray_header_iteration[iteration_frame]:
  qexists_tac `t` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
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
Finalise typed_sarray_header_iteration

Theorem typed_sarray_initial_cont[local]:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. mem_cont_sim ctx fn s u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
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
  `mem_cont_sim ctx fn s
    (jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
      (update_var ("%" ++ toString sa.cs_next_var) 0w s))` by
    (irule typed_sa_initial_sim >> simp[] >> conj_tac
     >- simp[typed_sa_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
     qexists_tac `sa.cs_next_id` >> simp[]) >>
  goal_assum (drule_at Any) >>
  simp[jump_to_def, update_var_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED


(* Compiler-facing loop interface: concrete states and instruction IDs stay local. *)
Theorem typed_sarray_compiler_iteration:
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
      ?v. mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
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
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
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
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
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
  `!k:num. (k+5)+1 = k+6 /\ (k+5)+2 = k+7 /\ (k+5)+3 = k+8` by decide_tac >>
  qpat_x_assum `!k:num. _` (fn offsets =>
    mp_tac (SIMP_RULE (pure_ss ++ numSimps.REDUCE_ss) [offsets]
      (Q.INST [`ss` |-> `type_memory_bytes ce st`,
               `ds` |-> `type_memory_bytes ce dt`,
               `id` |-> `sa.cs_next_id+5`,
               `header_bb` |->
                 `<|bb_label := fresh_label_output "typed_sa_cond" sa.cs_next_label;
                    bb_instructions := typed_sa_header_insts (sa.cs_next_id+2)
                      ("%" ++ toString sa.cs_next_var) ("%" ++ toString (sa.cs_next_var+1))
                      ("%" ++ toString (sa.cs_next_var+2)) n
                      (fresh_label_output "typed_sa_body" (sa.cs_next_label+1))
                      (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))|>`]
        typed_sarray_header_iteration))) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    gvs[typed_sa_header_insts_def, phi_prefix_length_def, mk_inst_def])) >>
  disch_then ACCEPT_TAC
QED

(* Full static-array copy: unlike iteration, this reaches the compiler endpoint. *)
Theorem typed_sarray_compiler_cont:
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
  lookup_block sb.cs_current_bb fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
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
      ?v. mem_cont_sim ctx fn u v /\ ~v.vs_halted /\
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
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
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
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!sc ec. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `Callback ==> _` >> disch_tac >>
  drule_all typed_sarray_initial_cont >>
  disch_then (qspec_then `ctx` (qx_choose_then `u` strip_assume_tac)) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME (n2w a) /\ eval_operand dst u = SOME (n2w b)` by
    (qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` mp_tac >>
     qpat_x_assum `!x. src = Var x \/ _ ==> _` mp_tac >>
     qpat_x_assum `eval_operand src s = _` mp_tac >>
     qpat_x_assum `eval_operand dst s = _` mp_tac >>
     qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `src` >> Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  suspend "iterate"
QED
Resume typed_sarray_compiler_cont[iterate]:
  mp_tac (Q.INST [`s` |-> `u`, `i` |-> `0:num`] typed_sarray_compiler_iteration) >>
  (impl_tac >- (gvs[Abbr `Callback`, MULT_COMM] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  suspend "exit"
QED
Resume typed_sarray_compiler_cont[exit]:
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`Abbrev (Callback = _)`, `Callback`,
     `!j addr m m'. _ ==> (Src j addr m = _)`,
     `!j addr m m'. _ ==> (D j addr m = _)`,
     `!x. src = Var x \/ _ ==> _`,
     `!j. j < n ==> Src j _ s.vs_memory`] >>
  drule_all typed_sarray_exit_cont >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  `t.vs_memory = v.vs_memory` by
    (qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v`
       mp_tac >> simp[venom_state_component_equality]) >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[mem_cont_sim_trans] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  suspend "frame"
QED
Resume typed_sarray_compiler_cont[frame]:
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `t with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = v` mp_tac >>
  qpat_x_assum `v with <|vs_vars := _; vs_memory := _;
    vs_current_bb := _; vs_inst_idx := _; vs_prev_bb := _|> = u` mp_tac >>
  qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _;
    vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[]
QED
Finalise typed_sarray_compiler_cont
