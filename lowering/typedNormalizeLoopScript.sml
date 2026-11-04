Theory typedNormalizeLoop
Ancestors
  typedNormalizeFrame typedArrayLoopControlMem typedArrayLoopLayoutMem
  context compileEnv emitHelper emitHelperProps exprLoweringProps fragExec
  venomInst venomState venomExecSemantics words arithmetic list rich_list

(* Keep the recursive child's exit state opaque: its current block and all
   ncounters determine the backedge, not the enclosing body's entry state. *)
Theorem typed_sarray_child_states:
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
Theorem typed_sa_pointer_cont:
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

Theorem typed_sarray_child_decompose:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st ncount sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?sc ec.
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
  qexistsl_tac [`entry`, `ec`] >> simp[Abbr `entry`] >>
  qpat_x_assum `fn_has_code sa entry fn` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def,
       DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `fn_has_code ec sb fn` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def]
QED
