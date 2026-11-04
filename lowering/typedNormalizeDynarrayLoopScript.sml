Theory typedNormalizeDynarrayLoop
Ancestors
  typedNormalizeDynarray typedArrayBoundControlMem typedArrayLoopLayoutMem typedArrayLoopControlMem
  context compileEnv emitHelper emitHelperProps exprLoweringProps fragExec
  venomInst venomState venomExecSemantics words arithmetic list rich_list

(* The recursive child is opaque; its returned counters determine the backedge. *)
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

(* Code certificates for the opaque child's entry and its returned backedge. *)
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

(* Align the accepted seven-op prologue with the actual loop's child state. *)
Theorem typed_dynarray_prefix_child:
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\ ci_mono sa sc /\ ci_mono sc sb /\
  sc.cs_blocks = header :: initial :: sa.cs_blocks /\
  lookup_block sa.cs_current_bb fn.fn_blocks = SOME initial /\
  initial.bb_label = sa.cs_current_bb /\
  sa.cs_next_var+5 <= sc.cs_next_var /\
  sa.cs_next_id+7 <= sc.cs_next_id ==>
  ?sm. sm.cs_current_bb = sa.cs_current_bb /\
    LENGTH sm.cs_current_insts = LENGTH sa.cs_current_insts+7 /\
    sm.cs_blocks = sa.cs_blocks /\ sm.cs_next_label = sa.cs_next_label /\
    sm.cs_next_var = sa.cs_next_var+5 /\ sm.cs_next_id = sa.cs_next_id+7 /\
    isPREFIX sm.cs_current_insts initial.bb_instructions /\
    ci_mono sa sm /\ ci_mono sm sc /\ ci_mono sm sb /\
    fn_has_code sa sm fn /\ fn_has_code sm sc fn
Proof
  strip_tac >> drule_all typed_dynarray_compiler_prefix >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `isPREFIX sm.cs_current_insts initial.bb_instructions` by
    (qpat_x_assum `fn_has_code sa sm fn` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >> gvs[]) >>
  `ci_mono sm sc` by
    (gvs[ci_mono_def, cs_extends_def]) >>
  `fn_has_code sm sc fn` by
    (irule fn_has_code_mid >>
     conj_tac >- fs[ci_mono_def] >>
     qexistsl_tac [`sb`, `sa`] >> fs[ci_mono_def]) >>
  qexists_tac `sm` >> simp[]
QED
