(* Generated fixed-array loop placement and register cutoff. *)
Theory typedCopyLoopPlacementMemory
Ancestors typedCopyLoopLayoutPtr typedCopyArrayLoopMemory typedCopyBodyFrame
  exprOperandVar compileEnv ASCIInumbers arithmetic list exprLoweringProps

Theorem typed_copy_loop_register_freshness[local]:
  sc.cs_next_var = sa.cs_next_var + 1 /\
  sa.cs_next_var + 7 <= se.cs_next_var /\
  ctr = "%" ++ toString sa.cs_next_var /\
  lt = "%" ++ toString (sa.cs_next_var + 1) /\
  done = "%" ++ toString (sa.cs_next_var + 2) /\
  so = "%" ++ toString (sa.cs_next_var + 3) /\
  doff = "%" ++ toString (sa.cs_next_var + 4) /\
  sp = "%" ++ toString (sa.cs_next_var + 5) /\
  dp = "%" ++ toString (sa.cs_next_var + 6) /\
  tmp = "%" ++ toString se.cs_next_var ==>
  not_fresh_at sc ctr /\ ~not_fresh_at sa ctr /\
  ~not_fresh_at sa tmp /\ ctr <> tmp /\
  (!x. MEM x [lt; done; so; doff; sp; dp] ==> ~not_fresh_at sc x) /\
  ALL_DISTINCT [ctr; so; doff; sp; dp]
Proof
  strip_tac >> gvs[not_fresh_at_def, toString_inj] >>
  rpt conj_tac >> simp[] >> rpt strip_tac >> gvs[] >>
  simp[toString_inj]
QED

Theorem typed_copy_sarray_loop_placement:
  !ce dst dty src sty count sa sz func.
  ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
    ~is_abi_dynamic ce.ce_struct_fields dty) /\
  compile_copy_sarray_typed ce dst dty src sty count sa = ((),sz) /\
  fn_has_code sa sz func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  ?sc si se header body exit ctr lt done so doff sp dp test bb back.
    header = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    ctr = "%" ++ toString sa.cs_next_var /\
    compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) /\
    fn_has_code si se func /\
    not_fresh_at si sp /\ not_fresh_at si dp /\
    ci_mono sa sc /\ ci_mono sc si /\
    not_fresh_at sc ctr /\ ~not_fresh_at sa ctr /\
    ~not_fresh_at sa ("%" ++ toString se.cs_next_var) /\
    ctr <> "%" ++ toString se.cs_next_var /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sc x) /\
    (!x. MEM x [lt; done; so; doff; sp; dp] ==> ~not_fresh_at sc x) /\
    ALL_DISTINCT [ctr; so; doff; sp; dp] /\
    lookup_block header func.fn_blocks = SOME test /\
    test.bb_instructions =
      [mk_inst sc.cs_next_id LT [Var ctr; Lit (n2w count)] [lt];
       mk_inst (sc.cs_next_id+1) ISZERO [Var lt] [done];
       mk_inst (sc.cs_next_id+2) JNZ [Var done; Label exit; Label body] []] /\
    lookup_block body func.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst (sc.cs_next_id+3) MUL
         [Var ctr; Lit (n2w (type_memory_bytes ce sty))] [so];
       mk_inst (sc.cs_next_id+4) MUL
         [Var ctr; Lit (n2w (type_memory_bytes ce dty))] [doff];
       mk_inst (sc.cs_next_id+5) ADD [src; Var so] [sp];
       mk_inst (sc.cs_next_id+6) ADD [dst; Var doff] [dp]] bb.bb_instructions /\
    si.cs_current_bb = body /\ LENGTH si.cs_current_insts = 4 /\
    lookup_block se.cs_current_bb func.fn_blocks = SOME back /\
    back.bb_instructions = se.cs_current_insts ++
      [mk_inst se.cs_next_id ADD [Var ctr; Lit 1w]
         ["%" ++ toString se.cs_next_var];
       mk_inst (se.cs_next_id+1) ASSIGN
         [Var ("%" ++ toString se.cs_next_var)] [ctr];
       mk_inst (se.cs_next_id+2) JMP [Label header] []] /\
    sz.cs_current_bb = exit /\ sz.cs_current_insts = []
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    typed_copy_loop_slice_locations >>
  disch_then (qspecl_then [`sa`, `sz`] mp_tac) >>
  disch_then (qspecl_then
    [`HD sc.cs_blocks`, `HD sb.cs_blocks`, `HD sz.cs_blocks`] mp_tac) >>
  disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `ci_mono sa sc` by
    (simp[ci_mono_def, cs_extends_def] >>
     qexists_tac `[HD sc.cs_blocks]` >> simp[]) >>
  `not_fresh_at si sp /\ not_fresh_at si dp` by
    simp[not_fresh_at_def, toString_inj] >>
  `sc.cs_current_bb = cond /\ sc.cs_current_insts = []` by simp[] >>
  `ci_mono sc si` by
    (qpat_x_assum `sc = _` kall_tac >>
     simp[ci_mono_def, cs_extends_def]) >>
  `ci_mono si se` by
    (qspec_then `ce` mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`Var dp`, `dty`, `Var sp`, `sty`, `si`] mp_tac) >>
     asm_rewrite_tac[] >> simp[]) >>
  `sa.cs_next_var + 7 <= se.cs_next_var` by
    (qpat_x_assum `ci_mono si se` mp_tac >>
     simp[ci_mono_def]) >>
  `not_fresh_at sc ctr /\ ~not_fresh_at sa ctr /\
   ~not_fresh_at sa ("%" ++ toString se.cs_next_var) /\
   ctr <> "%" ++ toString se.cs_next_var /\
   (!x. MEM x [lt; done; so; doff; sp; dp] ==> ~not_fresh_at sc x) /\
   ALL_DISTINCT [ctr; so; doff; sp; dp]` by
    (irule typed_copy_loop_register_freshness >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`sc`, `si`, `se`, `cond`, `body'`, `exit`,
    `ctr`, `lt`, `done`, `so`, `doff`, `sp`, `dp`,
    `HD sb.cs_blocks`, `bb`, `HD sz.cs_blocks`] >>
  rpt conj_tac >> simp[]
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  gvs[]
QED
