Theory bodyPtrPopLiteralBoundary
Ancestors bodyPtrPopSuffixSignature bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardBoundary bodyPtrPopGuardedWindow
  bodyPtrPopWindow exprLowering emitHelper compileEnv venomInst list rich_list
  context

Theorem pop_storage_blocks_unchanged:
  compile_dynarray_pop hdr 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
  sb.cs_blocks = sa.cs_blocks
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_pop_def, compile_ptr_load_def, compile_ptr_store_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem pop_guarded5_head_literal:
  ~pop_guarded5 (mk_inst id op [Lit h] outs :: xs)
Proof
  simp[pop_guarded5_def, mk_inst_def]
QED

Theorem pop_literal_guard_separation:
  a = mk_inst id op [Lit h] outs /\
  b.inst_opcode = ISZERO /\ c.inst_opcode = ISZERO /\
  d.inst_opcode = ASSERT /\ e.inst_opcode = SUB ==>
  (occurs5 pop_guarded5 (p ++ [a;b;c;d;e] ++ q) <=>
   occurs5 pop_guarded5 p \/ occurs5 pop_guarded5 q)
Proof
  strip_tac >> Induct_on `p`
  >- simp[occurs5_cons_take, pop_guarded5_head_nonload,
           pop_guarded5_head_literal] >>
  gen_tac >> simp[occurs5_cons_take] >>
  Cases_on `p`
  >- (simp[pop_guarded5_def] >> rpt strip_tac >> gvs[mk_inst_def]) >>
  namedCases_on `t` ["", "j rest"]
  >- (simp[pop_guarded5_def] >> rpt strip_tac >> gvs[mk_inst_def]) >>
  namedCases_on `rest` ["", "k rest2"]
  >- (simp[pop_guarded5_def] >> rpt strip_tac >> gvs[mk_inst_def]) >>
  namedCases_on `rest2` ["", "l rest3"]
  >- (simp[pop_guarded5_def] >> rpt strip_tac >> gvs[mk_inst_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem pop_literal_template_boundary:
  a = mk_inst id op [Lit h] outs /\
  b.inst_opcode = ISZERO /\ c.inst_opcode = ISZERO /\
  d.inst_opcode = ASSERT /\ e.inst_opcode = SUB /\
  EVERY (\i. i.inst_opcode <> ASSERT) q /\ pop_boundary_clean p ==>
  pop_boundary_clean (p ++ [a;b;c;d;e] ++ q)
Proof
  strip_tac >>
  `occurs5 pop_guarded5 (p ++ [a;b;c;d;e] ++ []) <=>
   occurs5 pop_guarded5 p \/ occurs5 pop_guarded5 []` by
    (irule pop_literal_guard_separation >> simp[] >>
     metis_tac[]) >>
  `pop_boundary_clean (p ++ [a;b;c;d;e])` by
    (simp[pop_boundary_clean_def] >> conj_tac
     >- (gvs[occurs5_short] >> metis_tac[pop_boundary_clean_windows]) >>
     `~pop_guard4 ((p ++ [a;b;c;d]) ++ [e])` by
       (irule pop_guard4_snoc_no_assert >> simp[]) >>
     pop_assum (mp_tac o SIMP_RULE std_ss [GSYM APPEND_ASSOC, APPEND]) >>
     simp[]) >>
  irule pop_boundary_clean_append_no_assert >> simp[]
QED

Theorem pop_literal_storage_boundary:
  compile_dynarray_pop (Lit h) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  pop_comp_boundary sa ==> pop_comp_boundary sb
Proof
  strip_tac >> drule pop_storage_suffix_shape >> strip_tac >>
  drule pop_storage_blocks_unchanged >> strip_tac >>
  gvs[pop_comp_boundary_def] >>
  qmatch_goalsub_abbrev_tac `pop_boundary_clean (p ++ [a;b;c;d;e;f;g;j;k])` >>
  `p ++ [a;b;c;d;e;f;g;j;k] = (p ++ [a;b;c;d;e]) ++ [f;g;j;k]` by
    simp[GSYM APPEND_ASSOC] >>
  pop_assum SUBST1_TAC >> irule pop_literal_template_boundary >>
  simp[Abbr `a`, Abbr `b`, Abbr `c`, Abbr `d`, Abbr `e`,
       Abbr `f`, Abbr `g`, Abbr `j`, Abbr `k`, Abbr `p`, mk_inst_def] >>
  Cases_on `tr` >> simp[]
QED
