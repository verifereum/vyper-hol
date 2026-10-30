(*
 * Staging a tuple for unpacking: where the tuple lies, the sizes of its
 * elements, and the optional MCOPY into a fresh buffer.
 *
 * TOP-LEVEL:
 *   tuple_element_sizes, tuple_memory_size_positive — element sizes
 *   optional_tuple_stage_code, optional_tuple_stage_run — the staging copy
 *   type_memory_bytes_tuple_list — a tuple type's size from its elements'
 *)
Theory tupleStageProps
Ancestors
  stmtSimDeclMem valueCopyBytes stmtSimReturn tupleMemoryLayout exprSim valueTypingMemoryProps
  list rich_list finite_map compileEnv valueEncoding vyperTyping
  loweringHalt context emitHelper emitHelperProps exprLoweringProps freshWrites
  loweringSlice fragExec localPtrsProps venomInst venomState venomExecSemantics
Libs
  monadsyntax

Theorem expr_tuple_memory_owned:
  !cenv cx tys tvs vs sa sb es op s w.
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) sa sb es (ArrayV (TupleV vs)) op s /\
    eval_operand op s = SOME w /\
    0 < type_memory_size_list tvs ==>
    tuple_in_memory vs tvs (w2n w) s.vs_memory /\
    tuple_val_wf vs tvs /\
    ?b sz. b <= w2n w /\
      w2n w + type_memory_size_list tvs <= b + sz /\
      ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
       (?name. local_region cenv es.scopes s name b sz))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_val_rel_def, expr_val_at_def, is_word_type_def,
      val_footprint_def, type_memory_size_def, val_in_memory_def, val_wf_def] >>
  metis_tac[]
QED

Theorem tuple_element_sizes:
  !tys tvs tenv cenv.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
         type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs)) ==>
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs
Proof
  rpt gen_tac >> strip_tac >>
  simp[LIST_REL_EL_EQN] >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >> simp[] >>
  qx_gen_tac `i` >> strip_tac >> Cases_on `is_word_type (EL i tys)`
  >- (drule (iffLR LIST_REL_EL_EQN) >> strip_tac >>
      first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
      strip_tac >> drule_all word_type_sizes >>
      disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem compatible_memory_type_positive:
  !tenv t tv vt vtv.
    evaluate_type tenv t = SOME tv /\
    evaluate_type tenv vt = SOME vtv /\ 0 < type_memory_size vtv /\
    (vt = t \/ is_bytestring_type vt /\ is_bytestring_type t) ==>
    0 < type_memory_size tv
Proof
  rpt gen_tac >> strip_tac
  >- gvs[] >>
  drule_all bytestring_type_value >> strip_tac >>
  simp[type_memory_size_def]
QED

Theorem tuple_memory_size_positive:
  !tys tvs tenv.
    tys <> [] /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) tys tvs /\
    (!i. i < LENGTH tys ==> is_word_type (EL i tys) \/
      ?vt vtv. evaluate_type tenv vt = SOME vtv /\
        0 < type_memory_size vtv /\
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys))) ==>
    0 < type_memory_size_list tvs
Proof
  Cases_on `tys` >> simp[] >> Cases_on `tvs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `evaluate_type tenv ht = SOME htv` >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac
  >- (drule_all word_type_sizes >>
      disch_then (qspec_then `ARB` strip_assume_tac) >>
      simp[type_memory_size_def]) >>
  `0 < type_memory_size htv` by
    (irule compatible_memory_type_positive >> goal_assum drule >> metis_tac[]) >>
  simp[type_memory_size_def]
QED

Theorem tuple_stage_copy_parts:
  !sz op sa staged sb func.
    (do buf <- compile_alloc_buffer sz;
        emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    fn_has_code sa sb func ==>
    ?sx sm p.
      sx = sa with cs_next_var := sa.cs_next_var + 1 /\
      staged = Var p /\ ~not_fresh_at sa p /\ not_fresh_at sb p /\
      emit_inst ALLOCA [Lit (n2w sz)] [p] sx = ((),sm) /\
      emit_void MCOPY [Var p; op; Lit (n2w sz)] sm = ((),sb) /\
      cs_extends sa sx /\ cs_extends sx sm /\ cs_extends sm sb /\
      fn_has_code sx sm func /\ fn_has_code sm sb func
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(do _ od) sa = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_alloc_buffer sz sa` >>
  rename1 `compile_alloc_buffer sz sa = (buf,sm)` >>
  Cases_on `emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)] sm` >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_void MCOPY _ sm = ((),sb)` >>
  drule compile_alloc_buffer_emission >>
  disch_then (qx_choosel_then [`sx`, `p`] strip_assume_tac) >>
  `cs_extends sm sb` by
    metis_tac[cs_appends_def, cs_appends_emit_helpers] >>
  `sm.cs_next_var = sb.cs_next_var` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_def, fresh_id_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  `cs_extends sx sb` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code sx sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  qexistsl [`sm`, `p`] >>
  simp[] >> conj_tac
  >- (irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  metis_tac[]
QED

Theorem tuple_stage_copy_run:
  !ctx func cenv cx es sa sb staged op s sw sz tv v.
    (do buf <- compile_alloc_buffer sz;
        emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    eval_operand op s = SOME sw /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\ sz < dimword (:256) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. eval_operand staged t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      stmt_state_rel func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt strip_tac >> drule_all tuple_stage_copy_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `p`] strip_assume_tac) >>
  `MEM (mk_inst sx.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by
    (irule emit_inst_fn_member >> qexists `sm` >> simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `op <> Var p` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  drule_all alloc_copy_memory_owned_run >>
  disch_then (qspec_then `ctx` (qx_choosel_then [`t`, `w`] strip_assume_tac)) >>
  qexistsl [`t`, `w`] >> simp[eval_operand_def] >>
  conj_tac >- (qpat_x_assum `sx = _` SUBST_ALL_TAC >> gvs[]) >>
  conj_tac
  >- (rpt strip_tac >> `x <> p` by metis_tac[] >> simp[]) >>
  metis_tac[]
QED

Theorem optional_tuple_stage_run:
  !ctx func cenv cx es flag tys tvs vs se sa sb staged op s sw.
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) sa = (staged,sb) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op s /\
    expr_val_at cenv cx (TupleT tys) se sa es (ArrayV (TupleV vs)) op s /\
    eval_operand op s = SOME sw /\
    0 < type_memory_size_list tvs /\
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    tuple_val_wf vs tvs /\ values_have_types tvs vs /\
    ?t w. eval_operand staged t = SOME w /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      stmt_state_rel func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (?b sz. b <= w2n w /\
        w2n w + type_memory_size_list tvs <= b + sz /\
        ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
         (?name. local_region cenv es.scopes t name b sz))) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all expr_tuple_memory_owned >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `values_have_types tvs vs` by gvs[value_has_type_def] >> simp[] >>
  Cases_on `flag`
  >- (qpat_x_assum `?b sz. _` kall_tac >> gvs[] >>
      `val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) s.vs_memory /\
       val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
       val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <=
         type_memory_size_list tvs` by
        simp[val_in_memory_def, val_wf_def, val_footprint_def, type_memory_size_def] >>
      drule_all tuple_stage_copy_run >>
      disch_then (qspec_then `ctx` (qx_choosel_then [`t`, `w`] strip_assume_tac)) >>
      qexistsl [`t`, `w`] >> simp[] >>
      conj_tac >- gvs[val_in_memory_def] >>
      conj_tac >- (qexistsl [`w2n w`, `type_memory_size_list tvs`] >>
        simp[] >> metis_tac[]) >> metis_tac[]) >>
  gvs[comp_return_def] >> qexistsl [`s`, `sw`] >> simp[] >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED

Theorem type_memory_bytes_tuple_list:
  !tys tvs cenv.
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs ==>
    type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >>
  simp[type_memory_bytes_def, type_memory_size_def] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[type_memory_bytes_def]
QED

Theorem optional_tuple_stage_code:
  !flag cenv tys op.
    (if flag then
       do buf <- compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys));
          ptr <- comp_return buf.buf_operand;
          emit_void MCOPY [ptr; op; Lit (n2w (SUM (MAP (type_memory_bytes cenv) tys)))];
          comp_return ptr od
     else comp_return op) =
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op)
Proof
  rpt gen_tac >> Cases_on `flag` >> simp[] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       type_memory_bytes_def] >> simp[SF ETA_ss]
QED
