(* Connect the actual unpack prefix with the snapshot head interface. *)
Theory tuplePlaceCompilerPrefix
Ancestors
  tuplePlaceHead tupleAssignParts abiCallerTupleLayout
Libs
  monadsyntax

val () = monadsyntax.enable_monad "compilation";
val () = monadsyntax.enable_monadsyntax ();

Theorem tuple_place_compiler_prefix_head:
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\
  value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
  expr_post ctx func cenv cx e es sa su s0 es1 (ArrayV (TupleV vs)) op sv /\
  (!x. op = Var x ==> not_fresh_at su x) /\ sa.cs_next_id <= su.cs_next_id /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  compile_tuple_unpack cenv (TupleT ltys) (is_memory_view e) gs op su = ((),sf) /\
  fn_has_code su sf func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
  ~sv.vs_halted /\ sv.vs_current_bb = su.cs_current_bb /\
  sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?staged sl elems ss t w.
    (if is_memory_view e /\ EXISTS (\t. ~is_word_type t) ltys /\
        0 < type_memory_size_list ltvs then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT ltys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT ltys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    compile_tuple_load_all cenv staged ltys 0 sl = (elems,ss) /\
    compile_tuple_store_all cenv ltys gs elems ss = ((),sf) /\
    cs_extends su sl /\ cs_extends sl ss /\ cs_extends ss sf /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
    tuple_place_head ctx func cenv cx es1 sa.cs_next_id ss
      tys ltys ltvs vs elems w 0 t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x sv) /\
    (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    gas_marked_path F ctx func sv 0 (OK t)
Proof
  strip_tac >>
  `SUM (MAP (type_memory_bytes cenv) ltys) = type_memory_size_list ltvs` by
    (irule abiCallerTupleLayoutTheory.abi_caller_memory_size_list >> simp[]) >>
  `~(is_memory_view e /\ EXISTS (\t. ~is_word_type t) ltys /\
     0 < type_memory_size_list ltvs /\ ~cenv.ce_target CapMcopy)` by metis_tac[] >>
  qpat_x_assum `compile_tuple_unpack _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [stmtLoweringTheory.compile_tuple_unpack_def,
    LET_THM, GSYM CONJ_ASSOC, arithmeticTheory.GREATER_DEF,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def,
    GSYM compileEnvTheory.type_memory_bytes_def] >>
  qmatch_goalsub_abbrev_tac `(if guard then stage else comp_return op) su` >>
  Cases_on `(if guard then stage else comp_return op) su` >>
  rename1 `_ = (staged,sl)` >> simp[] >>
  Cases_on `compile_tuple_load_all cenv staged ltys 0 sl` >>
  rename1 `compile_tuple_load_all _ _ _ _ _ = (elems,ss)` >>
  simp[] >> strip_tac >>
  qunabbrev_tac `stage` >>
  drule (SRULE [compileEnvTheory.comp_ignore_bind_def]
    stmtSimAssignTupleTheory.tuple_stage_grows) >> strip_tac >>
  drule stmtSimReturnTheory.compile_tuple_load_all_grows >> strip_tac >>
  drule tuple_target_stores_growth >> strip_tac >>
  `cs_extends sl sf` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code su sl func /\ fn_has_code sl sf func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code sl ss func /\ fn_has_code ss sf func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `type_memory_bytes cenv (TupleT ltys) = type_memory_size_list ltvs` by
    (simp[compileEnvTheory.type_memory_bytes_def] >> metis_tac[]) >>
  `(if guard then
      do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT ltys));
         emit_void MCOPY [buf.buf_operand; op;
           Lit (n2w (type_memory_bytes cenv (TupleT ltys)))];
         comp_return buf.buf_operand od
    else comp_return op) su = (staged,sl)` by
    (Cases_on `guard` >>
     gvs[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
     pairarg_tac >> gvs[compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def]) >>
  gnvs[compileEnvTheory.comp_ignore_bind_def] >>

  irule tuple_place_assignment_prefix_head >>
  simp[] >>
  goal_assum (drule_at Any) >>
  simp[Abbr `guard`, compileEnvTheory.comp_ignore_bind_def] >>
  metis_tac[]
QED
