(* Target-independent tuple assignment code decomposition. *)
Theory tupleAssignCode
Ancestors
  stmtSim stmtLowering exprLowering emitHelper compileEnv
  list rich_list
Libs
  monadsyntax

Theorem assign_tuple_targets_code_decompose:
  !cenv lctx ty gs e tys sa sf c.
    stmt_env cenv lctx ty (Assign (TupleTarget gs) e) sa = (c,sf) /\
    expr_type e = TupleT tys /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) ==>
    c = cenv /\
    ?vv sc op su staged sl elems ss.
      compile_expr cenv (TupleT tys) e sa = (vv,sc) /\
      unwrap_value cenv vv sc = (op,su) /\
      (if is_memory_view e /\ vv_location vv = SOME LocMemory /\
          EXISTS (\t. ~is_word_type t) tys /\
          0 < SUM (MAP (type_memory_bytes cenv) tys) then
         do buf <- compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys));
            ptr <- comp_return buf.buf_operand;
            emit_void MCOPY [ptr; op;
              Lit (n2w (SUM (MAP (type_memory_bytes cenv) tys)))];
            comp_return ptr od
       else comp_return op) su = (staged,sl) /\
      compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
      compile_tuple_store_all cenv tys gs elems ss = ((),sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
     compile_tuple_unpack_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (TupleT tys) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sc)` >>
  Cases_on `unwrap_value cenv vv sc` >>
  rename1 `unwrap_value _ _ _ = (op,su)` >> simp[] >>
  `~(is_memory_view e /\ vv_location vv = SOME LocMemory /\
      EXISTS (\t. ~is_word_type t) tys /\
      0 < SUM (MAP (type_memory_bytes cenv) tys) /\
      ~cenv.ce_target CapMcopy)` by metis_tac[] >>
  asm_simp_tac (srw_ss()) [GSYM CONJ_ASSOC, arithmeticTheory.GREATER_DEF,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `(if guard then stage else comp_return op) su` >>
  Cases_on `(if guard then stage else comp_return op) su` >>
  rename1 `_ = (staged,sl)` >> simp[] >>
  Cases_on `compile_tuple_load_all cenv staged tys 0 sl` >>
  rename1 `compile_tuple_load_all _ _ _ _ _ = (elems,ss)` >> simp[] >>
  Cases_on `compile_tuple_store_all cenv tys gs elems ss` >>
  rename1 `compile_tuple_store_all _ _ _ _ _ = (u,sf1)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  qexistsl [`staged`, `sl`, `elems`, `ss`] >> simp[]
QED
