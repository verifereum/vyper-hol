(* Compiler boundaries for declarations which change aggregate layout. *)
Theory stmtSimDeclTypedCode
Ancestors
  stmtSimDeclMem bodyDeclCopyMemory exprOpenCopies exprOpenPrimitives stmtLoweringMono
  stmtSimDecl stmtSimProps stmtLowering exprLowering exprLoweringProps context
  emitHelper emitHelperProps loweringSlice fragExec compileEnv
  freshWrites finite_map venomInst

Theorem compile_assign_value_typed_open:
  !cenv dst src loc dty sty bytes sa sb.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    ~block_is_terminated sa /\
    compile_assign_value cenv dst LocMemory src F loc dty sty bytes sa = ((),sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc = SOME LocMemory`
  >- (gvs[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac compile_alloc_buffer_open >>
      gvs[comp_return_def] >>
      rename1 `compile_copy_memory _ _ _ sm = ((),sn)` >>
      `~block_is_terminated sn` by
        (Cases_on `type_memory_bytes cenv sty` >>
         gvs[compile_copy_memory_def, comp_return_def] >>
         drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
      metis_tac[compile_store_memory_open]) >>
  gvs[compile_assign_value_def] >>
  metis_tac[compile_store_memory_open]
QED

Theorem annassign_typed_code_parts:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) /\
    cenv.ce_alloca_locals /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       !a b op. lower_value compile_expr c (expr_type e) e a = (op, b) ==>
                cs_extends a b) ==>
    ?st sA sV sB vv op p.
      declare_local cenv id vtyp sa = (c, st) /\
      FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((), sA) /\
      compile_expr c (expr_type e) e sA = (vv, sV) /\
      unwrap_value c vv sV = (op, sB) /\
      lower_value compile_expr c (expr_type e) e sA = (op, sB) /\
      compile_assign_value c (Var p) LocMemory op F (vv_location vv) vtyp
        (lowered_value_type cenv e)
        (type_memory_bytes c vtyp) sB = ((), sf) /\
      local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
      cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
      fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
      MEM (mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule stmt_env_annassign >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all annassign_copy_parts_mem >>
  disch_then (qx_choosel_then [`sA`, `sV`, `sB`, `vv`, `op`] strip_assume_tac) >>
  `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `cs_extends sA sB` by metis_tac[] >>
  `cs_extends sB sf` by
    (mp_tac (cj 1 ci_mono_stmt_helpers) >>
     simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
  `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >>
  qexistsl [`st`, `sA`, `sV`, `sB`, `vv`, `op`,
            `STRING #"%" (toString sa.cs_next_var)`] >> gvs[]
QED
