(* Loadable empty-declaration code layout; S1's wrappers are local. *)
Theory annAssignPtrEmptyLayout
Ancestors
 loweringSlice stmtSimDeclMem stmtSimDecl stmtSimProps stmtSimDefs exprLoweringProps
 emitHelperProps stmtLowering exprLowering compileEnv
 loweringPosts fragExec venomInst venomState list
Libs monadsyntax

Theorem compile_annassign_empty_parts_ptr:
 !cenv lctx ty id vtyp e st sf p sz.
 compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((),sf) /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
 has_length_word vtyp /\ is_empty_value_expr e ==>
 ?sA vv sB.
 emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((),sA) /\
 compile_expr cenv (expr_type e) e sA = (vv,sB) /\
 emit_void MSTORE [Var p; Lit 0w] sB = ((),sf)
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
 simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
 rpt (pairarg_tac >> simp[]) >> strip_tac >>
 imp_res_tac emit_inst_unit >> gvs[]
QED

Theorem annassign_empty_code_parts_ptr:
 !cenv lctx ty id vtyp e sa sf c func.
 stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c,sf) /\
 cenv.ce_alloca_locals /\ has_length_word vtyp /\ is_empty_value_expr e /\
 fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
 (!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   !a b vv. compile_expr c (expr_type e) e a = (vv,b) ==> cs_extends a b) ==>
 ?st sA sB vv p.
 declare_local cenv id vtyp sa = (c,st) /\
 FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
 emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((),sA) /\
 compile_expr c (expr_type e) e sA = (vv,sB) /\
 emit_void MSTORE [Var p; Lit 0w] sB = ((),sf) /\
 local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
 cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
 fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
 MEM (mk_inst st.cs_next_id ALLOCA
   [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
 rpt gen_tac >> strip_tac >>
 drule stmt_env_annassign >> strip_tac >>
 drule_all declare_local_ptr >> strip_tac >>
 drule_all compile_annassign_empty_parts_ptr >>
 disch_then (qx_choosel_then [`sA`,`vv`,`sB`] strip_assume_tac) >>
 `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
 `cs_extends sA sB` by metis_tac[] >>
 `cs_extends sB sf` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
 `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
 drule_all annassign_alloca_code >> strip_tac >>
 `fn_has_code sA sB func /\ fn_has_code sB sf func` by
   metis_tac[fn_has_code_split] >>
 qexistsl [`st`,`sA`,`sB`,`vv`,`STRING #"%" (toString sa.cs_next_var)`] >>
 simp[]
QED
