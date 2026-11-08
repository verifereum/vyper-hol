(* Loadable declaration layout boundary; the S1 wrapper is local. *)
Theory annAssignPtrWordLayout
Ancestors
 loweringSlice stmtSimDecl stmtSimProps stmtSimDefs exprLoweringProps
 emitHelperProps stmtLowering exprLowering compileEnv
 loweringPosts fragExec venomInst venomState list
Libs monadsyntax

Theorem annassign_word_code_parts_ptr:
 !cenv lctx ty id vtyp e sa sf c func.
 stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c,sf) /\
 cenv.ce_alloca_locals /\ is_word_type vtyp /\ ~has_length_word vtyp /\
 fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
 (!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   !a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
     cs_extends a b) ==>
 ?st sA sB op p.
 declare_local cenv id vtyp sa = (c,st) /\
 FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
 emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((),sA) /\
 lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
 emit_void MSTORE [Var p; op] sB = ((),sf) /\
 local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
 cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
 fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
 MEM (mk_inst st.cs_next_id ALLOCA
   [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
 simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
 Cases_on `declare_local cenv id vtyp sa` >>
 rename1 `declare_local cenv id vtyp sa = (bc,st)` >>
 Cases_on `compile_stmt bc lctx ty (AnnAssign id vtyp e) st` >>
 rename1 `compile_stmt bc lctx ty (AnnAssign id vtyp e) st = (u,sb)` >>
 Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
 rename1 `declare_local cenv id vtyp sa = (c,st)` >>
 rename1 `fn_has_code sa sf func` >>
 drule_all declare_local_ptr >> strip_tac >>
 `local_ptrs_reserved c st` by metis_tac[declare_local_reserved] >>
 `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
 `!a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
   cs_extends a b` by metis_tac[] >>
 drule_all compile_annassign_word_parts >>
 disch_then (qx_choosel_then [`sA`,`sB`,`op`] strip_assume_tac) >>
 `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
 `fn_has_code st sA func` by
   (qspecl_then [`st`,`sA`,`sf`,`func`] mp_tac fn_has_code_split >> simp[]) >>
 `fn_has_code sA sf func` by
   (qspecl_then [`st`,`sA`,`sf`,`func`] mp_tac fn_has_code_split >> simp[]) >>
 `fn_has_code sB sf func` by
   (qspecl_then [`sA`,`sB`,`sf`,`func`] mp_tac fn_has_code_split >> simp[]) >>
 qexistsl [`sA`,`sB`,`op`] >> gvs[]
QED
