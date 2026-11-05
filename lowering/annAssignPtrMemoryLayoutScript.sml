(* Code-layout boundaries for the copying annotated declaration branch. *)
Theory annAssignPtrMemoryLayout
Ancestors
 annAssignPtrFacts loweringSlice stmtSimProps stmtSimDefs
 stmtSimDeclMem stmtSimDecl exprLoweringProps
 stmtLowering exprLowering emitHelper emitHelperProps context compileEnv
 loweringPosts fragExec venomInst venomState list rich_list finite_map
Libs monadsyntax

Theorem annassign_declared_memory_types_ptr:
 !cenv id vtyp sa c st.
 declare_local cenv id vtyp sa = (c,st) /\ cenv.ce_alloca_locals ==>
 type_memory_bytes c = type_memory_bytes cenv /\
 (!e. lowered_value_type c e = lowered_value_type cenv e)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all declare_local_ptr >> strip_tac >>
 `c.ce_struct_fields = cenv.ce_struct_fields /\
  c.ce_func_return_type = cenv.ce_func_return_type` by
   (qpat_x_assum `c with <|ce_vars := _; ce_var_type := _;
      ce_dynarray_capacity := _|> = cenv` mp_tac >>
    simp[compile_env_component_equality]) >>
 simp[type_memory_bytes_frame, oneline lowered_value_type_def]
QED

Theorem annassign_memory_lowering_parts_ptr:
 !cenv lctx ty id vtyp e st sf p sz.
 compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((),sf) /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
 ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) ==>
 ?sA sV sB vv op.
 emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((),sA) /\
 compile_expr cenv (expr_type e) e sA = (vv,sV) /\
 unwrap_value cenv vv sV = (op,sB) /\
 lower_value compile_expr cenv (expr_type e) e sA = (op,sB) /\
 compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
  vtyp (lowered_value_type cenv e)
  (case vtyp of ArrayT elem_ty (Dynamic _) =>
    SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
          type_memory_bytes cenv elem_ty) | _ => NONE)
  (type_memory_bytes cenv vtyp) sB = ((),sf)
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
 simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
 rpt (pairarg_tac >> simp[]) >> strip_tac >>
 imp_res_tac emit_inst_unit >>
 gvs[lower_value_def, comp_bind_def] >> metis_tac[]
QED

Theorem annassign_memory_code_parts_ptr:
 !cenv lctx ty id vtyp e sa sf c func.
 stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c,sf) /\
 cenv.ce_alloca_locals /\ ~is_word_type vtyp /\
 ~(has_length_word vtyp /\ is_empty_value_expr e) /\
 (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
 fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
 (!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
   !a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
    cs_extends a b) ==>
 ?st sA sV sB vv op p.
 declare_local cenv id vtyp sa = (c,st) /\
 FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
 emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((),sA) /\
 compile_expr c (expr_type e) e sA = (vv,sV) /\
 unwrap_value c vv sV = (op,sB) /\
 lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
 compile_assign_value c (Var p) LocMemory op F (vv_location vv) vtyp
  (lowered_value_type cenv e)
  (case vtyp of ArrayT elem_ty (Dynamic _) =>
    SOME ((type_memory_bytes c elem_ty + 31) DIV 32,
          type_memory_bytes c elem_ty) | _ => NONE)
  (type_memory_bytes c vtyp) sB = ((),sf) /\
 local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
 cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
 fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
 MEM (mk_inst st.cs_next_id ALLOCA
  [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
 rpt gen_tac >> strip_tac >>
 drule stmt_env_annassign >> strip_tac >>
 drule_all declare_local_ptr >> strip_tac >>
 drule_all annassign_declared_memory_types_ptr >> strip_tac >>
 drule_all annassign_memory_lowering_parts_ptr >>
 disch_then (qx_choosel_then [`sA`,`sV`,`sB`,`vv`,`op`] strip_assume_tac) >>
 `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
 `cs_extends sA sB /\ cs_extends sB sf` by
  metis_tac[compile_assign_memory_widen_appends, cs_appends_def] >>
 `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
 drule_all annassign_alloca_code >> strip_tac >>
 `fn_has_code sA sB func /\ fn_has_code sB sf func` by
  metis_tac[fn_has_code_split] >>
 qexistsl [`st`,`sA`,`sV`,`sB`,`vv`,`op`,
   `STRING #"%" (toString sa.cs_next_var)`] >> simp[] >>
 qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >> simp[]
QED
