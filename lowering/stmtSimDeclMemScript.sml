(*
 * Statement simulation: a memory-backed local's declaration (#637)
 *
 * AnnAssign over stmt_frag (stmtSim) for a local whose type is not a word
 * type (an aggregate, a bytestring): the right-hand side's errors exit; on
 * a value the local's ALLOCA runs and compile_assign_value copies the
 * value's bytes into the local's buffer, staged through a buffer of its
 * own when the value is in memory, so the buffer holds the value as
 * val_in_memory lays it out.
 *
 * TOP-LEVEL:
 *   compile_annassign_memory_widen_stmt_frag — a memory-backed local's
 *                                              declaration, for every
 *                                              outcome of its right-hand
 *                                              side, lowered at the declared
 *                                              type or both bytestrings
 *   compile_annassign_memory_stmt_frag — the same, where the right-hand
 *                                        side is lowered at the declared
 *                                        type
 *)

Theory stmtSimDeclMem
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim stmtSimDeclStore
  stmtSimDecl valueCopy intCallResult exprOperandVar freshWrites
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv valueEncoding valueTypingMemoryProps
  vyperInterpreter vyperState vyperValue vyperTyping vyperExprNoControl
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* Declaration changes only the name-indexed parts of the environment;
   layout and the expression's lowered type are unaffected. *)
Theorem declare_local_memory_types[local]:
  !cenv id vtyp sa c st.
    declare_local cenv id vtyp sa = (c, st) /\ cenv.ce_alloca_locals ==>
    (!ty. type_memory_bytes c ty = type_memory_bytes cenv ty) /\
    (!e. lowered_value_type c e = lowered_value_type cenv e)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `c.ce_struct_fields = cenv.ce_struct_fields` by
    (qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
                            ce_dynarray_capacity := _ |> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  conj_tac
  >- (`!env ty. env.ce_struct_fields = cenv.ce_struct_fields ==>
          type_memory_bytes env ty = type_memory_bytes cenv ty` suffices_by
        metis_tac[] >>
      ho_match_mp_tac type_memory_bytes_ind >>
      rw[type_memory_bytes_def] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[]) >>
  gen_tac >> simp[oneline lowered_value_type_def]
QED

Theorem compile_assign_memory_appends:
  !cenv dst src loc ty info sz.
    cs_appends (compile_assign_value cenv dst LocMemory src F loc ty ty info sz)
Proof
  rpt gen_tac >>
  simp[compile_assign_value_def, compile_store_memory_def] >>
  Cases_on `loc = SOME LocMemory` >> simp[] >>
  Cases_on `is_word_type ty` >> simp[] >>
  Cases_on `is_bytestring_type ty` >>
  Cases_on `type_memory_bytes cenv ty` >>
  simp[compile_alloc_buffer_def, compile_copy_memory_def,
       compile_store_bytestring_def, compile_bytestring_copy_len_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return,
          compile_copy_memory_def, compile_store_bytestring_def,
          compile_bytestring_copy_len_def]) >>
  rw[cs_appends_emit_helpers, cs_appends_return,
          compile_copy_memory_def, compile_store_bytestring_def,
          compile_bytestring_copy_len_def]
QED

(* A bytestring destination copies the source's runtime length whatever the
   source's bound: the store is the one at the destination type. *)
Theorem compile_store_memory_bytestring_src:
  !cenv src dst dty sty.
    is_bytestring_type dty ==>
    compile_store_memory cenv src dst dty sty =
    compile_store_memory cenv src dst dty dty
Proof
  simp[compile_store_memory_def]
QED

Theorem is_bytestring_word_type:
  !t. is_bytestring_type t ==> ~is_word_type t
Proof
  Cases >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  simp[is_bytestring_type_def, is_word_type_def]
QED

Theorem bytestring_type_value:
  !tenv t tv.
    is_bytestring_type t /\ evaluate_type tenv t = SOME tv ==>
    (?n. tv = BaseTV (BytesT (Dynamic n))) \/ (?n. tv = BaseTV (StringT n))
Proof
  rpt gen_tac >> Cases_on `t` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  rw[is_bytestring_type_def, evaluate_type_def]
QED

(* The two bytestring types, of any bounds, lay out a value of either the
   same way: a length word, then the bytes. *)
Theorem bytestring_val_in_memory_transfer:
  !tenv t1 t2 tv1 tv2 v off mem.
    is_bytestring_type t1 /\ is_bytestring_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ evaluate_type tenv t2 = SOME tv2 /\
    value_has_type tv2 v /\ val_in_memory tv1 v off mem ==>
    val_in_memory tv2 v off mem
Proof
  rpt strip_tac >>
  qspecl_then [`tenv`, `t1`, `tv1`] mp_tac bytestring_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`] mp_tac bytestring_type_value >>
  simp[] >> rpt strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def]
QED

(* So do their footprints: a value of both a bytestring type and another
   fits the other's size. *)
Theorem bytestring_val_footprint_le[local]:
  !tenv t1 t2 tv1 tv2 v.
    is_bytestring_type t1 /\ is_bytestring_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ evaluate_type tenv t2 = SOME tv2 /\
    value_has_type tv1 v /\ value_has_type tv2 v ==>
    val_footprint tv1 v <= type_memory_size tv2
Proof
  rpt strip_tac >>
  `val_footprint tv1 v = val_footprint tv2 v` by
    (qspecl_then [`tenv`, `t1`, `tv1`] mp_tac bytestring_type_value >>
     qspecl_then [`tenv`, `t2`, `tv2`] mp_tac bytestring_type_value >>
     simp[] >> rpt strip_tac >>
     Cases_on `v` >> gvs[value_has_type_def, val_footprint_def]) >>
  simp[] >> irule val_footprint_le >> simp[value_has_type_memory_wf]
QED

Theorem lowered_value_type_bytestring[local]:
  !cenv e.
    is_bytestring_type (expr_type e) ==>
    is_bytestring_type (lowered_value_type cenv e)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, is_bytestring_type_def]
QED

(* The lowering's buffer for e's value, at e's lowered type, holds the
   value whose layout at the declared type is copied. *)
Theorem annassign_widen_footprint[local]:
  !tenv cenv e vtyp tyv ltv v.
    (expr_type e = vtyp \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type tenv vtyp = SOME tyv /\
    evaluate_type tenv (lowered_value_type cenv e) = SOME ltv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    value_has_type tyv v /\ value_has_type ltv v ==>
    val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `lowered_value_type cenv e = vtyp`
  >- (gvs[] >> irule val_footprint_le >> simp[value_has_type_memory_wf]) >>
  `is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)` by gvs[] >>
  `is_bytestring_type (lowered_value_type cenv e)` by
    simp[lowered_value_type_bytestring] >>
  simp[] >> irule bytestring_val_footprint_le >> metis_tac[]
QED

Theorem compile_assign_memory_widen_appends:
  !cenv dst src loc dty sty info sz.
    sty = dty \/ is_bytestring_type dty ==>
    cs_appends (compile_assign_value cenv dst LocMemory src F loc dty sty info sz)
Proof
  rpt gen_tac >> strip_tac >- simp[compile_assign_memory_appends] >>
  simp[compile_assign_value_def, compile_store_memory_bytestring_src] >>
  `!src. cs_appends (compile_store_memory cenv src dst dty dty)` by
    (gen_tac >> qspecl_then [`cenv`, `dst`, `src`, `NONE`, `dty`] mp_tac
       compile_assign_memory_appends >> simp[compile_assign_value_def]) >>
  rw[] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return, compile_alloc_buffer_def,
          compile_copy_memory_def]) >>
  Cases_on `type_memory_bytes cenv sty` >>
  rw[compile_copy_memory_def, cs_appends_emit_helpers, cs_appends_return]
QED

Theorem compile_annassign_memory_parts[local]:
  !cenv lctx ty id vtyp e st sf p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) ==>
    ?sA sV sB vv op.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sA) /\
      compile_expr cenv (expr_type e) e sA = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sA = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, emit_local_alloca_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emit_inst_unit >>
  gvs[lower_value_def, comp_bind_def] >> metis_tac[]
QED

(* A declaration's step: declare_local, then the statement's code under the
   extended environment. *)
Theorem stmt_env_annassign:
  !cenv lctx ty id vtyp e sa c sf.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) ==>
    ?st. declare_local cenv id vtyp sa = (c, st) /\
         compile_stmt c lctx ty (AnnAssign id vtyp e) st = ((), sf)
Proof
  rpt gen_tac >>
  pure_rewrite_tac[stmt_env_def, declare_stmt_local_def, comp_bind_def,
                  comp_ignore_bind_def, comp_return_def] >>
  Cases_on `declare_local cenv id vtyp sa` >>
  rename1 `declare_local cenv id vtyp sa = (bc, st)` >>
  Cases_on `compile_stmt bc lctx ty (AnnAssign id vtyp e) st` >>
  rename1 `compile_stmt bc lctx ty (AnnAssign id vtyp e) st = (u, sb)` >>
  Cases_on `u` >>
  asm_simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, comp_return_def,
                       pairTheory.UNCURRY_DEF, LET_THM, pairTheory.PAIR_EQ] >>
  disch_then (CONJUNCTS_THEN SUBST_ALL_TAC) >>
  asm_rewrite_tac[]
QED

(* The ALLOCA of a declared local's buffer, emitted from st to sA ahead of
   the rest of the declaration's code up to sf: the local's pointer is
   handed out before sA, the pointers stay reserved, and the ALLOCA is an
   instruction of func. *)
Theorem annassign_alloca_code:
  !cenv c id vtyp sa st sA sf func.
    declare_local cenv id vtyp sa = (c, st) /\ cenv.ce_alloca_locals /\
    local_ptrs_reserved cenv sa /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))]
      [STRING #"%" (toString sa.cs_next_var)] st = ((), sA) /\
    cs_extends sA sf /\ fn_has_code st sf func ==>
    local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\
    not_fresh_at sA (STRING #"%" (toString sa.cs_next_var)) /\
    cs_extends st sA /\ fn_has_code st sA func /\ fn_has_code sA sf func /\
    MEM (mk_inst st.cs_next_id ALLOCA
           [Lit (n2w (type_memory_bytes cenv vtyp))]
           [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved c st` by metis_tac[declare_local_reserved] >>
  `cs_extends st sA` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code st sA func /\ fn_has_code sA sf func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved c sA` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     imp_res_tac emit_inst_extends >> simp[]) >>
  `not_fresh_at sA (STRING #"%" (toString sa.cs_next_var))` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[] >> drule emit_inst_extends >> strip_tac >>
  `?bb. lookup_block sA.cs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX sA.cs_current_insts bb.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  `MEM (mk_inst st.cs_next_id ALLOCA
     [Lit (n2w (type_memory_bytes cenv vtyp))]
     [STRING #"%" (toString sa.cs_next_var)]) bb.bb_instructions` by
    gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  gvs[] >> metis_tac[lookup_block_fn_insts]
QED

Theorem annassign_memory_code_parts[local]:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) /\
    cenv.ce_alloca_locals /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
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
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes c elem_ty + 31) DIV 32,
                 type_memory_bytes c elem_ty) | _ => NONE)
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
  drule_all declare_local_memory_types >> strip_tac >>
  `lowered_value_type c e = lowered_value_type cenv e` by metis_tac[] >>
  drule_all compile_annassign_memory_parts >>
  disch_then (qx_choosel_then [`sA`, `sV`, `sB`, `vv`, `op`] strip_assume_tac) >>
  `fn_has_code st sf func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `cs_extends sA sB /\ cs_extends sB sf` by
    metis_tac[compile_assign_memory_widen_appends, cs_appends_def] >>
  `cs_extends sA sf` by metis_tac[cs_extends_trans] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `fn_has_code sA sB func /\ fn_has_code sB sf func` by
    metis_tac[fn_has_code_split] >>
  qexistsl [`st`, `sA`, `sV`, `sB`, `vv`, `op`,
            `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[] >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[]
QED

(* Copying into an allocated but non-live buffer preserves all live locals,
   even if this instruction's allocation is being reused at runtime. *)
Theorem stmt_state_rel_mcopy_alloca[local]:
  !func cenv cx es s inst p dst src sz.
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (dst, sz) ==>
    stmt_state_rel func cenv cx es (mcopy dst src sz s)
Proof
  rpt strip_tac >>
  `(mcopy dst src sz s with <|vs_vars := s.vs_vars;
                             vs_memory := s.vs_memory|>) = s` by
    simp[mcopy_def, write_memory_with_expansion_def, LET_THM] >>
  `!q. lookup_var q (mcopy dst src sz s) = lookup_var q s` by
    simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mcopy dst src sz s)` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac
     >- simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
             arithmeticTheory.MAX_DEF] >>
     conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
     reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
     qpat_assum `stmt_state_rel _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >>
     strip_tac >> qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _` drule_all >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  irule result_state_memory_frame >> conj_tac
  >- (qexists_tac `s` >> simp[] >>
  rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
  `regions_disjoint dst sz b sz'` by
    (irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`, `func`, `inst`, `name`, `p`, `es.scopes`, `s`] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  fs[compileEnvTheory.regions_disjoint_def]) >> first_assum ACCEPT_TAC
QED

Theorem mcopy_alloca_framed_frag[local]:
  !ctx func cenv cx es sa sb s inst p dw sw src sz tv v.
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sa = ((), sb) /\
    lookup_var p s = SOME dw /\ eval_operand src s = SOME sw /\
    sz < dimword (:256) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw, sz) /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz ==>
    frag_exec ctx sa sb (\t. t = s)
      (\t. stmt_state_rel func cenv cx es t /\
           val_in_memory tv v (w2n dw) t.vs_memory /\
           (!q. lookup_var q t = lookup_var q s) /\
           t.vs_allocas = s.vs_allocas) (\r. F)
Proof
  rpt strip_tac >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  drule_all emit_mcopy_run >> strip_tac >>
  `stmt_state_rel func cenv cx es (mcopy (w2n dw) (w2n sw) sz s)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl_tac [`inst`, `p`] >> simp[]) >>
  `val_in_memory tv v (w2n dw) (mcopy (w2n dw) (w2n sw) sz s).vs_memory` by
    (irule mcopy_val_in_memory >> simp[]) >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND3] >>
  simp[stmt_state_rel_inst_idx] >>
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def]
QED

Theorem alloc_copy_memory_framed_run:
  !ctx func cenv cx es sa sm sb s0 p src sz sw tv v.
    emit_inst ALLOCA [Lit (n2w sz)] [p] sa = ((), sm) /\
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sm = ((), sb) /\
    stmt_state_rel func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
    src <> Var p /\ eval_operand src s0 = SOME sw /\
    val_in_memory tv v (w2n sw) s0.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?s2 w. lookup_var p s2 = SOME w /\
      stmt_state_rel func cenv cx es s2 /\
      val_in_memory tv v (w2n w) s2.vs_memory /\
      (!x. x <> p ==> lookup_var x s2 = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP s2.vs_allocas aid = SOME entry) /\
      ~s2.vs_halted /\ s2.vs_current_bb = sb.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb.cs_current_insts /\
      !fuel r. run_from fuel ctx func s2 = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt strip_tac >> drule_all annassign_alloca_operand_framed_run >>
  disch_then (qspec_then `ctx` (qx_choosel_then [`s1`, `w`] strip_assume_tac)) >>
  `eval_operand src s1 = SOME sw` by simp[] >>
  `val_in_memory tv v (w2n sw) s1.vs_memory` by simp[] >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
   inst.inst_id = sa.cs_next_id` by
    simp[Abbr `inst`, mk_inst_def] >>
  `FLOOKUP s1.vs_allocas inst.inst_id = SOME (w2n w, sz)` by simp[] >>
  drule_all mcopy_alloca_framed_frag >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule frag_exec_no_exit_run >>
  disch_then (qspecl_then [`func`, `s1`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  qexistsl_tac [`s2`, `w`] >> simp[]
QED

Theorem stmt_state_rel_declare_store_frame[local]:
  !func cenv cx es s t sa id p sz w inst v tyv sc rest a.
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size tyv <= b ==>
           mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >- simp[] >>
     `not_fresh_at sa q` by
       (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[]) >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
       mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     `b + sz' <= w2n w \/ w2n w + type_memory_size tyv <= b` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (`t.vs_data_section = s.vs_data_section` by
       (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     irule immutables_rel_mem_agree >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >>
     fs[immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
     `off + type_memory_size tv <= w2n w \/
      w2n w + type_memory_size tyv <= off` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl_tac [`inst`, `s`, `w`] >> gs[] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Theorem annassign_memory_store_run[local]:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `get_tenv cx`, `tyv`, `v`, `sw`, `w`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel func cenv cx es'` >>
  `stmt_state_rel func cenv cx es' t` by
    (simp[Abbr `es'`] >> irule stmt_state_rel_declare_store_frame >>
     simp[] >> qexistsl_tac [`inst`, `s`, `sa`, `w`] >> gs[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `frag_exec ctx sa sb (\u. u = s)
     (\u. stmt_state_rel func cenv cx es' u /\
          (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
          u.vs_allocas = s.vs_allocas) (\r. F)` by
    (irule frag_exec_run_inst_seq >>
     fs[same_blocks_def, lookup_var_def] >> simp[stmt_state_rel_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  drule frag_exec_no_exit_run >>
  disch_then (qspecl_then [`func`, `s`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists_tac `u` >> simp[]
QED

(* Split the overlap-safe assignment into its allocation, flat copy and
   typed store. The allocation and the flat copy have the source's size;
   the store is the one at the destination type, which for a bytestring
   destination copies the runtime length whatever the source's bound.  The
   allocation output is fresh at the assignment entry. *)
Theorem annassign_staged_memory_widen_parts:
  !cenv dst src dty sty info bytes sa sb func.
    compile_assign_value cenv dst LocMemory src F (SOME LocMemory)
      dty sty info bytes sa = ((),sb) /\
    (sty = dty \/ is_bytestring_type dty) /\
    0 < type_memory_bytes cenv sty /\ fn_has_code sa sb func ==>
    ?sx sm sn tmp.
      sx = sa with cs_next_var := sa.cs_next_var + 1 /\
      ~not_fresh_at sa tmp /\ not_fresh_at sn tmp /\
      sa.cs_next_var <= sn.cs_next_var /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv sty))] [tmp]
        sx = ((),sm) /\
      emit_void MCOPY [Var tmp; src; Lit (n2w (type_memory_bytes cenv sty))]
        sm = ((),sn) /\
      compile_store_memory cenv (Var tmp) dst dty dty sn = ((),sb) /\
      cs_extends sa sx /\ cs_extends sx sm /\ cs_extends sm sn /\ cs_extends sn sb /\
      fn_has_code sx sm func /\ fn_has_code sm sn func /\
      fn_has_code sn sb func
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!x y. compile_store_memory cenv x y dty sty =
         compile_store_memory cenv x y dty dty` by
    (rpt gen_tac >> qpat_x_assum `_ \/ _` strip_assume_tac >>
     simp[compile_store_memory_bytestring_src]) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `cs_appends (compile_store_memory cenv (Var (STRING #"%" (toString sa.cs_next_var)))
      dst dty dty)` by
    (qspecl_then [`cenv`, `dst`, `Var (STRING #"%" (toString sa.cs_next_var))`,
                   `NONE`] mp_tac compile_assign_memory_appends >>
     simp[compile_assign_value_def]) >>
  rename1 `compile_copy_memory _ _ _ sm = ((),sn)` >>
  qabbrev_tac `sx = sa with cs_next_var := sa.cs_next_var + 1` >>
  `emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv sty))]
      [STRING #"%" (toString sa.cs_next_var)] sx = ((),sm)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, Abbr `sx`] >> strip_tac >> gvs[]) >>
  `emit_void MCOPY [Var (STRING #"%" (toString sa.cs_next_var)); src;
      Lit (n2w (type_memory_bytes cenv sty))] sm = ((),sn)` by
    (Cases_on `type_memory_bytes cenv sty` >> gvs[compile_copy_memory_def]) >>
  `cs_extends sx sm /\ cs_extends sm sn /\ cs_extends sn sb` by
    metis_tac[cs_appends_def, cs_appends_emit_helpers] >>
  `cs_extends sa sx` by
    simp[Abbr `sx`, cs_extends_def, emitted_blocks_def] >>
  `sm.cs_next_var = sn.cs_next_var` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_def, fresh_id_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  qexistsl_tac [`sm`, `sn`, `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[Abbr `sx`] >> conj_tac >-
    (irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem annassign_staged_memory_parts:
  !cenv dst src ty info bytes sa sb func.
    compile_assign_value cenv dst LocMemory src F (SOME LocMemory)
      ty ty info bytes sa = ((),sb) /\
    0 < type_memory_bytes cenv ty /\ fn_has_code sa sb func ==>
    ?sx sm sn tmp.
      sx = sa with cs_next_var := sa.cs_next_var + 1 /\
      ~not_fresh_at sa tmp /\ not_fresh_at sn tmp /\
      sa.cs_next_var <= sn.cs_next_var /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv ty))] [tmp]
        sx = ((),sm) /\
      emit_void MCOPY [Var tmp; src; Lit (n2w (type_memory_bytes cenv ty))]
        sm = ((),sn) /\
      compile_store_memory cenv (Var tmp) dst ty ty sn = ((),sb) /\
      cs_extends sa sx /\ cs_extends sx sm /\ cs_extends sm sn /\ cs_extends sn sb /\
      fn_has_code sx sm func /\ fn_has_code sm sn func /\
      fn_has_code sn sb func
Proof
  rpt strip_tac >> irule annassign_staged_memory_widen_parts >> simp[] >>
  metis_tac[]
QED

Theorem annassign_memory_assign_run[local]:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sty sa sb sw loc info bytes.
    compile_assign_value cenv (Var p) LocMemory src F loc ty sty info bytes sa = ((),sb) /\
    (sty = ty \/ is_bytestring_type ty) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    val_footprint tyv v <= type_memory_bytes cenv sty /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv <= sz /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> Cases_on `loc = SOME LocMemory`
  >- (qpat_x_assum `loc = _` SUBST_ALL_TAC >>
      drule_all annassign_staged_memory_widen_parts >>
      disch_then (qx_choosel_then [`sx`, `sm`, `sn`, `tmp`] strip_assume_tac) >>
      `MEM (mk_inst sx.cs_next_id ALLOCA
          [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) (fn_insts func)` by
        (drule emit_inst_extends >> strip_tac >>
         `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
                isPREFIX sm.cs_current_insts bb.bb_instructions` by
           metis_tac[fn_has_code_start] >>
         `MEM (mk_inst sx.cs_next_id ALLOCA
           [Lit (n2w (type_memory_bytes cenv sty))] [tmp]) bb.bb_instructions` by
           gvs[rich_listTheory.IS_PREFIX_APPEND] >>
         metis_tac[lookup_block_fn_insts]) >>
      `not_local_ptr cenv es.scopes tmp` by
        (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
      `src <> Var tmp /\ p <> tmp` by metis_tac[] >>
      `s.vs_current_bb = sx.cs_current_bb /\
       s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
      drule_all alloc_copy_memory_framed_run >>
      disch_then (qspec_then `ctx`
        (qx_choosel_then [`u`, `uw`] strip_assume_tac)) >>
      `lookup_var p u = SOME w /\
       FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz)` by simp[] >>
      `not_fresh_at sn p` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      `local_ptrs_reserved cenv sn` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
      `!x. Var tmp = Var x ==> not_fresh_at sn x` by simp[] >>
      `eval_operand (Var tmp) u = SOME uw` by simp[eval_operand_def] >>
      `lookup_scopes id es.scopes = NONE /\ not_local_ptr cenv es.scopes p` by simp[] >>
      drule_all annassign_memory_store_run >>
      disch_then (qspecl_then [`ctx`, `a`] mp_tac) >>
      disch_then (qx_choose_then `t` strip_assume_tac) >>
      qexists_tac `t` >> simp[] >> conj_tac
      >- (rpt strip_tac >>
          `not_fresh_at sn x` by
            (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
          `x <> tmp` by metis_tac[] >> simp[]) >>
      metis_tac[]) >>
  `compile_store_memory cenv src (Var p) ty ty sa = ((),sb)` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     gvs[compile_assign_value_def, compile_store_memory_bytestring_src]) >>
  drule_all annassign_memory_store_run >>
  disch_then (qspecl_then [`ctx`, `a`] ACCEPT_TAC)
QED

Theorem annassign_memory_store_post_run[local]:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p sz w inst v etv tyv vtyp sty
   sc rest a loc info bytes.
    expr_post func cenv cx e es sa sb s0 es1 v op s /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
    cs_extends sa sb /\ local_ptrs_reserved cenv sa /\
    ~is_word_type vtyp /\
    (expr_type e = vtyp \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (sty = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    value_has_type tyv v /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv <= sz /\
    type_memory_size tyv + 64 < dimword (:256) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    val_footprint tyv v <= type_memory_bytes cenv sty /\
    compile_assign_value cenv (Var p) LocMemory op F loc
      vtyp sty info bytes sb = ((),sf) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w,sz) ==>
    ?t. stmt_state_rel func cenv cx
          (es1 with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
               lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_then (drule_then assume_tac) compile_lower_value_var >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `val_wf tyv v` by simp[value_has_type_memory_wf] >>
  `~is_word_type (expr_type e)` by
    (qpat_x_assum `expr_type e = _ \/ _` strip_assume_tac >>
     gvs[is_bytestring_word_type]) >>
  `?sw. eval_operand op s = SOME sw /\
        val_in_memory etv v (w2n sw) s.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `val_in_memory tyv v (w2n sw) s.vs_memory` by
    (qpat_x_assum `expr_type e = _ \/ _` strip_assume_tac >> gvs[] >>
     irule bytestring_val_in_memory_transfer >> metis_tac[]) >>
  `lookup_var p s = SOME w /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz)` by metis_tac[] >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[cj 2 compile_expr_grows] >>
  `not_fresh_at sb p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all annassign_memory_assign_run >>
  disch_then (qspecl_then [`ctx`, `a`] mp_tac) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem annassign_memory_success_run[local]:
  !ctx func cenv cx id vtyp e es es' etv tyv sty sa sb sf op p sz s0 w inst loc info bytes.
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (),es') /\
    ~is_word_type vtyp /\
    (expr_type e = vtyp \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (sty = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!tv es1. eval_expr cx e es = (INL tv,es1) ==>
       ?v. tv = Value v /\ value_has_type tyv v /\
           val_footprint tyv v <= type_memory_bytes cenv sty) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\ cs_extends sa sb /\
    compile_assign_value cenv (Var p) LocMemory op F loc vtyp sty info bytes sb = ((),sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    stmt_state_rel func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var p s0 = SOME w /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv <= sz /\
    type_memory_size tyv + 64 < dimword (:256) ==>
    ?t. stmt_state_rel func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule eval_stmt_annassign_value >> strip_tac >>
  qpat_x_assum `!tv es1. _ ==> _` drule >> strip_tac >>
  qpat_x_assum `sty = _ \/ _` mp_tac >>
  qpat_x_assum `expr_type e = _ \/ _` mp_tac >>
  gvs[read_result_def, return_def] >>
  disch_then assume_tac >> disch_then assume_tac >>
  `not_local_ptr cenv es1.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es1`, `s0`] mp_tac) >>
  impl_tac >- simp[expr_res_ok_def, bind_def, read_result_def, return_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  `lookup_scopes id es1.scopes = NONE` by gvs[] >>
  drule_all annassign_memory_store_post_run >>
  disch_then (qspecl_then [`ctx`, `T`] mp_tac) >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem emit_void_nonterminator_open:
  !opc args sa sb.
    emit_void opc args sa = ((),sb) /\ ~is_terminator opc ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  Cases_on `sa.cs_current_insts` >>
  gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond, mk_inst_def]
QED

Theorem compile_store_memory_same_open[local]:
  !cenv src dst ty sa sb.
    0 < type_memory_bytes cenv ty /\
    compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_store_memory_def] >>
  Cases_on `is_word_type ty`
  >- (simp[] >> strip_tac >> drule emit_void_nonterminator_open >>
      simp[is_terminator_def]) >>
  Cases_on `is_bytestring_type ty`
  >- (simp[compile_store_bytestring_def, comp_bind_def] >> strip_tac >>
      pairarg_tac >> gvs[] >>
      drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  Cases_on `type_memory_bytes cenv ty` >>
  simp[compile_copy_memory_def] >> strip_tac >>
  drule emit_void_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_assign_value_memory_widen_open:
  !cenv dst src loc dty sty info bytes sa sb.
    0 < type_memory_bytes cenv dty /\ (sty = dty \/ is_bytestring_type dty) /\
    compile_assign_value cenv dst LocMemory src F loc dty sty info bytes sa = ((),sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!s d. compile_store_memory cenv s d dty sty =
         compile_store_memory cenv s d dty dty` by
    (rpt gen_tac >> qpat_x_assum `_ \/ _` strip_assume_tac >>
     simp[compile_store_memory_bytestring_src]) >>
  Cases_on `loc = SOME LocMemory`
  >- (gvs[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      drule_all compile_store_memory_same_open >> simp[]) >>
  gvs[compile_assign_value_def] >>
  drule_all compile_store_memory_same_open >> simp[]
QED

Theorem compile_assign_value_memory_same_open:
  !cenv dst src loc ty info bytes sa sb.
    0 < type_memory_bytes cenv ty /\
    compile_assign_value cenv dst LocMemory src F loc ty ty info bytes sa = ((),sb) ==>
    ~block_is_terminated sb
Proof
  rpt strip_tac >>
  drule_at (Pos last) compile_assign_value_memory_widen_open >> simp[]
QED

(* x: T = e for a type T that is not a word type, where e is not the
   empty-value form the lowering stores as a zero length word, and e's
   values have type T.  Either e has type T and is lowered at T, or T is a
   bytestring type and so is e's type: then e's value is widened to T's
   bound (or e is a literal, lowered at its own length), which keeps its
   layout.  The local's buffer is type_memory_bytes of T, the size
   val_in_memory lays a value of T out in, and that size is not 0 (Vyper
   has no empty structs or arrays; the copy then emits an instruction, so
   the block stays open) and leaves the 64 bytes compile_store_memory_run's
   bytestring copy rounds up by below 2 ** 256.  e's values have its
   lowered type too, whose size is type_memory_bytes of it: a value staged
   through a buffer of that size fits. *)
(* Why it holds.  As compile_annassign_stmt_frag: the relation at the
   declared environment c, the local's ALLOCA, then e's fragment, which
   exits on an error or ends in expr_post with e's operand holding its
   value in memory (expr_val_rel at a type that is not a word type, laid
   out as at T: bytestring_val_in_memory_transfer).  When e's value_vv is
   in memory, compile_assign_value allocates a buffer of e's lowered type's
   size (a fresh ALLOCA, whose region misses the live locals' and the new
   local's) and copies the value there (mcopy_val_in_memory, the copy
   covering the value's footprint: annassign_widen_footprint); either way
   compile_store_memory at T then copies it into the local's buffer (for a
   bytestring T the same copy whatever the source's bound;
   compile_store_memory_run, whose address bound needs only the size: its
   bytestring copy needs the length plus 64 below 2 ** 256, its other
   copies the size).  The local's region misses every other live local's
   (local_ptrs_rel_alloca_disjoint), so the writes keep their bytes, and
   local_ptrs_rel_write_local binds the local, as
   stmt_state_rel_declare_store does for one word. *)
Theorem compile_annassign_memory_widen_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es res es' etv tyv ltv.
    eval_stmt cx (AnnAssign id vtyp e) es = (res, es') /\
    cenv.ce_alloca_locals /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (expr_type e = vtyp \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    0 < type_memory_size ltv /\ type_memory_size ltv < dimword (:256) /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              ?v. tv = Value v /\ value_has_type tyv v /\ value_has_type ltv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `!st0 c st1. declare_local cenv id vtyp st0 = (c,st1) ==>
     !a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
              cs_extends a b` by metis_tac[] >>
  drule_all annassign_memory_code_parts >>
  disch_then (qx_choosel_then [`st`, `sA`, `sV`, `sB`, `vv`, `op`, `p`] strip_assume_tac) >>
  rename1 `declare_local cenv id vtyp sa = (c,st)` >>
  qpat_x_assum `!st0 c st1. _ ==> _ /\ _` drule >> strip_tac >>
  `stmt_state_rel func c cx es s0` by
    (irule stmt_state_rel_declare_local_entry >> metis_tac[]) >>
  `not_local_ptr c es.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  `s0.vs_current_bb = st.cs_current_bb /\
   s0.vs_inst_idx = LENGTH st.cs_current_insts` by
    (drule_all declare_local_ptr >> simp[] >> strip_tac >> gvs[]) >>
  `!t. type_memory_bytes c t = type_memory_bytes cenv t` by
    metis_tac[declare_local_memory_types] >>
  `type_memory_bytes cenv vtyp < dimword (:256)` by simp[] >>
  drule_all annassign_alloca_framed_run >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (qx_choosel_then [`salloc`, `w`] strip_assume_tac) >>
  Cases_on `res`
  >- suspend "success" >>
  `(do raw <- eval_expr cx e; read_result cx raw od) es = (INR y,es') /\
   expr_res_ok (INR y : value + exception)` by
    (drule eval_annassign_word_error >> simp[] >>
     disch_then (qspec_then `lctx` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[]
QED

Resume compile_annassign_memory_widen_stmt_frag[success]:
  Cases_on `x` >>
  qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [p] /\
   FLOOKUP salloc.vs_allocas ai.inst_id =
     SOME (w2n w,type_memory_bytes cenv vtyp)` by
    simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  `type_memory_size tyv <= type_memory_bytes cenv vtyp /\
   type_memory_bytes c vtyp = type_memory_size tyv /\
   0 < type_memory_bytes c (lowered_value_type cenv e) /\
   type_memory_bytes c (lowered_value_type cenv e) < dimword (:256)` by simp[] >>
  `!tv es1. eval_expr cx e es = (INL tv,es1) ==>
     ?v. tv = Value v /\ value_has_type tyv v /\
         val_footprint tyv v <= type_memory_bytes c (lowered_value_type cenv e)` by
    (rpt strip_tac >>
     qpat_x_assum `!tv es1. _ ==> ?v. _ /\ _ /\ value_has_type ltv v` drule >>
     strip_tac >> simp[] >>
     `val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)`
       suffices_by simp[] >>
     irule annassign_widen_footprint >> metis_tac[]) >>
  drule_all annassign_memory_success_run >> strip_tac >>
  `!tv es1. eval_expr cx e es = (INL tv,es1) ==> ?v. tv = Value v` by metis_tac[] >>
  drule_all annassign_word_top_ext >> strip_tac >>
  `!x. not_fresh_at sa x ==> x <> p /\ not_fresh_at sA x` by
    (`sA.cs_next_var = st.cs_next_var` by
       (drule emit_inst_extends >> simp[]) >>
     drule declare_local_old_fresh >> simp[] >> simp[not_fresh_at_def]) >>
  disj1_tac >> qexistsl [`t`, `c`] >> simp[stmt_lands_def] >>
  conj_tac >- suspend "open" >>
  rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
    (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func salloc = r /\ _ ==> _`
    drule >> simp[]
QED

Resume compile_annassign_memory_widen_stmt_frag[open]:
  `0 < type_memory_bytes c vtyp` by simp[] >>
  drule_all compile_assign_value_memory_widen_open >> simp[]
QED

Finalise compile_annassign_memory_widen_stmt_frag

(* x: T = e for a type T that is not a word type, where e has type T, is
   lowered at T (lowered_value_type, so not a bytestring literal of another
   length) and is not the empty-value form; the sizes as
   compile_annassign_memory_widen_stmt_frag. *)
Theorem compile_annassign_memory_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es res es' tyv.
    eval_stmt cx (AnnAssign id vtyp e) es = (res, es') /\
    cenv.ce_alloca_locals /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    expr_type e = vtyp /\ lowered_value_type cenv e = vtyp /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              ?v. tv = Value v /\ value_has_type tyv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'
Proof
  rpt strip_tac >> irule compile_annassign_memory_widen_stmt_frag >> gvs[] >>
  metis_tac[]
QED
