(* Compiler-facing separation for the optional tuple snapshot. *)
Theory assignTuplePtrStage
Ancestors
  assignTuplePtrAllocEndpoint assignTuplePtrCopyEndpoint assignTuplePtrStageFrame allocationPtr localPtrsProps
  typedCopyPtr robustCopyTransportPtr venomMemProofs valueEncodingProps valueEncodingTyping
  exprLoweringProps exprSimProps compileEnv venomState venomInst
  venomExecSemantics loweringHalt finite_map valueEncoding tupleStageProps
  bodyPtrDefs fragGasPathPtr vyperTyping emitHelperProps emitHelper ptrDiscipline localPtrsProps
Libs
  monadsyntax



Theorem optional_tuple_stage_run_ptr:
  !ctx func cenv cx es flag tys tvs vs se sa sb staged op s sw e d D PG G tn.
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
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~ctx_has_dalloca ctx /\ expr_type e = TupleT tys /\
    lowered_value_type cenv e = TupleT tys /\
    ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) op G tn s /\
    ptr_buf_ok cenv e op G s /\ ghost_inv d cenv cx es G tn s /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    tuple_val_wf vs tvs /\ values_have_types tvs vs /\
    ?t w G' tn'. eval_operand staged t = SOME w /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
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
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
      ghost_inv d cenv cx es G' tn' t /\
      ptr_val_ok cx (TupleT tys) (ArrayV (TupleV vs)) staged G' tn' t /\
      ptr_buf_ok cenv e staged G' t /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (flag ==> ?b. FLOOKUP t.vs_allocas sa.cs_next_id =
          SOME (b,type_memory_size_list tvs) /\ w2n w = b /\
        !name entry p sz u. lookup_scopes name es.scopes = SOME entry /\
          FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
          lookup_var p t = SOME u ==>
          w2n u + val_footprint entry.type entry.value <= b \/
          b + type_memory_size_list tvs <= w2n u)
Proof
  rpt gen_tac >> Cases_on `flag`
  >- suspend "copy"
  >> suspend "identity"
QED

Resume optional_tuple_stage_run_ptr[identity]:
  strip_tac >> gvs[comp_return_def] >>
  drule_all expr_tuple_memory_owned >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `values_have_types tvs vs` by
    fs[value_has_type_def] >>
  simp[] >> qexistsl_tac [`s`, `sw`, `G`, `tn`] >>
  simp[] >> conj_tac
  >- metis_tac[arithmeticTheory.ADD_COMM] >>
  simp[Once gas_path_ptr_cases]
QED

Resume optional_tuple_stage_run_ptr[copy]:
  strip_tac >> fs[] >>
  drule_all tuple_stage_copy_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `p`] strip_assume_tac) >>
  `not_local_ptr cenv es.scopes p` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `op <> Var p` by metis_tac[] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> p) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> p)` by
    (conj_tac >> rpt strip_tac >> metis_tac[]) >>
  gvs[] >>
  drule_at (Pat `emit_inst ALLOCA _ _ _ = _`) emit_alloca_endpoint_ptr >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`D`, `PG`]
    (qx_choosel_then [`t`, `b`, `G1`, `tn1`] strip_assume_tac)) >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by
    metis_tac[value_has_type_val_wf] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) m` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def] >> metis_tac[]) >>
  `!m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
       val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) m` by
    (qpat_x_assum `!ty tv se' sa' v op' w. _` drule >>
     simp[is_word_type_def] >> disch_then drule_all >> simp[]) >>
  qpat_x_assum `!ty tv se' sa' v op' w. _` kall_tac >>
  `?q base sz. op = Var q /\ FLOOKUP G q = SOME (base,sz) /\
       base <= w2n sw /\ w2n sw + type_memory_size_list tvs <= base + sz` by
    (qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
     simp[ptr_buf_ok_def] >> disch_then (qspec_then `sw` mp_tac) >>
     simp[]) >>
  gvs[] >>
  `lookup_var q t = SOME sw /\
   ptr_covers G1 tn1 q t (type_memory_size_list tvs)` by
    (fs[ptr_covers_def, ptr_val_ok_def, eval_operand_def] >> metis_tac[]) >>
  suspend "mcopy"
QED

Resume optional_tuple_stage_run_ptr[mcopy]:
  `type_memory_size_list tvs < dimword (:256)` by decide_tac >>
  qpat_assum `emit_void MCOPY _ _ = _` mp_tac >>
  rewrite_tac[GSYM emit_inst_def, emit_void_def] >> strip_tac >>
  `lookup_var p t = SOME (n2w b)` by fs[eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
     [Lit (n2w (type_memory_size_list tvs))] [p]) (fn_insts func)` by
    (qspec_then `sa with cs_next_var := sa.cs_next_var + 1` mp_tac
       emit_inst_fn_member >>
     disch_then drule_all >> simp[]) >>
  `!name entry r sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var r) sz) /\
    lookup_var r t = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= b \/
      b + type_memory_size_list tvs <= w2n w)` by
    (rpt gen_tac >> strip_tac >>
     `local_ptrs_rel func cenv es.scopes t` by
       fs[stmt_state_rel_def, state_rel_def] >>
     `val_wf entry.type entry.value` by
       (fs[local_ptrs_rel_def] >>
        qpat_x_assum `!name entry p sz. _` drule_all >> simp[]) >>
     conj_tac >- simp[] >> metis_tac[]) >>
  `val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def]) >>
  drule_at (Pat `emit_inst MCOPY _ _ _ = _`) emit_allocated_mcopy_endpoint_ptr >>
  disch_then (fn th => qpat_assum `MEM _ (fn_insts func)`
    (mp_then (Pat `MEM inst _`) mp_tac th)) >>
  simp[mk_inst_def] >>
  disch_then (fn th => qpat_assum `FLOOKUP t.vs_allocas sa.cs_next_id = SOME _`
    (mp_then (Pat `FLOOKUP _ _ = SOME _`) mp_tac th)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choosel_then [`G2`, `tn2`] strip_assume_tac)) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G1 tn1 t 0 G2 tn2 (OK u)` >>
  suspend "assemble"
QED

Resume optional_tuple_stage_run_ptr[assemble]:
  `u.vs_allocas = t.vs_allocas /\ ~u.vs_halted` by simp[Abbr `u`] >>
  `eval_operand (Var p) u = SOME (n2w b)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G2 tn2 (OK u)` by
    metis_tac[gas_path_ptr_then, arithmeticTheory.ADD] >>
  `ptr_covers G2 tn2 p u (type_memory_size_list tvs)` by simp[Abbr `u`] >>
  `!m. mem_agree_outside tn2.t_mem u.vs_memory m ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b m` by simp[Abbr `u`] >>
  `tuple_val_wf vs tvs /\ values_have_types tvs vs` by
    fs[val_wf_def, value_has_type_def] >>
  simp[] >> qexistsl_tac [`u`, `n2w b`, `G2`, `tn2`] >>
  simp[] >>
  suspend "resources"
QED

Resume optional_tuple_stage_run_ptr[resources]:
  conj_tac
  >- (qpat_x_assum `!m. mem_agree_outside tn2.t_mem u.vs_memory m ==> _`
        (qspec_then `u.vs_memory` mp_tac) >>
      simp[mem_agree_outside_def, val_in_memory_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[Abbr `u`] >>
  conj_tac >- simp[Abbr `u`] >>
  conj_tac
  >- (qexistsl_tac [`b`, `type_memory_size_list tvs`] >> simp[] >>
      disj1_tac >> qexists `sa.cs_next_id` >> simp[]) >>
  suspend "pointer_resources"
QED

Resume optional_tuple_stage_run_ptr[pointer_resources]:
  conj_tac
  >- (drule val_store_size_le >> simp[type_memory_size_def] >> strip_tac >>
      qpat_x_assum `ptr_covers G2 tn2 p u _` mp_tac >>
      qpat_x_assum `!m. mem_agree_outside tn2.t_mem u.vs_memory m ==> _` mp_tac >>
      qpat_x_assum `eval_operand (Var p) u = SOME _` mp_tac >>
      qpat_x_assum `evaluate_type _ _ = SOME (TupleTV tvs)` mp_tac >>
      qpat_x_assum `val_store_size _ _ <= _` mp_tac >>
      qpat_x_assum `b + type_memory_size_list tvs < _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[ptr_val_ok_def, ptr_mem_ok_def, ptr_covers_def,
           is_word_type_def, op_taint_def, eval_operand_def] >>
      rpt strip_tac >> gvs[] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_LESS_EQ_MONO]) >>
  conj_tac
  >- (qpat_x_assum `ptr_covers G2 tn2 p u _` mp_tac >>
      qpat_x_assum `lowered_value_type cenv e = _` mp_tac >>
      qpat_x_assum `type_memory_bytes cenv (TupleT tys) = _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[ptr_buf_ok_def, ptr_covers_def, eval_operand_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED

Finalise optional_tuple_stage_run_ptr
