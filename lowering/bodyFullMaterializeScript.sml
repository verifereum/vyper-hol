(*
 * compile_materialize_vv of a non-word stack value on the joint path: a
 * fresh buffer, then the value copied into it.  This is the save step of a
 * Log argument (compile_log_save_arg) when later arguments may write memory.
 *
 * TOP-LEVEL:
 *   materialize_stack_origin_ptr_path - the save as one joint path; the
 *     copy holds the value robustly, in a buffer disjoint from older sites
 *     and locals, with the frames the callers rebuild their ghosts from
 *)
Theory bodyFullMaterialize
Ancestors
  bodyFullAllocaFresh logStoreDataOriginPtr placeStoreDynPrepare ptrDiscipline
  bodyPtrStructLitMonotoneRepresentation typedCopyAppend typedStoreCode
  exprSimAlloc exprSimProps fragGasOriginPtr fragExec loweringHalt
  typedMemoryCopy bodyPtrDefs loweringStateRelDefs loweringShapeDefs
  vyperTypeArgFits exprLoweringProps exprLowering emitHelper context
  compileEnv venomState

(* Helper: the save's two compile steps. *)
Theorem materialize_stack_code[local]:
  compile_materialize_vv cenv ty (StackValue ty src) sa = (op,sb) ==>
  ?buf sm. compile_alloc_buffer (type_memory_bytes cenv ty) sa = (buf,sm) /\
           compile_store_memory cenv src buf.buf_operand ty ty sm = ((),sb) /\
           op = buf.buf_operand /\
           buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
           sa.cs_next_var <= sm.cs_next_var /\
           sm.cs_next_var <= sb.cs_next_var /\
           cs_extends sa sm /\ cs_extends sm sb
Proof
  simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, unwrap_value_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `compile_store_memory _ _ _ _ _ sm = (u,sb)` >>
  Cases_on `u` >> simp[] >>
  `buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
   sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  simp[] >>
  conj_tac >- (drule compile_store_memory_next_var >> simp[]) >>
  conj_tac >- (drule compile_alloc_buffer_extends >> simp[]) >>
  mp_tac (Q.SPECL [`cenv`, `src`, `buf.buf_operand`, `ty`, `ty`]
            cs_appends_compile_store_memory) >>
  simp[cs_appends_def] >> metis_tac[]
QED

(* TOP-LEVEL: a non-word stack value saved into a fresh buffer. *)
Theorem materialize_stack_origin_ptr_path:
  compile_materialize_vv cenv ty (StackValue ty (Var xs)) sa = (op,sb) /\
  ~is_word_type ty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  (type_memory_size tv = 0 \/
   w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (!b len. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,len) ==>
           regions_disjoint (w2n sw) (type_memory_size tv) b len) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q w t G' tn'.
    op = Var q /\ not_fresh_at sb q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
          stmt_state_rel H' ctx func cenv cx es t) /\
    allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    lookup_var q t = SOME w /\ ptr_covers G' tn' q t (type_memory_size tv) /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
           val_in_memory tv v (w2n w) mem) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    w2n w + type_memory_size tv < dimword (:256) /\
    w2n w + type_memory_size tv <= t.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
             FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sa.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
                  regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    (!a len. a + len <= w2n w \/ w2n w + type_memory_size tv <= a ==>
             mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!i. i IN tn'.t_mem /\
         ~(s.vs_alloca_next <= i /\ i < w2n w + type_memory_size tv) /\
         ~(w2n w <= i /\ i < w2n w + type_memory_size tv) ==>
         i IN tn.t_mem) /\
    (!x. not_fresh_at sa x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule materialize_stack_code >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `compile_alloc_buffer (type_memory_size tv) sa = (buf,sm)` by metis_tac[] >>
  mp_tac (Q.INST [`n` |-> `type_memory_size tv`, `sb` |-> `sm`]
            alloc_buffer_origin_ptr_path) >>
  impl_tac >- simp[] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  rename1 `gas_origin_ptr_path _ (s,G,tn) [] (OK u,G1,tn1)` >>
  rename1 `lookup_var q u = SOME w` >>
  `not_fresh_at sm xs` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `u.vs_memory = s.vs_memory /\ u.vs_halted = s.vs_halted` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `~u.vs_halted` by fs[] >>
  `lookup_var xs u = SOME sw` by metis_tac[] >>
  `val_footprint tv v <= type_memory_size tv` by
    (irule val_footprint_le >> first_assum ACCEPT_TAC) >>
  `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem` by
    (qspecl_then [`tv`, `v`, `w2n sw`, `w2n sw`, `val_footprint tv v`,
                  `tn.t_mem`, `tn1.t_mem`, `s.vs_memory`, `u.vs_memory`]
       mp_tac robust_val_in_memory_copy_transport_mono >>
     impl_tac >- (simp[] >> rpt strip_tac >> gvs[] >> decide_tac) >>
     simp[]) >>
  `ptr_covers G1 tn1 xs u (type_memory_size tv)` by
    (qpat_x_assum `ptr_covers G tn xs s _` mp_tac >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  `regions_disjoint (w2n sw) (type_memory_size tv) (w2n w)
     (type_memory_size tv)` by
    (Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id =
               SOME (w2n w,type_memory_size tv)`
     >- (qpat_x_assum `!b len. FLOOKUP s.vs_allocas sa.cs_next_id = _ ==> _`
           (qspecl_then [`w2n w`, `type_memory_size tv`] mp_tac) >>
         simp[]) >>
     `s.vs_alloca_next <= w2n w` by fs[] >>
     qpat_x_assum `type_memory_size tv = 0 \/ _` mp_tac >>
     simp[regions_disjoint_def] >> strip_tac >> simp[] >> decide_tac) >>
  `compile_store_memory cenv (Var xs) (Var q) ty ty sm = ((),sb)` by
    metis_tac[] >>
  mp_tac (Q.INST [`s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`, `sa` |-> `sm`,
                  `xd` |-> `q`, `dw` |-> `w`, `dty` |-> `ty`, `sty` |-> `ty`,
                  `dtv` |-> `tv`, `stv` |-> `tv`]
            compile_store_memory_origin_ptr_path) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >~ [`w2n sw + _ <= w2n w \/ _`]
      >- (qpat_x_assum `regions_disjoint (w2n sw) _ _ _` mp_tac >>
          rewrite_tac[regions_disjoint_def])
      >> simp[] >> decide_tac) >>
  strip_tac >>
  qexistsl_tac [`q`, `w`, `t`, `Gf`, `tnf`] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ u t` mp_tac >>
     rewrite_tac[typed_copy_state_frame_def] >> strip_tac >>
     qpat_x_assum `t with <| vs_vars := _; vs_memory := _; vs_prev_bb := _;
                           vs_current_bb := _; vs_inst_idx := _ |> = u`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `(!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u) /\
   (!a len. a + len <= w2n w \/ w2n w + type_memory_size tv <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory)` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ u t` mp_tac >>
     rewrite_tac[typed_copy_state_frame_def, typed_copy_frame_def] >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b len. local_region cenv es.scopes t name b len <=>
                local_region cenv es.scopes u name b len` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     metis_tac[local_ptrs_reserved_def]) >>
  `q = STRING #"%" (toString sa.cs_next_var)` by fs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [q])
     (fn_insts func)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  conj_tac
  >- (gen_tac >>
      mp_tac (Q.SPECL [`(D,lo,explicit,ctx,func,PG)`, `(s,G,tn)`, `[]`,
                       `(OK u,G1,tn1)`] gas_origin_ptr_path_append) >>
      simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `stmt_state_rel H' ctx func cenv cx es u` by metis_tac[] >>
      drule_at (Pos hd)
        (Q.INST [`sa` |-> `sm`,
                 `dst` |-> `w2n (w:256 word)`, `len` |-> `type_memory_size tv`,
                 `alloc_sz` |-> `type_memory_size tv`,
                 `inst` |-> `mk_inst sa.cs_next_id ALLOCA
                               [Lit (n2w (type_memory_size tv))] [q]`]
           place_typed_copy_alloca_state_frame) >>
      disch_then irule >>
      qexistsl_tac [`q`, `sa`, `sm`, `tv`, `w`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[venomInstTheory.mk_inst_def]) >>
  conj_tac
  >- (qpat_x_assum `allocas_from lo u` mp_tac >> simp[allocas_from_def]) >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_x_assum `ptr_covers G1 tn1 q u _` mp_tac >>
      simp[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >> `i IN tn1.t_mem` by metis_tac[] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED
