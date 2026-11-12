(* Shared fresh allocation and typed-copy boundary for expressions and returns. *)
Theory exprSimTypedAlloc
Ancestors
  exprSimAlloc exprSimCopy typedMemoryCopy exprLoweringProps loweringPosts venomMemDefs loweringStateRelDefs
  loweringHalt localPtrsProps freshWrites valueEncoding vyperTypeSystem
  list finite_map venomInst venomState fragExec exprSimProps loweringSlice compileEnv exprSimStorageCopy

Theorem typed_return_store_mono:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) ==>
  ci_mono sa sb
Proof
  strip_tac >>
  mp_tac (cj 1 ci_mono_typed_memory_family) >>
  disch_then (qspecl_then [`cenv`, `dst`, `dty`, `src`, `sty`, `sa`] mp_tac) >>
  simp[]
QED

Theorem compile_return_normalize_framed_frag:
  !ctx func cenv cx es ty sty stv dtv v val_op sa sm sb buf s sw R.
    compile_alloc_buffer (type_memory_bytes cenv ty) sa = (buf, sm) /\
    compile_store_memory_typed cenv buf.buf_operand ty val_op sty sm =
      ((), sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty ty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\
    type_memory_bytes cenv ty = type_memory_size dtv /\
    type_memory_size dtv < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    stmt_state_rel ctx func cenv cx es s /\
    eval_operand val_op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    ((?aid b len. aid < sa.cs_next_id /\
                  FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                  b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len) \/
     (?n b len. local_region cenv es.scopes s n b len /\
                b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len)) ==>
    frag_exec ctx sa sb (\z. z = s)
      (\u. ?w. stmt_state_rel ctx func cenv cx es u /\
               eval_operand buf.buf_operand u = SOME w /\
               w2n w + type_memory_size dtv < dimword (:256) /\
               val_in_memory dtv v (w2n w) u.vs_memory /\
               FLOOKUP u.vs_allocas sa.cs_next_id =
                 SOME (w2n w, type_memory_size dtv) /\
               (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
               (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP u.vs_allocas aid = SOME entry) /\
               (!off len. off + len <= w2n w \/
                  w2n w + type_memory_size dtv <= off ==>
                 mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
               (!aid b len. aid < sa.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
               (!name b len. local_region cenv es.scopes s name b len ==>
                 regions_disjoint (w2n w) (type_memory_size dtv) b len)) R
Proof
  rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `cs_extends sa sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    (drule typed_return_store_mono >> simp[ci_mono_def]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  `type_memory_bytes cenv ty < dimword (:256)` by simp[] >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (qpat_x_assum `(?aid b len. _) \/ _` strip_assume_tac
     >- (qpat_x_assum `!aid b len. _` drule_all >>
         simp[regions_disjoint_def] >> decide_tac) >>
     `local_region cenv es.scopes u n b len` by
       (drule_all copy_buffer_local_region_frame >>
        disch_then (qspecl_then [`es.scopes`, `n`, `b`, `len`] mp_tac) >>
        simp[]) >>
     qpat_x_assum `!name b len. _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  ( `!x. val_op = Var x ==> not_fresh_at sm x` by
      (qspecl_then [`type_memory_bytes cenv ty`, `sa`] mp_tac
         ci_mono_compile_alloc_buffer >>
       simp[ci_mono_def] >> strip_tac >>
       metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
    `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
    `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
    `sa.cs_next_var <= sm.cs_next_var` by
      (qspecl_then [`type_memory_bytes cenv ty`, `sa`] mp_tac
         ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
    `local_ptrs_reserved cenv sm` by
      metis_tac[local_ptrs_reserved_next_var] >>
    drule_all buffer_alloc_code >> strip_tac >>
    drule frag_exec_then >> disch_then irule >> simp[] >>
    drule typed_return_store_frag >>
    disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
    disch_then (drule_at (Pat `sfields_tenv_consistent _ _`)) >>
    disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
    disch_then (qspecl_then [`dtv`, `ctx`, `R`,
      `\t. stmt_state_rel ctx func cenv cx es t /\
        (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
          mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)`] mp_tac) >>
    impl_tac
    >- suspend "frame" >>
    suspend "post")
QED

Resume compile_return_normalize_framed_frag[frame]:
        markerLib.RESUME_TAC >> (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
        gen_tac >> strip_tac >> conj_tac
        >- (irule copy_buffer_state_rel_frame >>
        qexistsl_tac [`w2n w`,
          `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
             [STRING #"%" (toString sa.cs_next_var)]`,
          `u`, `sm`, `type_memory_size dtv`] >>
        simp[mk_inst_def] >> conj_tac
        >- (rpt strip_tac >>
            qpat_x_assum `!name b len. _` drule >>
            simp[regions_disjoint_def] >> decide_tac) >>
        rpt strip_tac >> first_x_assum irule >>
        simp[arithmeticTheory.ADD_COMM]) >>
        rpt strip_tac >> first_x_assum irule >> simp[arithmeticTheory.ADD_COMM])
QED

Resume compile_return_normalize_framed_frag[post]:
    markerLib.RESUME_TAC >> (disch_then assume_tac >> drule frag_exec_weaken >>
    disch_then irule >> simp[] >> rpt strip_tac >>
    drule copy_static_fields >> strip_tac >>
    qexists_tac `w` >> simp[] >> conj_tac
    >- (gvs[eval_operand_def] >> first_x_assum irule >> simp[]) >>
    conj_tac
    >- (rpt strip_tac >>
        `not_fresh_at sm x` by
          (irule freshWritesTheory.not_fresh_at_mono >>
           qexists_tac `sa` >> simp[]) >>
        qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >>
        qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
    suspend "retained")
QED

Resume compile_return_normalize_framed_frag[retained]:
  markerLib.RESUME_TAC >> (
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` drule >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name b len. local_region _ _ u _ _ _ ==> _` mp_tac >>
  simp[] >> disch_then irule >>
  qpat_assum `local_ptrs_reserved cenv sa`
    (mp_then Any mp_tac copy_buffer_local_region_frame) >>
  simp[] >> disch_then drule >>
  disch_then (qspecl_then [`es.scopes`, `name`, `b`, `len`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `name` >> simp[])
QED

Finalise compile_return_normalize_framed_frag

Theorem compile_return_normalize_frag:
  !ctx func cenv cx es ty sty stv dtv v val_op sa sm sb buf s sw R.
    compile_alloc_buffer (type_memory_bytes cenv ty) sa = (buf, sm) /\
    compile_store_memory_typed cenv buf.buf_operand ty val_op sty sm =
      ((), sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty ty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\
    type_memory_bytes cenv ty = type_memory_size dtv /\
    type_memory_size dtv < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    stmt_state_rel ctx func cenv cx es s /\
    eval_operand val_op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    ((?aid b len. aid < sa.cs_next_id /\
                  FLOOKUP s.vs_allocas aid = SOME (b,len) /\
                  b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len) \/
     (?n b len. local_region cenv es.scopes s n b len /\
                b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len)) ==>
    frag_exec ctx sa sb (\z. z = s)
      (\u. ?w. stmt_state_rel ctx func cenv cx es u /\
               eval_operand buf.buf_operand u = SOME w /\
               w2n w + type_memory_size dtv < dimword (:256) /\
               val_in_memory dtv v (w2n w) u.vs_memory /\
               FLOOKUP u.vs_allocas sa.cs_next_id =
                 SOME (w2n w, type_memory_size dtv) /\
               (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)) R
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all compile_return_normalize_framed_frag >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_weaken) >>
  simp[] >> disch_then irule >> simp[] >> rpt strip_tac >>
  qexists_tac `w` >> simp[]
QED

(* Shared bound on owned expression memory, also used by Return. *)
Theorem expr_val_at_bound:
  !func cenv cx t sa sb es v op s tv w ctx.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    eval_operand op s = SOME w ==>
    w2n w + val_footprint tv v < dimword (:256)
Proof
  rw[expr_val_at_def] >> first_x_assum (qspec_then `tv` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  TRY (simp[wordsTheory.w2n_lt] >> NO_TAC) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[])
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
     local_region_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED
