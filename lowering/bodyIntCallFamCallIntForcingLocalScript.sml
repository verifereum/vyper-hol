(* Generic forcing with a full frame for original locals. *)
Theory bodyIntCallFamCallIntForcingLocal
Ancestors
  bodyIntCallFamCallIntForcingFrames bodyIntCallForcing bodyIntCallWindowStorage
  bodyIntCallWindowPosts bodyIntCallForcingReadOnly loweringPosts context
  exprSimUnwrap exprSimProps exprLowering compileEnv intCallFrame exprSimAggregateChildren
  finite_map words valueCopy valueEncoding vyperInterpreter vyperState

Theorem intcall_value_forcing_frames:
  unwrap_value ce vv sa = (op,sb) /\ vv_holds ce cx ty r vv es s /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  allocas_above lo s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w a k. eval_operand (vv_operand vv) s = SOME w /\
      a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
      (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
           lookup_var x u = SOME w) /\
    locals_kept ce es s u /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\ vv_at ce cx ty sv sa es r vv s ==>
          expr_val_at ce cx ty sv sb es v op u) /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\ vv_own ce cx ty sv sa es r vv s ==>
          expr_val_own ce cx ty sv sb es v op u) /\
    (!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
      ?w a k. eval_operand op u = SOME w /\ a <= w2n w /\
        w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
        (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  strip_tac >>
  drule_all vv_holds_materialise >> strip_tac >>
  Cases_on `vv`
  >- (drule (SRULE [] protected_identity_value_forcing) >>
      disch_then drule >> simp[] >>
      disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
      qexists_tac `s` >> gvs[locals_kept_def, vv_operand_def] >>
      simp[vv_at_def, vv_own_def]) >>
  rename1 `LocatedValue ann p` >>
  Cases_on `is_word_type ty`
  >- (drule_all protected_word_value_frame_forcing >>
      disch_then (qspec_then `scopes` strip_assume_tac) >>
      `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
       u.vs_alloca_next = s.vs_alloca_next` by
        (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
      qexists_tac `u` >> fs[allocas_above_def, expr_val_at_def, expr_val_own_def] >>
      metis_tac[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule protected_identity_value_forcing >> disch_then drule >>
      simp[] >> disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
      qexists_tac `s` >> gvs[locals_kept_def] >>
      metis_tac[SRULE [] (Q.INST [`vv` |-> `LocatedValue ann p`]
        vv_identity_location)]) >>
  `ann = ty` by fs[vv_holds_def] >> gvs[] >>
  `p.ptr_location <> LocCalldata` by
    (Cases_on `p.ptr_location` >> fs[vv_holds_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by fs[vv_operand_def] >>
  `sa.cs_next_id < sb.cs_next_id` by (drule_all unwrap_materialization_id >> simp[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- suspend "code" >>
  suspend "storage"
QED

Resume intcall_value_forcing_frames[code]:
  mp_tac (Q.INST [`reserved` |-> `reserved`, `Win` |-> `Win`, `P` |-> `P`,
      `scopes` |-> `scopes`, `tv` |-> `tv`, `ty` |-> `ann`]
      (SPEC_ALL intcall_code_forcing_frames)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!name b sz. local_region ce es.scopes u name b sz <=>
      local_region ce es.scopes s name b sz` by
    (irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  mp_tac (Q.INST [`ty` |-> `ann`, `s` |-> `s`, `u` |-> `u`]
    materialized_value_location) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_tac >>
  qexists_tac `u` >> simp[] >>
  conj_tac >- (strip_tac >> qexistsl_tac [`w2n w`, `type_memory_size tv`] >> simp[]) >>
  metis_tac[]
QED

Resume intcall_value_forcing_frames[storage]:
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  mp_tac (Q.INST [`reserved` |-> `reserved`, `Win` |-> `Win`, `P` |-> `P`,
      `scopes` |-> `scopes`, `tv` |-> `tv`, `ty` |-> `ann`]
      (SPEC_ALL intcall_storage_forcing_frames)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!name b sz. local_region ce es.scopes u name b sz <=>
      local_region ce es.scopes s name b sz` by
    (irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  mp_tac (Q.INST [`ty` |-> `ann`, `s` |-> `s`, `u` |-> `u`]
    materialized_value_location) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_tac >>
  qexists_tac `u` >>
  (simp[] >>
   conj_tac >- (strip_tac >> qexistsl_tac [`w2n w`, `type_memory_size tv`] >> simp[]) >>
   first_assum ACCEPT_TAC)
QED

Finalise intcall_value_forcing_frames
