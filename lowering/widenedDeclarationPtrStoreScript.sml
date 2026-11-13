(* A layout-changing store initializes the declaration's fresh allocation. *)
Theory widenedDeclarationPtrStore
Ancestors widenedAssignPtrCopyRecursive aggregateStorePtr aggregateStorePtrFrame annAssignPtrMemoryAssign
  annAssignPtrDestinationFrame annAssignPtrBytestring annAssignPtrExterior
  annAssignPtrStore exprSimAggregateChildren exprSimAggregates typedMemoryCopy
  bodyPtrDefs loweringStateRelDefs exprLoweringProps localPtrsProps stmtFragPtr compileEnv
  ptrDiscipline venomState venomInst venomExecSemantics venomMemDefs valueEncodingDefs
  valueEncodingProps valueTypingMemoryProps context finite_map words arithmetic pred_set

Theorem widened_declaration_store_ptr:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\ ~is_word_type dty /\
  ~is_bytestring_type dty /\ dty <> sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  compile_store_memory ce src (Var p) dty sty sa = ((),sb) /\
  not_fresh_at sa p /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  lookup_var p s = SOME dw /\ eval_operand src s = SOME sw /\
  op_taint tn (Var p) = {} /\ op_taint tn src = {} /\
  ptr_covers G tn p s cap /\ type_memory_size dtv <= cap /\
  (0 < type_memory_size stv ==>
    ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size stv)) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  (w2n dw + type_memory_size dtv <= w2n sw \/
   w2n sw + type_memory_size stv <= w2n dw) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n sw) m) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  ghost_kept ce es fr G0 tn0 s0 G tn /\ local_ptrs_reserved ce sa /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  fr.cs_next_var <= sa.cs_next_var /\ fr.cs_next_id <= inst.inst_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,cap) /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
    FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!name b n. local_region ce es.scopes s0 name b n ==>
    local_region ce es.scopes s name b n) /\
  not_local_ptr ce es.scopes p /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) ==>
  ?H tm t.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func ce cx
      (es with scopes := (sc |+ (id,<|assignable := T; type := dtv;
        value := v; popped := []|>)) :: rest) t /\
    ghost_inv d ce cx
      (es with scopes := (sc |+ (id,<|assignable := T; type := dtv;
        value := v; popped := []|>)) :: rest) H tm t /\
    ghost_kept ce es fr G0 tn0 s0 H tm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `0 < type_memory_size dtv ==> ptr_covers G tn p s (type_memory_size dtv)` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_MONO_ADD_EQ]) >>
  mp_tac (Q.SPECL [`ce`,`get_tenv cx`,`ctx`,`cx_dead cx`,`PG`,
    `dty`,`sty`,`dtv`,`stv`,`v`] compile_store_memory_aggregate_counted_ptr) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`sa`,`sb`,`p`,`src`,`dw`,`sw`,`func`,`G`,`tn`,`s`]
    mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_path_ptr _ _ _ _ _ G tn s _ H tm (OK t)` >>
  `!name b n. local_region ce es.scopes s name b n ==>
    regions_disjoint (w2n dw) (type_memory_size dtv) b n` by
    (`alloca_inv s /\ local_ptrs_rel func ce es.scopes s` by
       fs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)` by
    (rpt strip_tac >> drule_all aggregate_alloca_immutable_sep >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx es t` by
    (mp_tac (Q.INST [`ctx` |-> `ctx`, `func` |-> `func`, `ce` |-> `ce`,
      `cx` |-> `cx`, `es` |-> `es`, `sa` |-> `sa`, `s` |-> `s`,
      `q` |-> `t`, `dst` |-> `w2n (dw:256 word)`, `n` |-> `type_memory_size dtv`]
      (SPEC_ALL aggregate_store_control_frame)) >>
     (impl_tac >- (fs[typed_copy_state_frame_def, typed_copy_frame_def,
       loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[])) >> simp[]) >>
  `ghost_inv d ce cx es H tm t` by
    (mp_tac (Q.INST [`d` |-> `d`, `ce` |-> `ce`, `cx` |-> `cx`,
      `es` |-> `es`, `ctx` |-> `ctx`, `func` |-> `func`, `sa` |-> `sa`,
      `G` |-> `G`, `tn` |-> `tn`, `s` |-> `s`, `t` |-> `t`,
      `H` |-> `H`, `tm` |-> `tm`, `b` |-> `w2n (dw:256 word)`,
      `k` |-> `type_memory_size dtv`] (SPEC_ALL literal_typed_copy_ghost_frame)) >>
     fs[] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (fs[typed_copy_state_frame_def] >> qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `ptr_covers H tm p t cap /\ lookup_var p t = SOME dw` by
    (conj_tac
     >- (irule annassign_ptr_covers_frame_ptr >>
         qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `!aid off nsz i. FLOOKUP s0.vs_allocas aid = SOME (off,nsz) /\
    aid < fr.cs_next_id /\ off <= i /\ i < off+nsz ==>
    ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv)` by
    (mp_tac (Q.SPECL [`s`,`s0`,`fr`,`inst`,`w2n (dw:256 word)`,`cap`,
       `type_memory_size dtv`] annassign_alloca_window_excludes_older_ptr) >> simp[]) >>
  `!name b n i. local_region ce es.scopes s0 name b n /\
    b <= i /\ i < b+n ==>
    ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv)` by
    (rpt strip_tac >>
     `local_region ce es.scopes s name b n` by metis_tac[] >>
     qpat_x_assum `!name b n. local_region ce es.scopes s name b n ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!x. not_fresh_at fr x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >>
     metis_tac[]) >>
  `ghost_kept ce es fr G0 tn0 s0 H tm` by
    (irule annassign_ghost_kept_vars_exterior_ptr >>
     qexistsl_tac [`G`,`tn`,
       `{i | w2n dw <= i /\ i < w2n dw + type_memory_size dtv}`] >>
     CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`H`,`tm`,`t`] >> simp[] >> conj_tac
  >- (mp_tac (Q.INST [`cenv` |-> `ce`, `s` |-> `t`, `sz` |-> `cap`,
        `w` |-> `dw`, `tv` |-> `dtv`, `assignable` |-> `T`]
        (SPEC_ALL annassign_memory_scope_state_ptr)) >>
      (impl_tac >- (simp[] >>
        qpat_x_assum `!m. mem_agree_outside tm.t_mem t.vs_memory m ==> _`
          (qspec_then `t.vs_memory` mp_tac) >>
        simp[mem_agree_outside_def])) >> simp[]) >>
  mp_tac (Q.SPECL [`d`,`ce`,`cx`,`es`,`H`,`tm`,`t`,`sc`,`rest`,`id`,
    `<|assignable := T; type := dtv; value := v; popped := []|>`,`p`,`cap`]
    annassign_ghost_scope_update_ptr) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED
