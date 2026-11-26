(* Lift the common aggregate Append scratch run over the live memory array.
   The scratch run ends before any guard or write to the target. *)
Theory bodyAppendMemoryScratchMods
Ancestors
  bodyAppendSlotScratchMods assignTuplePtrCopyLen exprLoweringProps
  exprSimCopy exprSimProps robustCopyTransportPtr fragExec freshWrites
  arithmetic finite_map words pair loweringStateRelDefs

Theorem append_memory_scratch_ready_mods:
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  compile_alloc_buffer (type_memory_bytes cenv elem) sm = (tmp,sc) /\
  compile_store_memory cenv (Var xs) tmp.buf_operand elem sty sc = ((),sd) /\
  ~is_word_type sty /\ ~is_word_type elem /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      len = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty elem /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) elem = SOME dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv elem = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  fn_has_code sm sc func /\ fn_has_code sc sd func /\
  local_ptrs_reserved cenv sm /\ fn_inst_ids_distinct func /\
  type_memory_size dtv + 64 < dimword (:256) /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  not_fresh_at sm xs /\ lookup_var xs s = SOME sw /\
  expr_val_at cenv cx sty start sm es v (Var xs) s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  (!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  local_region cenv es.scopes s id (w2n basew) sz /\
  w2n (bp:bytes32) = w2n (basew:bytes32) + k /\
  k + type_memory_size (ArrayTV dtv (Dynamic cap)) <= sz /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem) ==>
  ?z q b Gz tz.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    (!H : (bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es z) /\
    local_ptrs_reserved cenv sd /\
    ~z.vs_halted /\ z.vs_current_bb = sd.cs_current_bb /\
    z.vs_inst_idx = LENGTH sd.cs_current_insts /\
    tmp.buf_operand = Var q /\ not_fresh_at sd q /\
    lookup_var q z = SOME (n2w b) /\ ptr_covers Gz tz q z (type_memory_size dtv) /\
    eval_operand tmp.buf_operand z = SOME (n2w b) /\ op_taint tz tmp.buf_operand = {} /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (b,type_memory_size dtv) /\
    sm.cs_next_id < sd.cs_next_id /\ sm.cs_next_var <= sd.cs_next_var /\
    lo <= b /\ b + type_memory_size dtv < dimword (:256) /\
    b + type_memory_size dtv <= z.vs_alloca_next /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory dtv v b mem) /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem) /\
    local_region cenv es.scopes z id (w2n basew) sz /\
    loweringStateRelDefs$regions_disjoint b (type_memory_size dtv) (w2n basew) sz /\
    allocas_from lo z /\ lo <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ alloca_history func z /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP z.vs_allocas aid = SOME ent) /\
    (!aid off len. FLOOKUP z.vs_allocas aid = SOME (off,len) ==>
      FLOOKUP s.vs_allocas aid = SOME (off,len) \/ s.vs_alloca_next <= off) /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at sm x ==>
      not_fresh_at sd x /\ lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!op. (!x. op = Var x ==> not_fresh_at sm x) ==>
      eval_operand op z = eval_operand op s /\ op_taint tz op = op_taint tn op) /\
    (!x len. not_fresh_at sm x /\ ptr_covers G tn x s len ==> ptr_covers Gz tz x z len) /\
    typed_copy_frame b (type_memory_size dtv) s.vs_memory z.vs_memory /\
    (!i. ~(b <= i /\ i < b + type_memory_size dtv) ==>
      mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tz.t_mem <=> i IN tn.t_mem)) /\
    (!aid off len i. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) /\
      off <= i /\ i < off+len ==> (i IN tz.t_mem <=> i IN tn.t_mem)) /\
    z.vs_data_section = s.vs_data_section /\ z.vs_call_ctx = s.vs_call_ctx /\
    z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
    z.vs_immutables = s.vs_immutables /\ z.vs_labels = s.vs_labels /\
    tz.t_stor = tn.t_stor /\ tz.t_trans = tn.t_trans /\ tz.t_imm = tn.t_imm /\
    (immutable_frame_mods func cenv cx es s ==> immutable_frame_mods func cenv cx es z) /\
    (!D d. ghost_inv_at_mods D lo d cenv cx es G tn s ==>
      ghost_inv_at_mods D lo d cenv cx es Gz tz z) /\
    (!d. return_buf_frame d cenv sm s ==> return_buf_frame d cenv sd z) /\
    alloca_frame cenv es sm s cenv es z /\ ghost_kept_at lo cenv es sm G tn s Gz tz
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`sa` |-> `sm`,`sm` |-> `sc`,`sb` |-> `sd`,
    `buf` |-> `tmp`,`dty` |-> `elem`] (SPEC_ALL append_slot_scratch_ready_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`z`,`q`,`b`,`Gz`,`tz`] strip_assume_tac) >>
  `ci_mono sm sc /\ ci_mono sc sd` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_store_memory, SND] >>
  `ci_mono sm sd` by metis_tac[ci_mono_trans] >>
  `sm.cs_next_var <= sd.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `local_region cenv es.scopes z id (w2n basew) sz` by
    (irule (iffRL copy_buffer_local_region_frame) >> qexistsl_tac [`s`,`sm`] >> simp[]) >>
  qpat_assum `!name off len. local_region cenv _ z _ _ _ ==> _`
    (drule_then assume_tac) >>
  `!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
    val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem` by
    suspend "array" >>
  `!x len. not_fresh_at sm x /\ ptr_covers G tn x s len ==> ptr_covers Gz tz x z len` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  qexistsl_tac [`z`,`q`,`b`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume append_memory_scratch_ready_mods[array]:
  `val_footprint (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) <=
   type_memory_size (ArrayTV dtv (Dynamic cap))` by simp[val_footprint_le] >>
  match_mp_tac robust_val_in_memory_exterior_frame >>
  qexistsl_tac [`tn.t_mem`,`s.vs_memory`,`{i | b <= i /\ i < b + type_memory_size dtv}`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `loweringStateRelDefs$regions_disjoint b _ _ _` mp_tac >>
  pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Finalise append_memory_scratch_ready_mods
