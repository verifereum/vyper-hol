(* Consumer-side transport: actual footprints and exact immutable bytes. *)
Theory bodyIntCallFamCallIntForcingTransport
Ancestors
  bodyIntCallFamCallIntFootprintFrame bodyIntCallFamCallIntImmutableFrame
  bodyIntCallFamCallIntForcingLocal bodyIntCallFamCallIntTransport freshWrites

val deferred = ``\fp ce e vv r b es s.
  ?a. vv_holds ce fp.jc_cx (post_value_type ce e) r vv es s /\
    vv_at ce fp.jc_cx (post_value_type ce e) a b es r vv s /\
    (post_value_type ce e <> expr_type e ==>
      vv_own ce fp.jc_cx (post_value_type ce e) a b es r vv s) /\
    vv_storage_live fp.jc_cx vv es s /\
    (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
    (post_value_type ce e <> NoneT /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) /\
     (case vv of StackValue _ _ => T
               | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?w off len. eval_operand (vv_operand vv) s = SOME w /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
         off + len < dimword (:256) /\
         (fp.jc_lo <= off \/
          ?base size. fp.jc_staged base size /\ base <= off /\
                      off + len <= base + size))``;

val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

val immutable_frame = ``\ce cx (es:evaluation_state) s u.
  ce.ce_is_ctor ==> !name off itv iv.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    mem_bytes_at off (type_memory_size itv) u.vs_memory =
    mem_bytes_at off (type_memory_size itv) s.vs_memory``;

Theorem intcall_deferred_list_byte_frames:
  ^deferred_list fp ce ds vs rs sa es s /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  (!i. i < LENGTH ds ==>
    eval_operand (vv_operand (EL i vs)) u = eval_operand (vv_operand (EL i vs)) s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
    local_region ce es.scopes s name b sz) /\
  (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
  (!name b len. local_region ce es.scopes s name b len ==>
    mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
  ^immutable_frame ce fp.jc_cx es s u ==>
  ^deferred_list fp ce ds vs rs sb es u
Proof
  BETA_TAC >> strip_tac >> irule (BETA_RULE intcall_deferred_list_endpoint) >>
  simp[] >> qexistsl_tac [`sa`, `s`] >>
  gvs[] >> reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!i. _ ==> ?a. _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  irule intcall_vv_at_footprint_frame >>
  qexistsl_tac [`a`, `sa`, `ce`, `sa`] >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* Retain the materializer's single endpoint, including its write envelope. *)
val material_post = ``\fp ce ty v op sa sb es s reserved u w.
  gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
  expr_val_rel fp.jc_cx ty v op u /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  eval_operand op u = SOME w /\
  val_wf tv v /\ val_in_memory tv v (w2n w) u.vs_memory /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
  fp.jc_lo <= w2n w /\ w2n w + type_memory_size tv < dimword (:256) /\
  allocas_above fp.jc_lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!p k. fp.jc_prot p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
  (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
  (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
    local_region ce es.scopes s name b sz) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    regions_disjoint (w2n w) (type_memory_size tv) b sz) /\
  locals_kept ce es s u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!p k. regions_disjoint p k (w2n w) (type_memory_size tv) ==>
    mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory)``;

Theorem intcall_materializing_forcing_list:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\
  (p.ptr_location = LocCode \/ p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  vv_holds ce fp.jc_cx ty (Value v) (LocatedValue ty p) es s /\
  ~is_word_type ty /\ evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\ local_ptrs_reserved ce sa /\
  allocas_above fp.jc_lo s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. fp.jc_prot p k ==> p+k <= fp.jc_lo) /\
  ^deferred_list fp ce ds vs rs sa es s /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. ^material_post fp ce ty v op sa sb es s reserved u w /\
    ^deferred_list fp ce ds vs rs sb es u
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!q x. (reserved q \/ MEM q (MAP vv_operand vs)) /\ q = Var x ==>
    not_fresh_at sa x` by
    (rpt strip_tac >- metis_tac[] >>
     gvs[listTheory.MEM_MAP, listTheory.MEM_EL] >>
     qpat_x_assum `!i. _ ==> ?a. _` (qspec_then `n` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `?u w. ^material_post fp ce ty v op sa sb es s
      (\q. reserved q \/ MEM q (MAP vv_operand vs)) u w` by
    (Cases_on `p.ptr_location = LocCode`
     >- suspend "code"
     >> suspend "storage") >>
  `?inst. MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id` by
    (Cases_on `p.ptr_location = LocCode`
     >- metis_tac[intcall_code_unwrap_alloca]
     >> metis_tac[intcall_storage_unwrap_alloca]) >>
  `^immutable_frame ce fp.jc_cx es s u` by
    (gvs[] >>
     qpat_assum `!p k. regions_disjoint p k (w2n w) _ ==> _`
       (mp_then Any (fn th1 =>
         qpat_assum `stmt_state_rel _ _ _ _ _ u`
           (mp_then Any (fn th2 =>
             qpat_assum `MEM inst (fn_insts _)`
               (mp_then Any mp_tac th2)) th1))
         intcall_allocated_write_immutable_frame) >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     qexistsl_tac [`iv`, `name`] >> simp[]) >>
  gvs[] >>
  `^deferred_list fp ce ds vs rs sb es u` by
    (BETA_TAC >> irule (BETA_RULE intcall_deferred_list_byte_frames) >>
     simp[] >> qexistsl_tac [`s`, `sa`] >> gvs[] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _`
           (qspec_then `name` mp_tac) >> simp[]) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!aid b len. _ /\ _ ==> _` irule >>
         qexists_tac `aid` >> simp[]) >>
     conj_tac
     >- (rpt strip_tac >>
         `MEM (vv_operand (EL i vs)) (MAP vv_operand vs)` by
           (simp[listTheory.MEM_MAP] >> qexists_tac `EL i vs` >>
            simp[listTheory.EL_MEM]) >>
         qpat_x_assum `!q. _ ==> eval_operand q u = _`
           (qspec_then `vv_operand (EL i vs)` mp_tac) >> simp[]) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     qexistsl_tac [`iv`, `name`] >> simp[]) >>
  qexistsl_tac [`u`, `w`] >> gvs[] >> metis_tac[]
QED

Resume intcall_materializing_forcing_list[code]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.INST [`reserved` |-> `\q. reserved q \/ MEM q (MAP vv_operand vs)`,
    `Win` |-> `\b len. ?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len)`,
    `P` |-> `fp.jc_prot`, `lo` |-> `fp.jc_lo`, `scopes` |-> `es.scopes`,
    `cx` |-> `fp.jc_cx`, `func` |-> `fp.jc_func`, `ctx` |-> `fp.jc_ctx`]
    (SPEC_ALL bodyIntCallFamCallIntForcingFramesTheory.intcall_code_forcing_frames)) >>
  (impl_tac >-
    (simp[] >> conj_tac >- (gvs[]) >>
     rpt strip_tac >>
     qexists_tac `aid` >>
     goal_assum (drule_at Any) >> simp[])) >>
  BETA_TAC >> strip_tac >> qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED

Resume intcall_materializing_forcing_list[storage]:
  markerLib.RESUME_TAC >> gvs[] >>
  mp_tac (Q.INST [`reserved` |-> `\q. reserved q \/ MEM q (MAP vv_operand vs)`,
    `Win` |-> `\b len. ?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len)`,
    `P` |-> `fp.jc_prot`, `lo` |-> `fp.jc_lo`, `scopes` |-> `es.scopes`,
    `cx` |-> `fp.jc_cx`, `func` |-> `fp.jc_func`, `ctx` |-> `fp.jc_ctx`]
    (SPEC_ALL bodyIntCallFamCallIntForcingFramesTheory.intcall_storage_forcing_frames)) >>
  (impl_tac >-
    (simp[] >> conj_tac >- (gvs[]) >>
     rpt strip_tac >>
     qexists_tac `aid` >>
     goal_assum (drule_at Any) >> simp[])) >>
  BETA_TAC >> strip_tac >> qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED

Finalise intcall_materializing_forcing_list
