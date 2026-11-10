(* Resource boundaries for allocated argument staging. *)
Theory bodyIntCallFamCallIntAllocatedStage
Ancestors
  bodyIntCallFamCallIntWordStage bodyIntCallFamCallIntAllocationCertificates
  bodyIntCallFamCallIntEntryAllocationBoundary
  bodyIntCallFamCallIntGuardedEffect bodyIntCallFamCallIntStageStore
  valueEncodingProps

val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;
val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;

(* Forcing can write fresh materializations.  Old completed allocations,
   rather than the entire memory, are the frame needed by its consumer. *)
Theorem intcall_completed_prefix_byte_frames:
  ^completed_prefix cx start sa tys flags values ops s /\
  (!i tv. i < LENGTH tys /\ ~EL i flags /\
    evaluate_type (get_tenv cx) (EL i tys) = SOME tv ==> val_wf tv (EL i values)) /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  (!op. MEM op ops ==> eval_operand op u = eval_operand op s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) ==>
  ^completed_prefix cx start sb tys flags values ops u
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> _` drule >> strip_tac >>
  `eval_operand (EL i ops) u = SOME w` by
    metis_tac[listTheory.EL_MEM] >>
  qexistsl_tac [`tv`, `w`] >> simp[] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  Cases_on `EL i flags` >> gvs[] >>
  conj_tac
  >- (irule val_in_memory_mem_agree >> simp[] >>
      qexistsl_tac [`len`, `s.vs_memory`] >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`aid`, `len`] >> simp[] >> metis_tac[]
QED

(* A target-only continuation with allocation byte frames.  Forcing supplies
   the stronger old-allocation frame, without a local-disjointness premise. *)
Theorem intcall_target_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above fp.jc_lo u /\
  (!a k. fp.jc_prot a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
    local_region ce es.scopes s name b sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
  locals_kept ce es s u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sb u` by
    (irule bodyIntCallJointCallCoreTheory.intcall_joint_res_frame >> simp[] >>
     conj_tac
     >- fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
     qexistsl_tac [`es`, `s`, `sa`] >> simp[]) >>
  simp[bodyIntCallJointContractTheory.intcall_expr_cont_def] >> metis_tac[]
QED

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
          ?lb size. fp.jc_staged lb size /\ lb <= off /\
                      off + len <= lb + size))``;
val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

(* Unlike word forcing, this endpoint permits materialization writes, but
   retains every allocation in the completed prefix and the pending suffix. *)
Theorem intcall_stage_forcing_endpoint:
  unwrap_value ce vv sa = (op,sb) /\
  ^deferred fp ce e vv r sa es s /\ post_value_type ce e = expr_type e /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME tv /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ^completed_prefix fp.jc_cx start sa tys flags values ops s /\
  (!i tv. i < LENGTH tys /\ ~EL i flags /\
    evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME tv ==>
    val_wf tv (EL i values)) /\
  ^deferred_list fp ce ds vs rs sa es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    expr_val_rel fp.jc_cx (expr_type e) v op u /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    ^completed_prefix fp.jc_cx start sb tys flags values ops u /\
    ^deferred_list fp ce ds vs rs sb es u /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!x. op = Var x ==> not_fresh_at sb x)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sa`] exprLoweringPropsTheory.ci_mono_unwrap_value) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `!q x. (fp.jc_reserved q \/ MEM q ops) /\ q = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac
     >- fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
     gvs[listTheory.MEM_EL] >>
     qpat_x_assum `!i. i < LENGTH tys ==> _` (qspec_then `n` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `!p k. fp.jc_prot p k ==> p+k <= fp.jc_lo` by
    (qpat_assum `intcall_frame_ok fp`
      (ACCEPT_TAC o CONJUNCT1 o
       REWRITE_RULE [bodyIntCallJointContractTheory.intcall_frame_ok_def])) >>
  qpat_x_assum `?a. _` strip_assume_tac >>
  mp_tac (Q.INST [
    `reserved` |-> `\q. fp.jc_reserved q \/ MEM q ops`,
    `Win` |-> `\b len. ?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len)`,
    `scopes` |-> `es.scopes`, `ty` |-> `expr_type e`]
    (SPEC_ALL bodyIntCallFamCallIntForcingTransportTheory.intcall_value_forcing_list)) >>
  (impl_tac >- (BETA_TAC >> asm_rewrite_tac[] >>
    conj_tac >- gvs[] >>
    conj_tac >- (rpt strip_tac >> qexistsl_tac [`aid`, `p`, `k`] >> simp[]) >>
    gvs[] >> metis_tac[arithmeticTheory.ADD_COMM])) >>
  BETA_TAC >> strip_tac >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (irule intcall_target_cont >> asm_rewrite_tac[] >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> BETA_TAC >> qexists_tac `aid` >> simp[]) >>
     rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `^completed_prefix fp.jc_cx start sb tys flags values ops u` by
    (BETA_TAC >> irule (BETA_RULE intcall_completed_prefix_byte_frames) >>
     asm_rewrite_tac[] >> qexistsl_tac [`s`, `sa`] >>
     asm_rewrite_tac[] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!b len. _ ==> mem_bytes_at b len u.vs_memory = _` irule >>
         BETA_TAC >> qexists_tac `aid` >> asm_rewrite_tac[]) >>
     rpt strip_tac >>
     qpat_x_assum `!q. _ ==> eval_operand q u = _` irule >>
     BETA_TAC >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (drule exprOperandVarTheory.compiler_unwrap_value_var >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  qexists_tac `u` >> gvs[] >> metis_tac[]
QED

(* Allocation leaves every old byte intact, including the caller windows. *)
Theorem intcall_allocation_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above fp.jc_lo u /\
  u.vs_memory = s.vs_memory /\
  (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op u = eval_operand op s) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
    local_region ce es.scopes s name b sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >> irule intcall_target_cont >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!op. _ ==> eval_operand op u = _`
        (qspec_then `Var x` mp_tac) >>
      simp[venomStateTheory.eval_operand_def]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
      rpt strip_tac >> gvs[]) >>
  irule exprSimPropsTheory.locals_kept_mem >> simp[]
QED

Theorem intcall_stage_allocation_endpoint:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ^deferred_list fp ce ds vs rs sa es s /\
  ^completed_prefix fp.jc_cx start sa tys flags values ops s ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    ^deferred_list fp ce ds vs rs sb es u /\
    ^completed_prefix fp.jc_cx start sb tys flags values ops u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = s.vs_memory /\
    sa.cs_next_id < sb.cs_next_id /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s) /\
    (!name lb len. local_region ce es.scopes s name lb len ==>
      regions_disjoint (w2n w) sz lb len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  BETA_TAC >> strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  drule_all (BETA_RULE intcall_stage_allocation_certificates) >> strip_tac >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (irule intcall_allocation_cont >> simp[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val guarded_disjoint = ``\cx ty r vv es s dst len.
  case vv of
    StackValue ann op => (~is_word_type ty ==> !v tv w.
      read_result cx r es = (INL v,es) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w /\
      val_footprint tv v <> 0 ==>
      regions_disjoint (w2n w) (val_footprint tv v) dst len)
  | LocatedValue ann p => (p.ptr_location = LocMemory ==> !v tv w.
      read_result cx r es = (INL v,es) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand p.ptr_operand s = SOME w /\
      val_footprint tv v <> 0 ==>
      regions_disjoint (w2n w) (val_footprint tv v) dst len)``;
val immutable_disjoint = ``\ce cx (es:evaluation_state) dst len.
  ce.ce_is_ctor ==> !name off itv iv.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) dst len``;


(* Initialization frames the origin before allocation, not its fresh slot. *)
Theorem intcall_allocation_store_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es a t /\
  intcall_expr_cont fp ce env es a t es b s /\
  s.vs_memory = t.vs_memory /\ a.cs_next_var <= b.cs_next_var /\
  b.cs_next_var <= c.cs_next_var /\
  (!name off sz. local_region ce es.scopes s name off sz <=>
    local_region ce es.scopes t name off sz) /\
  typed_copy_effect fp.jc_ctx fp.jc_func b c s u dst len /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  (!off sz. fp.jc_prot off sz ==> regions_disjoint off sz dst len) /\
  (!name off sz. local_region ce es.scopes t name off sz ==>
    regions_disjoint off sz dst len) /\
  (!aid off sz. aid < a.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) ==>
    regions_disjoint off sz dst len) ==>
  intcall_expr_cont fp ce env es a t es c u
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es b s` by
    fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
  `local_ptrs_reserved ce b /\ allocas_above fp.jc_lo s` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_allocas] >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule placeMemoryCopyEffectTheory.typed_copy_effect_record >>
     disch_then (mp_tac o Q.AP_TERM `\v. v.vs_alloca_next`) >> simp[]) >>
  `!x. not_fresh_at b x ==> lookup_var x u = lookup_var x s` by
    metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_lookup] >>
  `!name off sz. local_region ce es.scopes u name off sz <=>
    local_region ce es.scopes t name off sz` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  `!off sz. regions_disjoint off sz dst len ==>
    mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz t.vs_memory` by
    (rpt strip_tac >>
     drule_all (REWRITE_RULE [GSYM compileEnvTheory.regions_disjoint_def]
       placeMemoryCopyEffectTheory.typed_copy_effect_bytes) >> simp[]) >>
  `locals_kept ce es t u` by
    (irule exprSimPropsTheory.locals_kept_regions >> metis_tac[]) >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op t` by
    (rpt strip_tac >>
     `eval_operand op u = eval_operand op s` by
       (irule bodyIntCallCopySharpDynamicTheory.typed_copy_effect_operand_preserved >>
        goal_assum (drule_at Any) >>
        fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
        rpt strip_tac >> gvs[]) >>
     fs[bodyIntCallJointContractTheory.intcall_expr_cont_def,
        bodyIntCallJointContractTheory.intcall_expr_res_def]) >>
  drule placeMemoryCopyEffectTheory.typed_copy_effect_endpoint >> strip_tac >>
  irule intcall_target_cont >> simp[] >>
  fs[bodyIntCallJointContractTheory.intcall_expr_cont_def,
     intCallFrameTheory.allocas_above_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem intcall_completed_prefix_allocation_store:
  ^completed_prefix cx start a tys flags values ops t /\
  (!i tv. i < LENGTH tys /\ ~EL i flags /\
    evaluate_type (get_tenv cx) (EL i tys) = SOME tv ==> val_wf tv (EL i values)) /\
  a.cs_next_id <= c.cs_next_id /\ a.cs_next_var <= b.cs_next_var /\
  b.cs_next_var <= c.cs_next_var /\ s.vs_memory = t.vs_memory /\
  t.vs_alloca_next <= s.vs_alloca_next /\
  (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
    eval_operand op s = eval_operand op t) /\
  (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
    FLOOKUP s.vs_allocas aid = SOME entry) /\
  typed_copy_effect ctx func b c s u dst len /\
  (!aid off sz. aid < a.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) ==>
    regions_disjoint off sz dst len) ==>
  ^completed_prefix cx start c tys flags values ops u
Proof
  BETA_TAC >> strip_tac >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_allocas] >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (drule placeMemoryCopyEffectTheory.typed_copy_effect_record >>
     disch_then (mp_tac o Q.AP_TERM `\v. v.vs_alloca_next`) >> simp[]) >>
  `!op. MEM op ops ==> eval_operand op u = eval_operand op t` by
    (rpt strip_tac >>
     `!x. op = Var x ==> not_fresh_at a x` by
       (gvs[listTheory.MEM_EL] >>
        qpat_x_assum `!i. i < LENGTH tys ==> _` (qspec_then `n` mp_tac) >>
        simp[] >> metis_tac[]) >>
     `!x. op = Var x ==> not_fresh_at b x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     `eval_operand op u = eval_operand op s` by
       metis_tac[bodyIntCallCopySharpDynamicTheory.typed_copy_effect_operand_preserved] >>
     metis_tac[]) >>
  irule (BETA_RULE intcall_completed_prefix_byte_frames) >>
  simp[] >> qexistsl_tac [`t`, `a`] >> simp[] >>
  rpt conj_tac
  >~ [`mem_bytes_at _ _ u.vs_memory = _`]
  >- (rpt strip_tac >> rename1 `FLOOKUP t.vs_allocas aid = SOME (off,sz)` >>
      `regions_disjoint off sz dst len` by metis_tac[] >>
      drule_all (REWRITE_RULE [GSYM compileEnvTheory.regions_disjoint_def]
        placeMemoryCopyEffectTheory.typed_copy_effect_bytes) >> simp[]) >>
  gvs[] >> metis_tac[]
QED

(* Equal-layout initialization, preserving certificates at their proper origins. *)
Theorem intcall_equal_store_endpoint:
  compile_store_memory ce src dst ty ty b = ((),c) /\
  (!x. src = Var x ==> not_fresh_at b x) /\
  (!x. dst = Var x ==> not_fresh_at b x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code b c fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es a t /\
  intcall_expr_cont fp ce env es a t es b s /\
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  a.cs_next_var <= b.cs_next_var /\ b.cs_next_var <= c.cs_next_var /\
  s.vs_memory = t.vs_memory /\
  (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
    eval_operand op s = eval_operand op t) /\
  (!name off sz. local_region ce es.scopes s name off sz <=>
    local_region ce es.scopes t name off sz) /\
  (!off sz. fp.jc_prot off sz ==>
    regions_disjoint off sz (w2n dw) (type_memory_size tv)) /\
  (!name off sz. local_region ce es.scopes t name off sz ==>
    regions_disjoint off sz (w2n dw) (type_memory_size tv)) /\
  (!aid off sz. aid < a.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) ==>
    regions_disjoint off sz (w2n dw) (type_memory_size tv)) /\
  ^immutable_disjoint ce fp.jc_cx es (w2n dw) (type_memory_size tv) /\
  ^deferred_list fp ce ds vs rs b es s /\
  (!i. i < LENGTH ds ==>
    ^guarded_disjoint fp.jc_cx (post_value_type ce (EL i ds))
      (EL i rs) (EL i vs) es s (w2n dw) (type_memory_size tv)) /\
  ^completed_prefix fp.jc_cx start a tys flags values ops t /\
  (!i tv. i < LENGTH tys /\ ~EL i flags /\
    evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME tv ==>
    val_wf tv (EL i values)) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,MAX 32 (type_memory_size tv)) /\
  start.cs_next_id <= aid /\ aid < b.cs_next_id /\
  w2n dw + MAX 32 (type_memory_size tv) < dimword (:256) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es a t es c u /\
    ^deferred_list fp ce ds vs rs c es u /\
    ^completed_prefix fp.jc_cx start c (tys ++ [ty]) (flags ++ [F])
      (values ++ [v]) (ops ++ [dst]) u
Proof
  BETA_TAC >> strip_tac >>
  `intcall_expr_res fp ce env es b s /\ ~s.vs_halted /\
   s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts` by
    fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\ local_ptrs_reserved ce b` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `?u. val_in_memory tv v (w2n dw) u.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func b c s u (w2n dw) (type_memory_size tv) /\
    stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u` by
    (irule intcall_stage_store_effect >> simp[] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `intcall_expr_cont fp ce env es a t es c u` by
    (irule intcall_allocation_store_cont >> simp[] >> metis_tac[]) >>
  `!x. not_fresh_at b x ==> lookup_var x u = lookup_var x s` by
    metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_lookup] >>
  `!name off sz. local_region ce es.scopes u name off sz <=>
    local_region ce es.scopes s name off sz` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  `^deferred_list fp ce ds vs rs c es u` by
    (BETA_TAC >> irule (BETA_RULE intcall_deferred_list_guarded_store_effect) >>
     simp[] >> goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
     gvs[] >> metis_tac[]) >>
  `^completed_prefix fp.jc_cx start c tys flags values ops u` by
    (BETA_TAC >> irule (BETA_RULE intcall_completed_prefix_allocation_store) >>
     simp[] >> goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
     fs[bodyIntCallJointContractTheory.intcall_expr_cont_def] >>
     qexistsl_tac [`a`, `t`] >> gvs[] >> metis_tac[]) >>
  `eval_operand dst u = SOME dw` by
    metis_tac[bodyIntCallCopySharpDynamicTheory.typed_copy_effect_operand_preserved] >>
  `u.vs_allocas = s.vs_allocas /\ alloca_inv u` by
    metis_tac[placeMemoryCopyEffectTheory.typed_copy_effect_allocas,
      exprLoweringPropsTheory.stmt_state_rel_def] >>
  `!x. dst = Var x ==> not_fresh_at c x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `^completed_prefix fp.jc_cx start c [ty] [F] [v] [dst] u` by
    (BETA_TAC >> irule (BETA_RULE bodyIntCallFamCallIntStageInterfaceTheory.intcall_completed_memory_singleton) >>
     simp[] >> qexists_tac `aid` >> simp[]) >>
  `^completed_prefix fp.jc_cx start c (tys ++ [ty]) (flags ++ [F])
      (values ++ [v]) (ops ++ [dst]) u` by
    (BETA_TAC >> irule (BETA_RULE intcall_completed_append) >>
     rule_assum_tac BETA_RULE >> gvs[] >> metis_tac[]) >>
  drule placeMemoryCopyEffectTheory.typed_copy_effect_path >> strip_tac >>
  qexists_tac `u` >> rule_assum_tac BETA_RULE >> gvs[]
QED

(* Pending footprints are separated at their pre-allocation origin. *)
Theorem intcall_deferred_allocation_guarded:
  ^deferred fp ce e vv r a es t /\
  stmt_state_rel ctx func ce fp.jc_cx es s /\
  FLOOKUP s.vs_allocas a.cs_next_id = SOME (dst,sz) /\
  (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
    FLOOKUP s.vs_allocas aid = SOME entry) /\
  (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
    eval_operand op s = eval_operand op t) /\
  (!name lb len. local_region ce es.scopes t name lb len ==>
    regions_disjoint dst sz lb len) ==>
  ^guarded_disjoint fp.jc_cx (post_value_type ce e) r vv es s dst sz
Proof
  BETA_TAC >> strip_tac >>
  `eval_operand (vv_operand vv) s = eval_operand (vv_operand vv) t` by
    metis_tac[] >>
  Cases_on `vv` >>
  gvs[contextTheory.vv_operand_def] >> rpt strip_tac >>
  irule bodyIntCallFamCallIntAllocationGeometryTheory.intcall_vv_at_allocation_disjoint >>
  simp[contextTheory.vv_operand_def] >>
  goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`ctx`, `func`, `s`] >>
  simp[contextTheory.vv_operand_def] >> gvs[]
QED

Theorem intcall_allocated_store_endpoint:
  compile_alloc_buffer (MAX 32 (type_memory_size tv)) a = (buf,b) /\
  compile_store_memory ce src buf.buf_operand ty ty b = ((),c) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  expr_val_rel fp.jc_cx ty v src t /\
  fn_has_code a b fp.jc_func /\ fn_has_code b c fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\ intcall_frame_ok fp /\
  intcall_expr_res fp ce env es a t /\ start.cs_next_id <= a.cs_next_id /\
  ^deferred_list fp ce ds vs rs a es t /\
  ^completed_prefix fp.jc_cx start a tys flags values ops t /\
  (!i tv. i < LENGTH tys /\ ~EL i flags /\
    evaluate_type (get_tenv fp.jc_cx) (EL i tys) = SOME tv ==>
    val_wf tv (EL i values)) /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_expr_cont fp ce env es a t es c u /\
    ^deferred_list fp ce ds vs rs c es u /\
    ^completed_prefix fp.jc_cx start c (tys ++ [ty]) (flags ++ [F])
      (values ++ [v]) (ops ++ [buf.buf_operand]) u
Proof
  BETA_TAC >> strip_tac >>
  `MAX 32 (type_memory_size tv) < dimword (:256)` by
    (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  drule_all (BETA_RULE intcall_stage_allocation_endpoint) >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es a t es b s` >>
  suspend "allocation_frame"
QED

Resume intcall_allocated_store_endpoint[allocation_frame]:
  `a.cs_next_id <= b.cs_next_id /\ a.cs_next_var <= b.cs_next_var` by
    (mp_tac (Q.SPECL [`MAX 32 (type_memory_size tv)`,`a`]
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `b.cs_next_id <= c.cs_next_id /\ b.cs_next_var <= c.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`,`src`,`buf.buf_operand`,`ty`,`ty`,`b`]
       exprLoweringPropsTheory.ci_mono_compile_store_memory) >>
     fs[exprLoweringPropsTheory.ci_mono_def,
        bodyIntCallJointContractTheory.intcall_expr_cont_def]) >>
  `local_ptrs_reserved ce a` by
    fs[bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   allocas_above fp.jc_lo s /\
   (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
      FLOOKUP s.vs_allocas aid = SOME entry) /\
   (!name off sz. local_region ce es.scopes s name off sz <=>
      local_region ce es.scopes t name off sz)` by
    (conj_tac
     >- fs[bodyIntCallJointContractTheory.intcall_expr_cont_def,
           bodyIntCallJointContractTheory.intcall_expr_res_def] >>
     conj_tac
     >- fs[bodyIntCallJointContractTheory.intcall_expr_cont_def,
           bodyIntCallJointContractTheory.intcall_expr_res_def] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `intcall_expr_cont _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE
             [bodyIntCallJointContractTheory.intcall_expr_cont_def]) >>
         qpat_x_assum `!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==> _` drule >>
         simp[]) >>
     rpt strip_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `a` >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!op. _ ==> eval_operand op s = _`
       (qspec_then `Var x` mp_tac) >> simp[venomStateTheory.eval_operand_def]) >>
  suspend "allocation_separation"
QED

Resume intcall_allocated_store_endpoint[allocation_separation]:
  `!off sz. fp.jc_prot off sz ==>
    regions_disjoint off sz (w2n w) (type_memory_size tv)` by
    (rpt strip_tac >>
     `off + sz <= fp.jc_lo` by
       fs[bodyIntCallJointContractTheory.intcall_frame_ok_def] >>
     simp[compileEnvTheory.regions_disjoint_def]) >>
  `!name off sz. local_region ce es.scopes t name off sz ==>
    regions_disjoint off sz (w2n w) (type_memory_size tv)` by
    (rpt strip_tac >>
     qpat_x_assum `!name lb len. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[compileEnvTheory.regions_disjoint_def, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!aid off sz. aid < a.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) ==>
    regions_disjoint off sz (w2n w) (MAX 32 (type_memory_size tv))` by
    (rpt strip_tac >> irule intcall_allocation_old_regions >>
     metis_tac[]) >>
  `expr_val_rel fp.jc_cx ty v src s` by
    (irule intcall_expr_val_rel_same_memory >> simp[] >> metis_tac[]) >>
  `?sw. eval_operand src s = SOME sw /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory)` by
    (qpat_assum `expr_val_rel _ _ _ _ s` mp_tac >>
     pure_rewrite_tac[loweringPostsTheory.expr_val_rel_def] >>
     disch_then (qx_choose_then `sw` strip_assume_tac) >>
     qexists_tac `sw` >> simp[]) >>
  `^immutable_disjoint ce fp.jc_cx es (w2n w) (MAX 32 (type_memory_size tv))` by
    (BETA_TAC >> rpt strip_tac >>
     irule bodyIntCallFamCallIntStageAllocationTheory.intcall_stage_allocation_immutable_window >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `!i. i < LENGTH ds ==>
    ^guarded_disjoint fp.jc_cx (post_value_type ce (EL i ds))
      (EL i rs) (EL i vs) es s (w2n w) (MAX 32 (type_memory_size tv))` by
    (BETA_TAC >> rpt strip_tac >> irule (BETA_RULE intcall_deferred_allocation_guarded) >>
     conj_tac >- (qexistsl_tac [`a`, `t`] >> simp[] >> metis_tac[]) >> metis_tac[]) >>
  suspend "store_finish"
QED

Resume intcall_allocated_store_endpoint[store_finish]:
  `!aid off sz. aid < a.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) ==>
    regions_disjoint off sz (w2n w) (type_memory_size tv)` by
    (rpt strip_tac >> irule intcall_regions_disjoint_subwindow >>
     qexistsl_tac [`MAX 32 (type_memory_size tv)`, `w2n w`] >> simp[] >> metis_tac[]) >>
  `^immutable_disjoint ce fp.jc_cx es (w2n w) (type_memory_size tv)` by
    (BETA_TAC >> rpt strip_tac >> irule intcall_regions_disjoint_subwindow >>
     qexistsl_tac [`MAX 32 (type_memory_size tv)`, `w2n w`] >> simp[] >>
     rule_assum_tac BETA_RULE >> metis_tac[]) >>
  `!i. i < LENGTH ds ==>
    ^guarded_disjoint fp.jc_cx (post_value_type ce (EL i ds))
      (EL i rs) (EL i vs) es s (w2n w) (type_memory_size tv)` by
    (BETA_TAC >> rpt strip_tac >> rule_assum_tac BETA_RULE >>
     qpat_x_assum `!i. i < LENGTH ds ==> (case EL i vs of StackValue ax ox => _ | LocatedValue ay px => _)` drule >>
     Cases_on `EL i vs` >> simp[] >> rpt strip_tac >>
     irule intcall_regions_disjoint_subwindow >>
     qexistsl_tac [`MAX 32 (type_memory_size tv)`, `w2n w`] >> simp[] >> metis_tac[]) >>
  `!x. src = Var x ==> not_fresh_at b x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  rule_assum_tac BETA_RULE >>
  `?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es a t es c u /\
    ^deferred_list fp ce ds vs rs c es u /\
    ^completed_prefix fp.jc_cx start c (tys ++ [ty]) (flags ++ [F])
      (values ++ [v]) (ops ++ [buf.buf_operand]) u` by
    (BETA_TAC >> irule (BETA_RULE intcall_equal_store_endpoint) >> simp[] >>
     qexistsl_tac [`a.cs_next_id`, `b`, `src`, `sw`] >>
     gvs[arithmeticTheory.ADD_COMM] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rule_assum_tac BETA_RULE >> qexists_tac `u` >> reverse conj_tac
  >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    fragGasModeTheory.gas_marked_path_then)) >>
  qexists_tac `s` >> simp[]
QED

Finalise intcall_allocated_store_endpoint
