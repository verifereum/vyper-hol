(* Endpoint transport uses actual value footprints, not W capacities. *)
Theory bodyIntCallFamCallIntTransport
Ancestors
  bodyIntCallJointCallCore loweringPosts context exprSimProps
  exprSimAggregateChildren exprSimConvert bodyIntCallFamCallIntCertificates

Theorem intcall_value_holds_endpoint:
  vv_holds ce cx ty r vv es s /\ vv_at ce cx ty a b es r vv s /\
  vv_storage_live cx vv es s /\ stmt_state_rel ctx func ce cx es u /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (case vv of
     StackValue ann op => (~is_word_type ty ==> !v tv w.
       read_result cx r es = (INL v,es) /\
       evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w ==>
       mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory)
   | LocatedValue ann p => (p.ptr_location = LocMemory ==> !v tv w.
       read_result cx r es = (INL v,es) /\
       evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand p.ptr_operand s = SOME w ==>
       mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory)) /\
  (ce.ce_is_ctor ==> !name off itv iv.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    mem_bytes_at off (type_memory_size itv) u.vs_memory =
    mem_bytes_at off (type_memory_size itv) s.vs_memory) ==>
  vv_holds ce cx ty r vv es u
Proof
  Cases_on `vv` >> simp[vv_operand_def] >> strip_tac
  >- (irule intcall_stack_vv_holds_frame >> qexistsl [`es`, `s`] >> simp[] >>
      rpt strip_tac >> fs[vv_at_def, expr_val_at_def] >> metis_tac[]) >>
  Cases_on `p.ptr_location`
  >- (irule intcall_memory_vv_holds_frame >> simp[] >> qexistsl [`es`, `s`] >> simp[] >>
      conj_tac
      >- (rpt strip_tac >> fs[vv_at_def] >> metis_tac[]) >>
      rpt strip_tac >>
      `?v. read_result cx r es = (INL v,es)` by fs[vv_holds_def] >>
      `val_footprint tv v = 32` by
        (drule_all word_tv_memory_size >> strip_tac >>
         `~is_bytestring_type ty` by metis_tac[is_word_type_not_bytestring] >>
         metis_tac[evaluated_nonbytes_footprint]) >>
      gvs[] >> metis_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes])
  >- (irule intcall_storage_vv_holds_frame >> simp[] >>
      conj_tac >- metis_tac[] >>
      qexistsl [`es`, `s`] >> simp[vv_storage_live_def])
  >- (irule intcall_storage_vv_holds_frame >> simp[] >>
      conj_tac >- metis_tac[] >>
      qexistsl [`es`, `s`] >> simp[vv_storage_live_def])
  >- (fs[vv_holds_def] >>
      irule intcall_immutable_holds_frame >> qexistsl [`es`, `s`] >> simp[] >>
      metis_tac[])
  >> fs[vv_holds_def]
QED

(* ML-only abbreviations, identical to the deferred certificate interface. *)
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

val footprint_frame = ``\cx ty r vv es s u.
  case vv of
    StackValue ann op => (~is_word_type ty ==> !v tv w.
      read_result cx r es = (INL v,es) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w ==>
      mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory)
  | LocatedValue ann p => (p.ptr_location = LocMemory ==> !v tv w.
      read_result cx r es = (INL v,es) /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand p.ptr_operand s = SOME w ==>
      mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory)``;

val immutable_frame = ``\ce cx (es:evaluation_state) s u.
  ce.ce_is_ctor ==> !name off itv iv.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    mem_bytes_at off (type_memory_size itv) u.vs_memory =
    mem_bytes_at off (type_memory_size itv) s.vs_memory``;

Theorem intcall_deferred_endpoint:
  ^deferred fp ce e vv r b es s /\
  b.cs_next_id <= d.cs_next_id /\ b.cs_next_var <= d.cs_next_var /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!aid q. FLOOKUP s.vs_allocas aid = SOME q ==> FLOOKUP u.vs_allocas aid = SOME q) /\
  (!n off sz. local_region ce es.scopes u n off sz <=>
              local_region ce es.scopes s n off sz) /\
  ^footprint_frame fp.jc_cx (post_value_type ce e) r vv es s u /\
  ^immutable_frame ce fp.jc_cx es s u ==>
  ^deferred fp ce e vv r d es u
Proof
  BETA_TAC >> strip_tac >> qexists `a` >>
  conj_tac >- (irule intcall_value_holds_endpoint >>
    conj_tac >- (qexistsl [`fp.jc_ctx`, `fp.jc_func`] >> simp[]) >>
    qexistsl [`a`, `b`, `s`] >> simp[] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (irule intcall_vv_at_frame >> metis_tac[]) >>
  conj_tac >- (strip_tac >> irule intcall_vv_own_frame >> metis_tac[]) >>
  conj_tac >- (irule intcall_vv_storage_live_frame >> metis_tac[]) >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED

val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

Theorem intcall_deferred_list_endpoint:
  ^deferred_list fp ce ds vs rs b es s /\
  b.cs_next_id <= d.cs_next_id /\ b.cs_next_var <= d.cs_next_var /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  (!i. i < LENGTH ds ==>
    eval_operand (vv_operand (EL i vs)) u = eval_operand (vv_operand (EL i vs)) s) /\
  (!aid q. FLOOKUP s.vs_allocas aid = SOME q ==> FLOOKUP u.vs_allocas aid = SOME q) /\
  (!n off sz. local_region ce es.scopes u n off sz <=>
              local_region ce es.scopes s n off sz) /\
  (!i. i < LENGTH ds ==>
    ^footprint_frame fp.jc_cx (post_value_type ce (EL i ds)) (EL i rs) (EL i vs) es s u) /\
  ^immutable_frame ce fp.jc_cx es s u ==>
  ^deferred_list fp ce ds vs rs d es u
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  irule (BETA_RULE intcall_deferred_endpoint) >>
  conj_tac
  >- (qexistsl [`b`, `s`] >> simp[] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
