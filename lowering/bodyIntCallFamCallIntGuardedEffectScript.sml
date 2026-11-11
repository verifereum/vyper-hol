(* Pending stores need separation only of nonempty actual footprints. *)
Theory bodyIntCallFamCallIntGuardedEffect
Ancestors
  bodyIntCallFamCallIntTransport placeMemoryCopyEffect bodyIntCallCopySharpDynamic

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

Theorem intcall_deferred_list_guarded_store_effect:
  ^deferred_list fp ce ds vs rs sa es s /\
  typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u dst len /\
  sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  (!name b n. local_region ce es.scopes u name b n <=>
              local_region ce es.scopes s name b n) /\
  (!i. i < LENGTH ds ==>
    ^guarded_disjoint fp.jc_cx (post_value_type ce (EL i ds))
      (EL i rs) (EL i vs) es s dst len) /\
  ^immutable_disjoint ce fp.jc_cx es dst len ==>
  ^deferred_list fp ce ds vs rs sb es u
Proof
  BETA_TAC >> strip_tac >>
  irule (BETA_RULE intcall_deferred_list_endpoint) >> simp[] >>
  qexistsl_tac [`sa`, `s`] >> gvs[] >>
  conj_tac
  >- (drule typed_copy_effect_allocas >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      drule typed_copy_effect_operand_preserved >>
      disch_then irule >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum (drule_then mp_tac) >>
      Cases_on `EL i vs` >> simp[] >> rpt strip_tac >>
      qmatch_goalsub_rename_tac `val_footprint tv v` >>
      (Cases_on `val_footprint tv v = 0`
       >- simp[valueEncodingTheory.mem_bytes_at_def]) >>
      irule typed_copy_effect_bytes >>
      metis_tac[compileEnvTheory.regions_disjoint_def]) >>
  rpt strip_tac >> irule typed_copy_effect_bytes >>
  metis_tac[compileEnvTheory.regions_disjoint_def]
QED
