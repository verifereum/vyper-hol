Theory bodyPtrPopReturned
Ancestors
  bodyPtrPopRootChild bodyPtrPopLiveElement bodyPtrPopRegionInvariant
  bodyPtrPopDeclaredEntry bodyPtrDefs accountsRelProps context
  exprSimPopStorage compileEnv vyperValue vyperStorage words pred_set

(* Extent is demanded only when an actual selected tainted byte exists. *)
Theorem pop_last_child_taint_header:
  storage_read_live cx tr st hdr (ArrayTV tv (Dynamic n)) /\
  X SUBSET {(k,b) | storage_dead cx tr st (w2n k) b} /\
  len = w2n (lookup_storage hdr st) /\ 0 < len /\ len <= n /\
  elem = hdr + n2w (1 + (len - 1) * type_slot_size tv) ==>
  pop_region_taint_ok (update_storage hdr u st) (w2n elem) tv
    (key_update X hdr {})
Proof
  strip_tac >>
  Cases_on `type_slot_size tv = 0`
  >- simp[pop_region_taint_ok_def] >>
  rewrite_tac[pop_region_taint_ok_def] >> rpt gen_tac >> strip_tac >>
  `storage_dead cx tr st (w2n k) b` by
    (qpat_x_assum `_ SUBSET _` mp_tac >> simp[SUBSET_DEF] >>
     disch_then (qspec_then `(k,b)` mp_tac) >>
     gvs[ptrDisciplineTheory.key_update_def]) >>
  `w2n hdr + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword (:256)` by
    (qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
     simp[storage_read_live_def] >> metis_tac[]) >>
  `w2n elem + type_slot_size tv <= dimword (:256) /\
   w2n hdr < w2n elem` by
    (drule_all pop_array_last_bounds >> gvs[]) >>
  `storage_read_live cx tr st elem tv` by
    (drule pop_live_dynamic_element >>
     disch_then (qspec_then `len - 1` mp_tac) >>
     impl_tac >- simp[] >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM] >> simp[]) >>
  drule_all pop_child_taint_header >>
  simp[]
QED

Theorem pop_returned_place_of_region:
  evaluate_type (get_tenv cx) ann = SOME tv /\
  eval_operand op s = SOME elem /\ op_taint tn op = {} /\
  pop_region_taint_ok
    (if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage)
    (w2n elem) tv (if tr then tn.t_trans else tn.t_stor) ==>
  ptr_vv_ok cx ann result
    (LocatedValue ann (mk_ptr op (if tr then LocTransient else LocStorage)))
    es G tn s
Proof
  Cases_on `tr` >>
  simp[bodyPtrDefsTheory.ptr_vv_ok_def, contextTheory.mk_ptr_def,
       pop_region_taint_ok_def] >> metis_tac[]
QED

Theorem pop_declared_returned_place:
  expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,hdr,ArrayTV tv (Dynamic n)) /\
  stor_taint_ok cx tn s /\
  raw = (if tr then s.vs_transient s.vs_call_ctx.cc_address
         else (s.vs_accounts s.vs_call_ctx.cc_address).storage) /\
  len = w2n (lookup_storage hdr raw) /\ 0 < len /\
  elem = hdr + n2w (1 + (len - 1) * type_slot_size tv) /\
  (if tr then sf.vs_transient sf.vs_call_ctx.cc_address
   else (sf.vs_accounts sf.vs_call_ctx.cc_address).storage) =
    update_storage hdr u raw /\
  (if tr then tnf.t_trans else tnf.t_stor) =
    key_update (if tr then tn.t_trans else tn.t_stor) hdr {} /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  eval_operand op sf = SOME elem /\ op_taint tnf op = {} ==>
  ptr_vv_ok cx ann result
    (LocatedValue ann (mk_ptr op (if tr then LocTransient else LocStorage)))
    esf Gf tnf sf
Proof
  strip_tac >> irule pop_returned_place_of_region >> simp[] >>
  `len <= n` by
    (drule_all pop_declared_array_slots >>
     disch_then assume_tac >> drule pop_array_length_bound >> strip_tac >>
     `0 < type_slot_size (ArrayTV tv (Dynamic n))` by simp[type_slot_size_def] >>
     drule_all pop_declared_header_agree >> strip_tac >> gvs[] >> metis_tac[]) >>
  `storage_read_live cx tr raw hdr (ArrayTV tv (Dynamic n))` by
    metis_tac[declared_storage_region_read_live] >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def,
       compileEnvTheory.call_ctx_rel_def] >>
  `(if tr then tn.t_trans else tn.t_stor) SUBSET
     {(k,b) | storage_dead cx tr raw (w2n k) b}` by
    (Cases_on `tr` >>
     gvs[stor_taint_ok_def, cx_dead_def]) >>
  irule pop_last_child_taint_header >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`cx`,`tr`] >> gvs[]
QED
