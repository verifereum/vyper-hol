(* The observed region constrains storage taint at both the loaded header
   and a selected child, regardless of how the slot operand was computed. *)
Theory bodyArrayObservedSlotOperandMods
Ancestors
  bodyFullShadowBodyInv bodyPtrDefs loweringPosts accountsRelProps
  vyperStoragePlaceObserved loweringStateRelDefs sourceUnitExecution
  ptrDiscipline vyperValue words pred_set

Theorem array_observed_slot_operand_mods:
  dead_lo_ok_mods H D lo cenv cx /\
  ghost_inv_at_mods D lo d cenv cx ee G tn u /\
  storage_place_observed H (StoragePlace tr w vt) /\
  evaluate_type (get_tenv cx) ty = SOME vt /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand u = SOME w /\
  op_taint tn p.ptr_operand = {} ==>
  ptr_vv_ok cx ty (PlaceR (StoragePlace tr w vt)) (LocatedValue ann p) ee G tn u /\
  (!etv cap. vt = ArrayTV etv (Dynamic cap) ==>
     key_taint (if tr then tn.t_trans else tn.t_stor) w = {})
Proof
  strip_tac >>
  Cases_on `type_slot_size vt = 0`
  >- (conj_tac
      >- (Cases_on `tr` >> gvs[ptr_vv_ok_def, slot_loc_def]) >>
      rpt strip_tac >> gvs[type_slot_size_def]) >>
  `!raw. storage_read_live H tr raw w vt` by
    (gen_tac >> irule storage_place_observed_read_live >> simp[]) >>
  `stor_taint_ok_at D tn u` by fs[ghost_inv_at_mods_def] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` kall_tac >>
  `!k b. w2n w <= w2n k /\ w2n k < w2n w + type_slot_size vt /\ b < 32 /\
         (k,b) IN (if tr then tn.t_trans else tn.t_stor) ==>
         dead_bytes (if tr then u.vs_transient u.vs_call_ctx.cc_address
                     else (u.vs_accounts u.vs_call_ctx.cc_address).storage)
                    (w2n w) vt (w2n k) b` by
    (Cases_on `tr` >> Cases_on `u.vs_call_ctx.cc_address = cx.txn.target` >>
     gvs[stor_taint_ok_at_def, dead_lo_ok_mods_def, cx_dead_def, SUBSET_DEF,
         pairTheory.FORALL_PROD, storage_read_live_def] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  conj_tac
  >- (Cases_on `tr` >> gvs[ptr_vv_ok_def, slot_loc_def] >> metis_tac[]) >>
  rpt strip_tac >> simp[key_taint_def, EXTENSION] >>
  gen_tac >> rename1 `~(b < 32) \/ _` >>
  Cases_on `b < 32` >> simp[] >> strip_tac >>
  `w2n w < w2n w + type_slot_size (ArrayTV etv (Dynamic cap))` by
    simp[type_slot_size_def] >>
  qpat_assum `!k b. _ ==> dead_bytes _ _ _ _ _`
    (qspecl_then [`w`, `b`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule (CONJUNCT1 dead_bytes_range) >> simp[]
QED
