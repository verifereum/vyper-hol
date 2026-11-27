(* Join the saved representations at the reached unwrap cut, before any row write. *)
Theory bodyAbiTupleSelectedUnwrapMods
Ancestors
  bodyAbiTupleIdentityRestoreMods bodyAbiTupleCodeRestoreMods
  bodyAbiTupleSlotRestoreMods bodyAbiTupleUnwrapNormalizeMods
  bodyAbiTupleCaptureMods bodyAbiEncodePackedPostMods bodyFullPostsMods
  bodyAbiTupleBufferStateMods exprLoweringProps exprSimMemDefs
  loweringPosts compileEnv vyperStorageFootprint finite_map list arithmetic
Libs horizonTypeLib

(* The wrapped layout supplies the type and slot-size bound
   (abi_encode_tuple_layout_mods), and the saved compile/snapshot equations
   with the argument precondition give log_capture_operand_not_label_mods.
   The packed result supplies storage_trace_domain; its canonical horizon
   is available by storage_trace_domain_def. The tuple loop supplies the
   cursor site even in the static-head callback. *)
Theorem abi_tuple_selected_unwrap_mods:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin se e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s) /\
  valid_horizon cx st0 H ee.storage_trace /\
  storage_trace_domain cx st0 ee.storage_trace /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  MEM owner (fn_insts func) /\ owner.inst_id = shared /\
  owner.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cur (fn_insts func) /\ cur.inst_id = loc /\
  cur.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= capacity-dst_offset /\
  hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= capacity-dst_offset /\
  (!l. vv_operand saved <> Label l) /\
  unwrap_value ce saved a = (src,r) /\ fn_has_code a r func /\ ci_mono a r /\
  ty = lowered_value_type ce e /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  type_memory_bytes ce ty = type_memory_size rt /\ type_memory_size rt < 2**64 /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func ==>
  ?z Gz tz first last.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix r z Gz tz /\
    abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc
      a u Gu tu r z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i r z Gz tz /\
    expr_val_at ce cx ty first last ee v src z /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\
    expr_store_bound cx ty v src z /\
    (!x. src = Var x ==> not_fresh_at r x) /\
    (shared < first.cs_next_id \/ last.cs_next_id <= shared) /\
    last.cs_next_id <= r.cs_next_id /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  Cases_on `(?tag op. saved = StackValue tag op) \/
    (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)`
  >- suspend "identity" >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  `?p. saved = LocatedValue (lowered_value_type ce e) p /\
    (p.ptr_location = LocCode \/ p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)`
    suffices_by (disch_then (qx_choose_then `p` (map_every assume_tac o CONJUNCTS)) >>
                 suspend "material") >>
  suspend "material_shape"
QED

Resume abi_tuple_selected_unwrap_mods[identity]:
  drule_all abi_tuple_identity_restore_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`u`,`Gu`,`tu`,`si`,`ss`] >> asm_rewrite_tac[] >>
  qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r u Gu tu`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  qpat_x_assum `r = a` SUBST_ALL_TAC >> decide_tac
QED

Resume abi_tuple_selected_unwrap_mods[material_shape]:
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (strip_assume_tac o REWRITE_RULE[abi_encode_saved_row_mods_def])
  >- (qpat_x_assum `~((?tag op. saved = StackValue tag op) \/ _)` mp_tac >> simp[])
  >- (qpat_x_assum `~((?tag op. saved = StackValue tag op) \/ _)` mp_tac >> simp[] >>
      metis_tac[]) >>
  rename1 `saved = LocatedValue _ p` >>
  qexists `p` >> conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `p.ptr_location` >> gvs[vv_holds_mods_def,vv_holds_def]
QED

Resume abi_tuple_selected_unwrap_mods[material]:
  qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a u Gu tu`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  `pbase + dst_offset + LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
   pbase + dst_offset + hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity`
    by decide_tac >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` >>
  (drule_all abi_tuple_slot_restore_mods ORELSE
    (`p.ptr_location = LocCode` by fs[] >> drule_all abi_tuple_code_restore_mods)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`inst`,`szw`,`out`,`mid`,`b`,`n`]
      (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`z`,`Gz`,`tz`,`a`,`r`] >>
  asm_simp_tac bool_ss [venomStateTheory.operand_11,LESS_EQ_REFL] >>
  irule abi_tuple_materialized_unwrap_normalize_mods >>
  qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a u Gu tu`
    (irule_at Any) >>
  qpat_assum `exec_alloca inst u szw = OK mid` (irule_at Any) >>
  qpat_assum `cur.inst_id = loc` (irule_at Any) >>
  qpat_assum `inst.inst_outputs = [out]` (irule_at Any) >>
  qpat_assum `cur.inst_outputs = [cursor_var]` (irule_at Any) >>
  qpat_assum `owner.inst_outputs = [root]` (irule_at Any) >>
  qpat_assum `FLOOKUP z.vs_allocas a.cs_next_id = SOME (b,n)` (irule_at Any) >>
  qexistsl [`explicit`,`PG`,`H`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then (ACCEPT_TAC o CONJUNCT1))
QED

Finalise abi_tuple_selected_unwrap_mods
