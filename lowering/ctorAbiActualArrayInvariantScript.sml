(* Pure persistent observations for actual-site constructor array loops. *)
Theory ctorAbiActualArrayInvariant
Ancestors
  ctorAbiActualArrayIteration ctorAbiActualObservations ctorAbiActualSites
  ctorAbiActualMemory ctorAbiActualFrame abiDecoderDynamicLoopSetup abiDecoderContract
  abiDecoderReentry abiDecoderVarSequence abiEncoderRegisteredEffect abiDecoderTypedContract
  abiDecoderArraySetupInputs abiDecoderArrayInvariant rich_list ctorAbiActualChildFrame vyperTyping
  allocaFrontierBound allocaBudgetProps valueEncoding valueEncodingDefs valueEncodingProps
  venomMemDefs venomState compileEnv loweringStateRelDefs finite_map list words arithmetic pred_set
  abiDecoderArrayPrefix abiDecoderReentryAddress abiDecoderExecution
  abiEncoderPrimitiveEffect venomExecSemantics

Definition ctor_actual_array_observation_def:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s <=>
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s
End

Theorem ctor_actual_child_preserves_slot:
  abi_encoder_registered_effect (ctor_actual_sites func child) [(c,k)] s t /\
  alloca_inv t /\ FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\
  slot_id NOTIN child /\ venomMemDefs$regions_disjoint (slot,32) (c,k) ==>
  mload slot t = mload slot s
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas slot_id = SOME (slot,32)` by
    fs[abi_encoder_registered_effect_def] >>
  `mem_bytes_at slot 32 t.vs_memory = mem_bytes_at slot 32 s.vs_memory` by
    (irule ctor_actual_registered_window >>
     qexistsl [`ctor_actual_sites func child`, `[(c,k)]`] >>
     asm_simp_tac bool_ss [] >> reverse conj_tac
     >- (gvs[venomMemDefsTheory.regions_disjoint_def] >> rpt strip_tac >> decide_tac) >>
     rpt strip_tac >>
     `i <> slot_id` by (gvs[ctor_actual_sites_def] >> metis_tac[]) >>
     gvs[alloca_inv_def, allocas_non_overlapping_def, venomMemDefsTheory.regions_disjoint_def] >>
     metis_tac[]) >>
  fs[mload_def, mem_bytes_at_def]
QED

Theorem ctor_actual_array_observation_operand:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
  eval_operand op s = SOME w
Proof
  strip_tac >> Cases_on `op` >>
  gvs[ctor_actual_array_observation_def, abi_decoder_operand_live_def, eval_operand_def] >>
  first_x_assum irule >> fs[IN_DEF]
QED

Theorem ctor_actual_address_old_vars:
  abi_decoder_address_frame next s t ==>
  !x w. abi_decoder_older_vars next x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w
Proof
  simp_tac bool_ss [abi_decoder_address_frame_def] >> rpt strip_tac >>
  qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
  simp[abi_decoder_operand_live_def, eval_operand_def, IN_DEF]
QED

Theorem ctor_actual_address_allocations:
  abi_decoder_address_frame next s t ==>
  (alloca_inv t = alloca_inv s) /\
  (alloca_frontier_inv ctx func site t = alloca_frontier_inv ctx func site s) /\
  (ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s)
Proof
  simp[abi_decoder_address_frame_def] >> strip_tac >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_frontier_inv_def, remaining_alloca_budget_def, ctor_actual_scratch_def]
QED

Theorem ctor_actual_array_observation_ranges:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\
  abi_decoder_ranges DLOAD (Lit 0w) hi src dst 0 sb len d outsz b cap initial ==>
  abi_decoder_ranges DLOAD (Lit 0w) hi src dst 0 sb len d outsz b cap s
Proof
  strip_tac >>
  fs[abi_decoder_ranges_def] >> simp[eval_operand_def] >> rpt conj_tac >>
  metis_tac[ctor_actual_array_observation_operand]
QED

Theorem ctor_actual_array_observation_setup_inputs:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_operand_live next ip /\ eval_operand ip initial = SOME (n2w slot) /\
  mem_bytes_at sb len initial.vs_data_section = bytes ==>
  eval_operand ip s = SOME (n2w slot) /\
  mload (w2n (n2w slot : bytes32)) s = n2w cursor /\
  mem_bytes_at sb len s.vs_data_section = bytes
Proof
  strip_tac >>
  `eval_operand ip s = SOME (n2w slot)` by
    (metis_tac[ctor_actual_array_observation_operand]) >>
  fs[ctor_actual_array_observation_def, alloca_inv_def, alloca_next_valid_def] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_frontier_inv_bound] >>
  `slot + 32 <= s.vs_alloca_next` by metis_tac[] >>
  `slot < dimword (:256)` by decide_tac >> simp[]
QED

Theorem ctor_actual_address_source_hi:
  abi_decoder_address_frame next s t /\
  abi_decoder_operand_live next hi /\
  mem_bytes_at sb len s.vs_data_section = bytes /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + len <= h /\ h < dimword (:256)) ==>
  mem_bytes_at sb len t.vs_data_section = bytes /\
  (hi = Lit 0w \/ ?h. eval_operand hi t = SOME (n2w h) /\
    sb + len <= h /\ h < dimword (:256))
Proof
  rw[abi_decoder_address_frame_def] >> metis_tac[]
QED

Theorem ctor_actual_array_child_inputs_at_index:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD (Lit 0w) hi src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  prepared.vs_data_section = initial.vs_data_section /\
  (hi = Lit 0w \/ !w. eval_operand hi initial = SOME w ==> eval_operand hi prepared = SOME w) ==>
  let off = abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j;
      k = type_memory_bytes ce ty;
      cell = d+32+j*k in
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (EL j avs) (EL j vs) /\
  type_memory_size tv = k /\ all_have_type tv vs /\ j < LENGTH avs /\
  cell+k <= d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\ d <= cell /\
  sb+off+LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) < dimword (:256) /\
  mem_bytes_at (sb+off) (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)))
    prepared.vs_data_section = enc (vyper_to_abi_type env ty) (EL j avs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi prepared = SOME (n2w h) /\
    sb+off+LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) <= h /\ h < dimword (:256))
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
   d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by
    fs[abi_decoder_ranges_def] >>
  `abi_decode_source DLOAD initial = initial.vs_data_section` by simp[abi_decode_source_def] >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     (abi_decode_source DLOAD initial) =
     enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    (pure_asm_rewrite_tac [] >> REFL_TAC) >>
  mp_tac (Q.INST [`pre` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `post` |-> `DROP (SUC j) (avs:abi_value list)`,
    `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`,
    `s` |-> `initial:venom_state`, `opc` |-> `DLOAD`]
    abi_decoder_dynarray_child_source) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [LET_THM, abi_decode_source_def] >> strip_tac >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    fs[abi_decoder_metadata_def] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexists `h` >> asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem ctor_actual_array_observation_child:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j prepared /\
  j < LENGTH vs /\ all_have_type tv vs /\ D <= d /\
  d+32+j*type_memory_size tv+type_memory_size tv <= d+outsz /\
  d+outsz <= D+N /\ child SUBSET ids /\ slot_id NOTIN child /\
  venomMemDefs$regions_disjoint (slot,32) (d+32+j*type_memory_size tv,type_memory_size tv) /\
  next <= middle.cs_next_var /\
  abi_encoder_registered_effect (ctor_actual_sites func child)
    [(d+32+j*type_memory_size tv,type_memory_size tv)] prepared t /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) t.vs_memory /\
  alloca_inv t /\ alloca_frontier_inv ctx func site t /\
  ctor_actual_scratch func ids D N t /\ D+N <= t.vs_alloca_next /\
  fresh_vars_wrt limit_st t /\ t.vs_data_section = prepared.vs_data_section /\
  t.vs_call_ctx = prepared.vs_call_ctx /\ t.vs_labels = prepared.vs_labels /\
  (!x w. not_fresh_at middle x /\ lookup_var x prepared = SOME w ==> lookup_var x t = SOME w) ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ctor_actual_array_observation_def]) >>
  `LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  `D <= d+32 /\ d+32+j*type_memory_size tv <= D+N` by
    (qpat_x_assum `D <= d` mp_tac >>
     qpat_x_assum `d+outsz <= D+N` mp_tac >>
     qpat_x_assum `_ + type_memory_size tv <= d+outsz` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `all_have_type tv (TAKE j vs)` by
    (fs[all_have_type_EVERY] >> simp[EVERY_TAKE]) >>
  `elems_in_memory (TAKE j vs ++ [EL j vs]) (d+32) tv t.vs_memory` by
    (irule ctor_actual_child_append_element >> asm_simp_tac bool_ss [] >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     qexistsl [`D`, `N`, `ids`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `mload slot t = mload slot prepared` by
    (metis_tac[ctor_actual_child_preserves_slot]) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 prepared.vs_memory` by
    (irule ctor_actual_registered_window >>
     qexistsl [`ctor_actual_sites func child`,
       `[(d+32+j*type_memory_size tv,type_memory_size tv)]`] >>
     asm_simp_tac bool_ss [] >> conj_tac
     >- (rpt strip_tac >> irule (cj 2 ctor_actual_sites_scratch_contained) >>
         goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
         qexistsl [`child`, `D`, `func`, `ids`, `N`] >>
         asm_simp_tac bool_ss [] >>
         qpat_x_assum `d+32+j*type_memory_size tv <= D+N` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> rpt strip_tac >> decide_tac) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] prepared t` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  simp_tac bool_ss [ctor_actual_array_observation_def] >>
  asm_simp_tac bool_ss [TAKE_SUC, TAKE1_DROP] >>
  conj_tac >- simp[] >>
  conj_tac >- fs[mload_def, mem_bytes_at_def] >>
  conj_tac >- fs[abi_encoder_registered_effect_def] >>
  reverse conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
  rpt strip_tac >>
  `lookup_var x prepared = SOME w` by metis_tac[] >>
  `not_fresh_at middle x` by
    (fs[abi_decoder_older_vars_def, not_fresh_at_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem ctor_actual_array_observation_backedge:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j s /\
  slot_id IN ctor_actual_sites func ids /\ all_have_type tv vs /\
  32 + LENGTH vs * type_memory_size tv <= outsz /\
  venomMemDefs$regions_disjoint (slot,32) (d,outsz) /\
  next <= nv /\ nv < limit_st.cs_next_var ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) (SUC j)
    (jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s)))
Proof
  strip_tac >>
  qabbrev_tac `t = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s))` >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString nv),n2w (SUC j)) /\
   t.vs_labels = s.vs_labels` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  `fresh_vars_wrt limit_st s` by fs[ctor_actual_array_observation_def] >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `abi_decode_frame slot 32 s t` by
    (simp[abi_decode_frame_def, Abbr `t`, jump_to_def, update_var_def] >>
     rpt strip_tac >> irule EQ_TRANS >>
     irule_at Any mstore_mem_bytes_at_disjoint >> simp[]) >>
  `all_have_type tv (TAKE (SUC j) vs)` by
    (fs[all_have_type_EVERY] >> irule EVERY_TAKE >> first_assum ACCEPT_TAC) >>
  `SUC j * type_memory_size tv <= LENGTH vs * type_memory_size tv` by
    (fs[ctor_actual_array_observation_def] >> simp[LE_MULT_RCANCEL, LENGTH_TAKE]) >>
  `elems_in_memory (TAKE (SUC j) vs) (d+32) tv t.vs_memory` by
    (irule abi_decode_frame_preserves_elements >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`s`, `slot`, `32`] >>
     full_simp_tac bool_ss [ctor_actual_array_observation_def,
       venomMemDefsTheory.regions_disjoint_def] >>
     asm_simp_tac bool_ss [LENGTH_TAKE] >> decide_tac) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (qpat_x_assum `abi_decode_frame slot 32 s t` mp_tac >>
     simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >>
     first_x_assum irule >>
     fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mload d t = mload d s` by
    (qpat_x_assum `mem_bytes_at d 32 _ = _` mp_tac >>
     simp_tac bool_ss [mem_bytes_at_def, mload_def, LET_THM] >>
     disch_then SUBST1_TAC >> REFL_TAC) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s t` by
    (`abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s
       (mstore slot (n2w (SUC j)) s)` by
       (irule abi_encoder_registered_slot_store >> qexists `slot_id` >>
        fs[ctor_actual_array_observation_def]) >>
     pop_assum mp_tac >>
     simp[Abbr `t`, jump_to_def, abi_encoder_registered_effect_def,
       update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  `alloca_inv t = alloca_inv s /\
   alloca_frontier_inv ctx func site t = alloca_frontier_inv ctx func site s /\
   ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def,
      write_memory_with_expansion_def, alloca_inv_def, allocas_non_overlapping_def,
      alloca_next_valid_def, alloca_frontier_inv_def, remaining_alloca_budget_def,
      ctor_actual_scratch_def] >>
  `mload slot t = n2w (SUC j)` by
    (simp[Abbr `t`, abi_decode_mload_jump,
       venomMemProofsTheory.mload_mstore_same_proof]) >>
  full_simp_tac bool_ss [ctor_actual_array_observation_def] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >>
      `lookup_var x s = SOME w` by metis_tac[] >>
      `abi_decoder_operand_live nv (Var x)` by
        (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF] >>
         metis_tac[LESS_EQ_TRANS]) >>
      qpat_x_assum `!op. _` (qspec_then `Var x` mp_tac) >>
      simp[eval_operand_def]) >>
  irule abi_encoder_registered_effect_trans >> qexists `s` >>
  asm_simp_tac bool_ss []
QED

Theorem ctor_actual_array_observation_entry:
  mload d initial = n2w (LENGTH vs) /\
  FLOOKUP initial.vs_allocas slot_id = SOME (slot,32) /\ mload slot initial = 0w /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  fresh_vars_wrt limit_st initial ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial 0 0 initial
Proof
  simp[ctor_actual_array_observation_def, val_in_memory_def,
    abi_encoder_registered_effect_refl]
QED

Theorem ctor_actual_array_observation_terminal:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) s ==>
  elems_in_memory vs (d+32) tv s.vs_memory /\
  mload d s = n2w (LENGTH vs) /\ mload slot s = n2w (LENGTH vs)
Proof
  simp[ctor_actual_array_observation_def]
QED
