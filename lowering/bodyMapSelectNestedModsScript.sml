(* A nested mapping lookup completes at the endpoint of its slot calculation. *)
Theory bodyMapSelectNestedMods
Ancestors
  bodyFullPostsMods gasOutcomeFullPostMods vyperHashMapStorage
  vyperStoragePlaceProvenance gasOutcomeFull fragGasOriginPtr loweringPosts
  bodyFullHashKeccakFixed context vyperAST vyperState

Theorem mapping_select_map_mods:
  storage_mapping_region cx tr slot (HashMapT kt (HashMapT ikt ivt)) /\
  fin.gas_obs = [] /\ ~it.vs_halted /\
  vv = LocatedValue ann (mk_ptr outop (slot_loc tr)) /\
  eval_operand outop u = SOME (hashmap_slot slot (encode_hashmap_key kt v)) /\
  op_taint tnu outop = {} /\ op_prov Gu outop = NONE /\
  wb_frame cenv es fin sa s0 u /\
  (~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 u) /\
  return_buf_frame d cenv sa u /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (it,Gi,tni) [] (OK u,Gu,tnu) /\
    stmt_state_rel H ctx func cenv cx fin u /\
    immutable_frame_mods func cenv cx fin u /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx fin Gu tnu u) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (select_result cx (expr_type obj) (HashMapRef tr slot kt (HashMapT ikt ivt))
      (ValueSubscript v)) (fin,it,Gi,tni)
    (\H res ee G tn t. ?tr slot kt vt tp p.
      res = INL (HashMapRef tr slot kt vt) /\
      storage_mapping_region cx tr slot (HashMapT kt vt) /\
      vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
      eval_operand p.ptr_operand t = SOME slot /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
         aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) ==>
         mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
      locals_kept cenv es ee s0 t /\
      (~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 t) /\
      return_buf_frame d cenv sa t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R
Proof
  strip_tac >>
  `fin with gas_obs := [] = fin` by
    (qpat_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `storage_mapping_region cx tr (hashmap_slot slot (encode_hashmap_key kt v))
      (HashMapT ikt ivt)` by
    (irule storage_mapping_region_step >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gu`, `fin`,
    `INL (HashMapRef tr (hashmap_slot slot (encode_hashmap_key kt v)) ikt ivt)`,
    `u`, `tnu`] >>
  simp[select_result_hashmap_nested] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  simp[mk_ptr_def] >> first_assum ACCEPT_TAC
QED
