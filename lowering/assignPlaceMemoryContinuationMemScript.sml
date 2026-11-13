(* Memory assignment endpoints retain the local frame of fresh staging. *)
Theory assignPlaceMemoryContinuationMem
Ancestors
  placeAssignStagingMem placeMemoryStateRebuild placeMemoryStagingFrame
  exprSimMemUnwrap abiBuiltinAllocation fragExec venomExecSemantics
  venomInst venomState rich_list exprLoweringProps freshWrites emitHelperProps
  loweringHalt abiTupleProps compileEnv exprSimProps placeTypedCopyPrimitiveMem
  fragGasPathMem valueEncodingProps placeMemoryLiveRegion abiCallerLocalScratch
  stmtSimDefs loweringPosts exprSimAlloc placeMemoryCopyEffect
  placeMemoryAssignForward valueEncodingTyping exprSimHypsDefs exprSimHyps

Theorem assign_alloc_buffer_record[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  (t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_alloca_def, eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  simp[update_var_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[venom_state_component_equality]
QED

Theorem assign_staging_frame_mem[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand op n sm = ((),sn) /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
  fn_has_code sa sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\ n = type_memory_size stv /\
  val_wf stv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + n <= s.vs_alloca_next /\ alloca_history func s ==>
  ?r u tw. gas_path_mem ctx func s 0 (OK r) /\
    gas_path_mem ctx func s 0 (OK u) /\
    stmt_state_rel ctx func cenv cx ee r /\ alloca_history func r /\
    r.vs_memory = s.vs_memory /\ s.vs_alloca_next <= r.vs_alloca_next /\
    eval_operand buf.buf_operand r = SOME tw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    w2n tw + n < dimword (:256) /\ w2n tw + n <= r.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       regions_disjoint (w2n tw) n b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
       local_region cenv ee.scopes r name b len) /\
    typed_copy_effect ctx func sm sn r u (w2n tw) n /\
    val_in_memory stv v (w2n tw) u.vs_memory
Proof
  strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  rename1 `gas_path_mem ctx func s 0 (OK r)` >>
  `(r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (drule_all assign_alloc_buffer_record >> simp[]) >>
  `!name b len. local_region cenv ee.scopes s name b len ==>
     local_region cenv ee.scopes r name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `w2n sw + n <= r.vs_alloca_next` by decide_tac >>
  drule_all compile_copy_memory_effect_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `typed_copy_effect ctx func sm sn r u _ _` >>
  `gas_path_mem ctx func s 0 (OK u)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  `val_in_memory stv v (w2n w) u.vs_memory` by
    (irule valueEncodingPropsTheory.val_in_memory_relocate >> conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `n`, `w2n sw`] >> simp[]) >>
  qexistsl_tac [`r`, `u`, `w`] >> simp[] >> metis_tac[]
QED

Theorem assign_memory_destination_bounds:
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  w2n w + type_memory_size dtv <= s.vs_alloca_next /\
  w2n w + type_memory_size dtv < dimword (:256)
Proof
  strip_tac >> drule_all memory_place_live_region >> strip_tac >>
  `local_ptrs_rel func cenv ee.scopes s` by
    metis_tac[stmt_state_rel_def, state_rel_def] >>
  `b + len <= s.vs_alloca_next` by metis_tac[abi_caller_local_end] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >> decide_tac
QED

Theorem assign_direct_effect_state:
  stmt_state_rel ctx func cenv cx ee s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  val_in_memory dtv v (w2n w) t.vs_memory /\
  typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size dtv) ==>
  stmt_state_rel ctx func cenv cx ff t
Proof
  strip_tac >> irule memory_place_write_stmt_state >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ t.vs_memory`)) >>
  qexistsl_tac [`dty`, `ee`, `env`, `p`, `s`, `s`, `sa`] >>
  gvs[typed_copy_effect_def] >> conj_tac
  >- metis_tac[] >>
  rpt strip_tac >>
  drule_all memory_place_live_region >> strip_tac >>
  `immutable_alloca_sep func cenv cx ee s` by
    metis_tac[stmt_state_rel_def] >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[immutable_alloca_sep_def] >>
  disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!id b sz. local_region _ _ _ _ _ _ ==> _` drule >>
  simp[regions_disjoint_def] >> strip_tac >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len _ = _` irule >> decide_tac
QED

Theorem assign_staging_immutable_frame[local]:
  stmt_state_rel ctx func cenv cx ee r /\
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm func /\
  FLOOKUP r.vs_allocas sa.cs_next_id = SOME (tmp,n) /\
  local_region cenv ee.scopes r name root_addr len /\
  root_addr <= d /\ d+k <= root_addr+len /\
  typed_copy_effect ctx func sm sn r u tmp n /\
  typed_copy_effect ctx func sn sb u t d k ==>
  (cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) r.vs_memory)
Proof
  strip_tac >> rpt strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `immutable_alloca_sep func cenv cx ee r` by metis_tac[stmt_state_rel_def] >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[immutable_alloca_sep_def] >>
  disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac) >>
  simp[] >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) tmp n` by
    (qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _` irule >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `regions_disjoint off (type_memory_size tv) root_addr len` by metis_tac[] >>
  `mem_bytes_at off (type_memory_size tv) t.vs_memory =
   mem_bytes_at off (type_memory_size tv) u.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off (type_memory_size tv) u.vs_memory =
   mem_bytes_at off (type_memory_size tv) r.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >>
     gvs[regions_disjoint_def]) >> simp[]
QED

Theorem assign_staged_effect_state[local]:
  stmt_state_rel ctx func cenv cx ee s /\
  stmt_state_rel ctx func cenv cx ee r /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm func /\
  FLOOKUP r.vs_allocas sa.cs_next_id = SOME (tmp,n) /\
  r.vs_memory = s.vs_memory /\ gas_path_mem ctx func s 0 (OK u) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP r.vs_allocas aid = SOME e) /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    local_region cenv ee.scopes r name b len) /\
  (!name b len. local_region cenv ee.scopes r name b len ==>
    regions_disjoint tmp n b len) /\
  sa.cs_next_var <= sn.cs_next_var /\
  typed_copy_effect ctx func sm sn r u tmp n /\
  typed_copy_effect ctx func sn sb u t (w2n w) (type_memory_size dtv) /\
  val_in_memory dtv v (w2n w) t.vs_memory ==>
  stmt_state_rel ctx func cenv cx ff t
Proof
  strip_tac >>
  drule_all memory_place_live_region >> strip_tac >>
  `local_region cenv ee.scopes r name b len` by metis_tac[] >>
  `cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) r.vs_memory` by
    (rpt strip_tac >> irule assign_staging_immutable_frame >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ sn sb _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    metis_tac[fragGasModeTheory.gas_marked_path_from_mem] >>
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by
    (gvs[typed_copy_effect_def] >> simp[]) >>
  drule_at (Pat `typed_copy_effect _ _ sn sb _ _ _ _`) staging_store_local_frame >>
  simp[] >> disch_then (qspecl_then [`tmp`, `n`] mp_tac) >>
  simp[typed_copy_effect_record, typed_copy_effect_allocas] >>
  disch_then (qspec_then `ee.scopes` mp_tac) >>
  disch_then (qspecl_then [`sa`, `s`, `r`, `cenv`] mp_tac) >>
  (impl_tac >- (gvs[typed_copy_effect_def] >> metis_tac[])) >> strip_tac >>
  irule memory_place_write_stmt_state >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ t.vs_memory`)) >>
  qexistsl_tac [`dty`, `ee`, `env`, `p`, `r`, `s`, `sa`] >> simp[] >>
  metis_tac[]
QED

Theorem assign_staged_memory_path_mem[local]:
  compile_alloc_buffer (type_memory_size stv) sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand op (type_memory_size stv) sm = ((),sn) /\
  compile_store_memory cenv buf.buf_operand dst_op dty sty sn = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  eval_operand op s = SOME sw /\ eval_operand dst_op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx ee s /\ expr_sim_inv cenv cx env ee /\
  local_ptrs_reserved cenv sa /\ alloca_history func s /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sn sb` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     qspecl_then [`cenv`, `buf.buf_operand`, `dst_op`, `dty`, `sty`, `sn`]
       mp_tac ci_mono_compile_store_memory >> simp[ci_mono_def] >>
     rpt strip_tac >> gvs[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  `type_memory_size stv < dimword (:256)` by
    (`s.vs_alloca_next < dimword (:256)` by
       metis_tac[alloca_room_next_lt, stmt_state_rel_def] >> decide_tac) >>
  `val_wf stv v /\ val_wf dtv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  drule_at (Pat `compile_copy_memory _ _ _ _ = _`) assign_staging_frame_mem >>
  disch_then (qspecl_then [`v`, `sw`, `stv`] mp_tac) >>
  simp_tac bool_ss [] >>
  disch_then drule_all >> strip_tac >> suspend "store"
QED

Resume assign_staged_memory_path_mem[store]:
  `w2n w + type_memory_size dtv <= s.vs_alloca_next /\
   w2n w + type_memory_size dtv < dimword (:256)` by
    (irule assign_memory_destination_bounds >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule_all memory_place_live_region >> strip_tac >>
  `local_region cenv ee.scopes r name b len` by metis_tac[] >>
  `w2n tw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n tw` by
    (`regions_disjoint (w2n tw) (type_memory_size stv) b len` by metis_tac[] >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
    (qspec_then `type_memory_size stv` (qspec_then `sa` mp_tac)
       ci_mono_compile_alloc_buffer >>
     qspecl_then [`buf.buf_operand`, `op`, `type_memory_size stv`, `sm`]
       mp_tac ci_mono_compile_copy_memory >> simp[ci_mono_def]) >>
  `sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `(!x. dst_op = Var x ==> not_fresh_at sn x) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sn x)` by
    (conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     rpt strip_tac >> gvs[] >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `u.vs_labels = s.vs_labels` by
    (gvs[typed_copy_effect_def, venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `eval_operand dst_op u = SOME w /\ eval_operand buf.buf_operand u = SOME tw` by
    (gvs[typed_copy_effect_def] >>
     Cases_on `dst_op` >> gvs[eval_operand_def] >>
     `not_fresh_at sm s'` by metis_tac[] >> simp[]) >>
  `u.vs_alloca_next = r.vs_alloca_next` by
    (drule typed_copy_effect_record >>
     disch_then (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  `w2n tw + type_memory_size stv <= u.vs_alloca_next /\
   w2n w + type_memory_size dtv <= u.vs_alloca_next` by decide_tac >>
  `?t. gas_path_mem ctx func u 0 (OK t) /\
       val_in_memory dtv v (w2n w) t.vs_memory /\
       typed_copy_effect ctx func sn sb u t (w2n w) (type_memory_size dtv)` by
    (irule compile_store_memory_nonword_effect_mem >>
     drule typed_copy_effect_endpoint >> strip_tac >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`, `get_tenv cx`] >> simp[] >>
     `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
        type_memory_bytes cenv ty = type_memory_size tv` by
       metis_tac[expr_sim_inv_memory_size] >>
     gvs[expr_sim_inv_def, typed_copy_effect_def] >> metis_tac[]) >>
  suspend "finish"
QED

Resume assign_staged_memory_path_mem[finish]:
  markerLib.RESUME_TAC >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[not_fresh_at_mono, typed_copy_effect_lookup] >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (qpat_assum `typed_copy_effect _ _ sm sn _ _ _ _`
       (mp_then (Pat `typed_copy_effect _ _ _ _ _ _ _ _`) mp_tac
         assign_staged_effect_state) >>
     disch_then drule_all >> simp[]) >>
  drule_at (Pat `typed_copy_effect _ _ sn sb _ _ _ _`) typed_copy_effect_endpoint >>
  strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sn x` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     drule_at (Pat `typed_copy_effect _ _ sn sb _ _ _ _`) typed_copy_effect_lookup >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED
Finalise assign_staged_memory_path_mem


Theorem assign_storage_unwrap_endpoint_mem:
  post_value_type cenv e = expr_type e /\
  unwrap_value cenv (LocatedValue ty srcp) sm = (op,sb) /\
  (srcp.ptr_location = LocStorage \/ srcp.ptr_location = LocTransient) /\
  ~is_word_type ty /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. srcp.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv /\ type_memory_size tv < 2**64) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty srcp) s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?z w tv. gas_path_mem ctx func s 0 (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op z = SOME w /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    w2n w + type_memory_size tv < dimword (:256) /\
    w2n w + type_memory_size tv <= z.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes z name b len ==>
      regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_unwrap_layout_facts >> strip_tac >>
  drule_all storage_unwrap_type_facts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  `storage_holds cx (srcp.ptr_location = LocTransient) ty (Value v) a ee u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >> simp[storage_holds_def]) >>
  `!x. srcp.ptr_operand = Var x \/ buf.buf_operand = Var x ==>
    not_fresh_at mid x` by
    (gen_tac >> strip_tac
     >- (irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >> gvs[]) >>
  `w2n w + 32 * type_slot_size tv < 2**256 /\
   w2n w + 32 * type_slot_size tv <= u.vs_alloca_next` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots, wordsTheory.dimword_def] >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_at (Pat `storage_holds _ _ _ _ _ _ u`) storage_unwrap_typed_suffix_path_mem >>
  disch_then drule_all >> strip_tac >> suspend "finish"
QED

Resume assign_storage_unwrap_endpoint_mem[finish]:
  rename1 `copy_static z = copy_static u` >>
  `expr_post ctx func cenv cx e es sa sb s0 ee v buf.buf_operand z` by
    (irule buffer_post_transport >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`mid`, `srcp`, `s`, `sm`, `ty`, `tv`, `u`, `w`] >>
     asm_rewrite_tac [] >> simp[]) >>
  `local_ptrs_reserved cenv mid` by metis_tac[local_ptrs_reserved_next_var] >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
    regions_disjoint (w2n w) (type_memory_size tv) b len` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes u name b len` by
       metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >> metis_tac[]) >>
  drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK z)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  qexistsl_tac [`z`, `w`, `tv`] >> gvs[] >> metis_tac[]
QED
Finalise assign_storage_unwrap_endpoint_mem

Theorem assign_code_typed_suffix_mem[local]:
  compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca src dst
    (type_slot_size tv) 0 mid = ((),sb) /\
  fn_has_code mid sb func /\ fn_inst_ids_distinct func /\
  copy_old_operand mid src /\ copy_old_operand mid dst /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  stmt_state_rel ctx func cenv cx ee u /\
  immutable_holds cenv cx ty (Value v) a ee u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  w2n w + type_memory_size tv <= u.vs_alloca_next /\
  w2n w + type_memory_size tv < dimword (:256) /\
  w2n a + type_memory_size tv < dimword (:256) /\
  (cenv.ce_is_ctor ==>
    (!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region u = SOME 0w /\ copy_old_operand mid region) /\
    w2n a + type_memory_size tv <= u.vs_alloca_next /\
    regions_disjoint (w2n a) (type_memory_size tv) (w2n w) (type_memory_size tv)) /\
  (~cenv.ce_is_ctor ==> w2n a + type_memory_size tv <= LENGTH u.vs_data_section) /\
  alloca_history func u /\ ~u.vs_halted /\
  u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_path_mem ctx func u 0 (OK z) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w
Proof
  strip_tac >> `alloca_inv u` by fs[stmt_state_rel_def] >>
  Cases_on `cenv.ce_is_ctor`
  >- suspend "constructor" >> suspend "runtime"
QED

Resume assign_code_typed_suffix_mem[constructor]:
  gvs[] >>
  `w2n w + 0 + 32 * type_slot_size tv <= u.vs_alloca_next /\
   w2n w + 0 + 32 * type_slot_size tv < dimword (:256) /\
   w2n a + 0 + 32 * type_slot_size tv <= u.vs_alloca_next /\
   w2n a + 0 + 32 * type_slot_size tv < dimword (:256)` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  drule_all ctor_code_copy_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] exprSimCopyTheory.copy_ctor_contents) >>
  strip_tac >>
  `eval_operand dst t = SOME w` by
    (drule exprSimStorageCopyTheory.storage_copy_operand_preserved >>
     disch_then (qspecl_then [`mid`, `dst`] mp_tac) >>
     gvs[exprSimCopyTheory.copy_old_operand_def]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Resume assign_code_typed_suffix_mem[runtime]:
  gvs[] >>
  `w2n w + 0 + 32 * type_slot_size tv <= u.vs_alloca_next /\
   w2n w + 0 + 32 * type_slot_size tv < dimword (:256) /\
   w2n a + 0 + 32 * type_slot_size tv <= LENGTH u.vs_data_section /\
   w2n a + 0 + 32 * type_slot_size tv < dimword (:256)` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  drule_all code_copy_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] exprSimCopyTheory.copy_runtime_contents) >>
  strip_tac >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] runtime_copy_frame_facts) >>
  strip_tac >>
  `eval_operand dst t = SOME w` by
    (drule exprSimStorageCopyTheory.storage_copy_operand_preserved >>
     disch_then (qspecl_then [`mid`, `dst`] mp_tac) >>
     gvs[exprSimCopyTheory.copy_old_operand_def]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
Finalise assign_code_typed_suffix_mem


Theorem assign_code_unwrap_endpoint_mem:
  post_value_type cenv e = expr_type e /\
  unwrap_value cenv (LocatedValue ty srcp) sm = (op,sb) /\
  srcp.ptr_location = LocCode /\
  ~is_word_type ty /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. srcp.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty srcp) s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?z w tv. gas_path_mem ctx func s 0 (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op z = SOME w /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    w2n w + type_memory_size tv < dimword (:256) /\
    w2n w + type_memory_size tv <= z.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes z name b len ==>
      regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[exprLoweringTheory.unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = (_,sc)` >>
  `ty = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand srcp.ptr_operand s = SOME a /\
       immutable_holds cenv cx ty (Value v) a ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all exprSimCopyTheory.immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv ty = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv ty < dimword (:256)` by decide_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv ty`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid sc` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid sc /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sc.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func /\ fn_has_code mid sc func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  suspend "allocated"
QED

Resume assign_code_unwrap_endpoint_mem[allocated]:
  `exprSimCopy$copy_old_operand mid srcp.ptr_operand /\
   exprSimCopy$copy_old_operand mid buf.buf_operand` by
    (rw[exprSimCopyTheory.copy_old_operand_def] >> gvs[] >>
     metis_tac[not_fresh_at_mono]) >>
  `(type_memory_bytes cenv ty + 31) DIV 32 = type_slot_size tv` by
    (simp[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `immutable_holds cenv cx ty (Value v) a ee u` by
    (qpat_x_assum `immutable_holds _ _ _ _ _ _ s` mp_tac >>
     simp[immutable_holds_def]) >>
  `cenv.ce_is_ctor ==>
    (!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region u = SOME 0w /\ exprSimCopy$copy_old_operand mid region) /\
    w2n a + type_memory_size tv <= u.vs_alloca_next /\
    regions_disjoint (w2n a) (type_memory_size tv) (w2n w) (type_memory_size tv)` by
    suspend "constructor_bounds" >>
  `~cenv.ce_is_ctor ==> w2n a + type_memory_size tv <= LENGTH u.vs_data_section` by
    (strip_tac >> irule bodyImmutableUnwrapMemoryTheory.runtime_immutable_data_section >> metis_tac[]) >>
  `w2n w + type_memory_size tv <= u.vs_alloca_next /\
   w2n w + type_memory_size tv < dimword (:256)` by fs[] >>
  drule_all assign_code_typed_suffix_mem >> strip_tac >> suspend "finish"
QED
Resume assign_code_unwrap_endpoint_mem[constructor_bounds]:
  strip_tac >>
  `immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `eval_operand region s = SOME 0w` by fs[immutable_base_zero_def] >>
      `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
        metis_tac[local_ptrs_reserved_imm_base] >>
      `exprSimCopy$copy_old_operand sa region` by
        (simp[exprSimCopyTheory.copy_old_operand_def] >> rpt strip_tac >> gvs[]) >>
      `exprSimCopy$copy_old_operand sm region` by
        (irule exprSimCopyTheory.copy_old_operand_mono >> qexists_tac `sa` >> fs[]) >>
      `exprSimCopy$copy_old_operand mid region` by
        (irule exprSimCopyTheory.copy_old_operand_mono >> qexists_tac `sm` >> fs[]) >>
      `eval_operand region u = eval_operand region s` by
        (Cases_on `region` >> fs[eval_operand_def, exprSimCopyTheory.copy_old_operand_def]) >>
      fs[]) >>
  conj_tac >- metis_tac[ctor_immutable_frontier, arithmeticTheory.LE_TRANS] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
     [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  irule exprSimCopyTheory.immutable_holds_alloca_disjoint >>
  qexistsl_tac [`cenv`, `ctx`, `cx`, `ee`, `func`] >>
  goal_assum (drule_at Any) >> simp[mk_inst_def] >>
  qexistsl_tac [`ty`, `u`, `v`] >> gvs[]
QED

Resume assign_code_unwrap_endpoint_mem[finish]:
  rename1 `copy_static z = copy_static u` >>
  `expr_post ctx func cenv cx e es sa sc s0 ee v buf.buf_operand z` by
    (irule buffer_post_transport >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`mid`, `srcp`, `s`, `sm`, `ty`, `tv`, `u`, `w`] >>
     asm_rewrite_tac [] >> simp[]) >>
  `local_ptrs_reserved cenv mid` by metis_tac[local_ptrs_reserved_next_var] >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
    regions_disjoint (w2n w) (type_memory_size tv) b len` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes u name b len` by
       metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >> metis_tac[]) >>
  drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK z)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  qexistsl_tac [`z`, `w`, `tv`] >> gvs[] >> metis_tac[]
QED
Finalise assign_code_unwrap_endpoint_mem


Theorem assign_direct_memory_path_mem[local]:
  compile_store_memory cenv op dst_op dty sty sa = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  eval_operand op s = SOME sw /\ eval_operand dst_op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    regions_disjoint (w2n sw) (type_memory_size stv) b len) /\
  stmt_state_rel ctx func cenv cx ee s /\ expr_sim_inv cenv cx env ee /\
  local_ptrs_reserved cenv sa /\ alloca_history func s /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `w2n w + type_memory_size dtv <= s.vs_alloca_next /\
   w2n w + type_memory_size dtv < dimword (:256)` by
    (irule assign_memory_destination_bounds >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (`s.vs_alloca_next < dimword (:256)` by
       metis_tac[alloca_room_next_lt, stmt_state_rel_def] >> decide_tac) >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (drule_all memory_place_live_region >> strip_tac >>
     `regions_disjoint (w2n sw) (type_memory_size stv) b len` by metis_tac[] >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  `val_wf stv v /\ val_wf dtv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `?t. gas_path_mem ctx func s 0 (OK t) /\
       val_in_memory dtv v (w2n w) t.vs_memory /\
       typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size dtv)` by
    (irule compile_store_memory_nonword_effect_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`, `get_tenv cx`] >> simp[] >>
     `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
        type_memory_bytes cenv ty = type_memory_size tv` by
       metis_tac[expr_sim_inv_memory_size] >>
     gvs[expr_sim_inv_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule assign_direct_effect_state >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[typed_copy_effect_lookup]
QED


Theorem assign_place_memory_continuation_mem:
  compile_assign_value cenv dst_op LocMemory op F src_loc dty sty dynarray_info mem_size sa = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  eval_operand op s = SOME sw /\ eval_operand dst_op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (src_loc <> SOME LocMemory ==>
    !name b len. local_region cenv ee.scopes s name b len ==>
      regions_disjoint (w2n sw) (type_memory_size stv) b len) /\
  stmt_state_rel ctx func cenv cx ee s /\ expr_sim_inv cenv cx env ee /\
  local_ptrs_reserved cenv sa /\ alloca_history func s /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `src_loc = SOME LocMemory`
  >- (`type_memory_bytes cenv sty = type_memory_size stv` by
        metis_tac[expr_sim_inv_memory_size] >>
      gvs[stmtLoweringTheory.compile_assign_value_def, comp_bind_def,
          comp_return_def, comp_ignore_bind_def] >>
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      irule assign_staged_memory_path_mem >> simp[] >>
      goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
      simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `compile_store_memory cenv op dst_op dty sty sa = ((),sb)` by
    gvs[stmtLoweringTheory.compile_assign_value_def] >>
  irule assign_direct_memory_path_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
