Theory placeStoreDynPrepare
Ancestors
  placeStoreAllocPath placeTypedCopyRecursivePath exprSimBufferStore
  exprLoweringProps compileEnv typedMemoryCopy venomState stmtLowering
  exprLowering finite_map loweringHalt freshWrites fragGasMode fragExec venomInst exprSimAlloc

Theorem place_stmt_control_frame[local]:
  stmt_state_rel ctx func cenv cx es
    (s with <|vs_prev_bb := prev; vs_current_bb := bb; vs_inst_idx := ix|>) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  `!op. eval_operand op (s with <|vs_prev_bb := prev;
      vs_current_bb := bb; vs_inst_idx := ix|>) = eval_operand op s` by
    (Cases >> simp[venomStateTheory.eval_operand_def, lookup_var_def]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
    local_region_def, local_backed_def, storage_rel_def, transient_rel_def,
    accounts_rel_def, immutables_rel_def, logs_rel_def,
    venomMemDefsTheory.alloca_inv_def, alloca_room_def, fmp_room_def,
    immutable_alloca_sep_def, immutable_base_zero_def,
    lookup_var_def, venomStateTheory.eval_operand_def, contract_storage_def, contract_transient_def,
    venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, pending_alloca_size_def]
QED

Theorem place_typed_copy_alloca_state_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  typed_copy_state_frame sa dst len s t /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,alloc_sz) /\ len <= alloc_sz /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint dst len b sz) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `!name tv v off. cenv.ce_is_ctor /\
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) dst len` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[stmt_state_rel_def]) >>
     fs[immutable_alloca_sep_def] >>
     `regions_disjoint off (type_memory_size tv) dst alloc_sz` by metis_tac[] >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es
     (t with <|vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
               vs_inst_idx := s.vs_inst_idx|>)` suffices_by
    simp[place_stmt_control_frame] >>
  irule buffer_store_state_frame >>
  qexistsl_tac [`dst`, `len`, `s`, `sa`] >>
  simp[lookup_var_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac)
  >- (rpt strip_tac >> first_x_assum drule >> simp[lookup_var_def])
  >- gvs[venom_state_component_equality] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem place_dyn_assign_compile_cut:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_assign_value cenv dst loc src F src_loc (ArrayT et (Dynamic n)) sty
    (SOME (ew,ems)) sz sa = ((),sb) ==>
  ?prepared mid.
    (if ArrayT et (Dynamic n) <> sty then
       comp_bind (compile_alloc_buffer sz)
         (\buf. comp_bind
           (compile_store_memory_typed cenv buf.buf_operand
              (ArrayT et (Dynamic n)) src sty)
           (\u. comp_return buf.buf_operand))
     else comp_return src) sa = (prepared,mid) /\
    compile_dynarray_to_storage prepared dst ew ems (loc = LocTransient)
      mid = ((),sb)
Proof
  strip_tac >>
  gvs[compile_assign_value_def, is_bytestring_type_def, comp_bind_def,
      comp_return_def, AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  goal_assum (drule_at Any) >> gvs[comp_ignore_bind_def, comp_bind_def]
QED

Theorem place_alloca_source_disjoint:
  stmt_state_rel ctx func cenv cx es s /\
  inst.inst_outputs = [out] /\ exec_alloca inst s (n2w sz:bytes32) = OK t /\
  lookup_var out t = SOME dw /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  sz < dimword (:256) /\
  a + len <= s.vs_alloca_next /\
  (!b cap. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,cap) ==>
     a + len <= b \/ b + cap <= a) ==>
  a + len <= w2n dw \/ w2n dw + sz <= a
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[]
  >- (strip_tac >>
      gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          wordsTheory.w2n_n2w]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME region` >>
  PairCases_on `region` >> strip_tac >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem place_dyn_normalize_run:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,mid) /\
  compile_store_memory_typed cenv buf.buf_operand dty src sty mid = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t pw. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME pw /\
    val_in_memory dtv v (w2n pw) t.vs_memory /\
    eval_operand dst t = SOME dw /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    contract_storage t = contract_storage s /\
    contract_transient t = contract_transient s /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `cs_extends sa mid` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends mid sb` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all place_alloc_buffer_source_path >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ u` kall_tac >>
     irule place_alloca_source_disjoint >>
     simp[] >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
         [STRING #"%" (toString sa.cs_next_var)]`,
       `STRING #"%" (toString sa.cs_next_var)`, `raw`] >>
     gvs[run_inst_seq_def, mk_inst_def, venomExecSemanticsTheory.step_inst_base_def,
         venomStateTheory.eval_operands_def,
         venomStateTheory.eval_operand_def, lookup_var_def, AllCaseEqs()] >>
     rpt strip_tac >>
     qpat_x_assum `!aid b sz. _ /\ sa.cs_next_id <= aid ==> _` drule >>
     simp[]) >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  `eval_operand src u = SOME sw` by
    (Cases_on `src` >> gvs[venomStateTheory.eval_operand_def]) >>
  `!x. src = Var x ==> not_fresh_at mid x` by metis_tac[] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at mid x` by simp[] >>
  `local_ptrs_reserved cenv mid` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
  drule compile_store_memory_typed_forward_run >>
  disch_then (qspec_then `tenv` mp_tac) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ u.vs_memory`)) >>
  disch_then (drule_at (Pat `fn_has_code mid sb _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `eval_operand buf.buf_operand u = _`)) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule place_typed_copy_alloca_state_frame >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     qexistsl_tac [`type_memory_size dtv`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
         [STRING #"%" (toString sa.cs_next_var)]`] >>
     simp[mk_inst_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
     qexists_tac `u` >> simp[gas_marked_path_def]) >>
  `eval_operand buf.buf_operand t = SOME w` by
    (drule typed_copy_state_frame_operand >>
     disch_then (qspec_then `buf.buf_operand` mp_tac) >> simp[]) >>
  `eval_operand dst t = SOME dw` by
    (drule typed_copy_state_frame_operand >>
     disch_then (qspec_then `dst` mp_tac) >> simp[]) >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
  simp[typed_copy_state_frame_def, venom_state_component_equality] >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  gvs[contract_storage_def, contract_transient_def] >>
  rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at mid x ==> _` (qspec_then `x` mp_tac) >>
  simp[]
QED

Theorem place_dyn_prepare_run:
  (if dty <> sty then
     comp_bind (compile_alloc_buffer (type_memory_size dtv))
       (\buf. comp_bind
         (compile_store_memory_typed cenv buf.buf_operand dty src sty)
         (\u. comp_return buf.buf_operand))
   else comp_return src) sa = (prepared,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t pw. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand prepared t = SOME pw /\
    val_in_memory dtv v (w2n pw) t.vs_memory /\
    eval_operand dst t = SOME dw /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    contract_storage t = contract_storage s /\
    contract_transient t = contract_transient s /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `dty = sty`
  >- (gvs[comp_return_def] >> qexistsl_tac [`s`, `sw`] >>
      simp[gas_marked_path_def] >> irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  irule place_dyn_normalize_run >> simp[arithmeticTheory.ADD_COMM] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  simp[arithmeticTheory.ADD_COMM] >>
  qexistsl_tac [`stv`, `tenv`] >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
