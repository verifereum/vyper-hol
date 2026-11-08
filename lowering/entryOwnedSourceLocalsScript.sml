(* Local pointers at the fixed source-owned registration endpoint. *)
Theory entryOwnedSourceLocals
Ancestors
  calldataRegistrationLocals entryRuntimePackageLayout entrySourceOwnedEndpoint
  allocaFrontierBound venomMemDefs venomState entryLocals list finite_map

Theorem owned_source_scope_lookup[local]:
  bind_arguments tenv args (MAP (\(ty,tv,v,at,av). v) values) = SOME env /\
  ALL_DISTINCT (MAP FST args) /\
  MAP FST pa = MAP FST args /\
  LIST_REL (\(name,ty) (ty',tv,v,(at:abi_type),(av:abi_value)).
    ty' = ty /\ evaluate_type tenv ty = SOME tv) args values /\
  LIST_REL (\(name,tv,v) (dst,p,id).
    FLOOKUP cer.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\ ins.inst_id = id) /\
    id < registered.cs_next_id /\ abi_decoder_operand_live registered.cs_next_var dst /\
    FLOOKUP out.vs_allocas id = SOME (p,type_memory_size tv) /\
    eval_operand dst out = SOME (n2w p) /\
    val_wf tv v /\ val_in_memory tv v p out.vs_memory)
    (MAP (\((name,(prim:bool),(dyn:bool),(sz:num),(info:abi_dec_info)),(ty,tv,v,at,av)). (name,tv,v))
      (ZIP (pa,values))) outputs /\
  out.vs_alloca_next < dimword (:256) /\ alloca_inv out ==>
  !name entry ptr sz.
    FLOOKUP env name = SOME entry /\
    FLOOKUP cer.ce_vars name = SOME (PtrVar (Var ptr) sz) ==>
    ?p ins. lookup_var ptr out = SOME (n2w p) /\ p < dimword (:256) /\
      MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
      ins.inst_outputs = [ptr] /\ FLOOKUP out.vs_allocas ins.inst_id = SOME (p,sz) /\
      type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
      val_in_memory entry.type entry.value p out.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all decoded_arguments_scope_lookup >> strip_tac >>
  `LENGTH args = LENGTH values /\ LENGTH pa = LENGTH args` by
    metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  qpat_x_assum `LIST_REL _ args values` mp_tac >>
  rewrite_tac[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  qabbrev_tac `arg = EL i args` >> qabbrev_tac `value = EL i values` >>
  PairCases_on `arg` >> PairCases_on `value` >> simp[] >> strip_tac >>
  suspend "owned"
QED

Resume owned_source_scope_lookup[owned]:
  qpat_x_assum `LIST_REL _ (MAP _ _) outputs` mp_tac >>
  rewrite_tac[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[EL_MAP, EL_ZIP] >>
  qabbrev_tac `spec = EL i pa` >> qabbrev_tac `slot = EL i outputs` >>
  PairCases_on `spec` >> PairCases_on `slot` >> simp[] >> strip_tac >>
  `spec0 = arg0` by
    (qpat_x_assum `MAP FST pa = MAP FST args` (mp_tac o Q.AP_TERM `EL i`) >>
     simp[EL_MAP, GSYM markerTheory.Abbrev_def] >> gvs[]) >>
  gvs[markerTheory.Abbrev_def, eval_operand_def] >>
  `slot1 < dimword (:256)` by
    (fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts fn)`)) >> simp[]
QED

Finalise owned_source_scope_lookup

Theorem owned_source_arguments_local_ptrs:
  set_external_package_target target
    (package_external_fn tops locks keys (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pa,mc,pay,nr',key,locks',view,fbody',rt) /\
  compile_register_positional_args ce pa 4 st = (cer,registered) /\
  bind_arguments (type_env tops) args (MAP (\(ty,tv,v,at,av). v) values) = SOME env /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) (ty',tv,v,(at:abi_type),(av:abi_value)).
    ty' = ty /\ evaluate_type (type_env tops) ty = SOME tv) args values /\
  LIST_REL (\(name,tv,v) (dst,p,id).
    FLOOKUP cer.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\ ins.inst_id = id) /\
    id < registered.cs_next_id /\ abi_decoder_operand_live registered.cs_next_var dst /\
    FLOOKUP out.vs_allocas id = SOME (p,type_memory_size tv) /\
    eval_operand dst out = SOME (n2w p) /\
    val_wf tv v /\ val_in_memory tv v p out.vs_memory)
    (MAP (\((name,(prim:bool),(dyn:bool),(sz:num),(info:abi_dec_info)),(ty,tv,v,at,av)). (name,tv,v))
      (ZIP (pa,values))) outputs /\
  alloca_inv out /\ alloca_frontier_inv ctx fn site out /\
  unit_alloca_budget ctx < dimword (:256) /\ fn_inst_ids_distinct fn ==>
  local_ptrs_rel fn cer [env] out
Proof
  strip_tac >> drule targeted_external_package_vars >> strip_tac >>
  `MAP FST pa = MAP FST args` by simp[build_positional_args_FST] >>
  drule_all targeted_registered_locals >> strip_tac >>
  `out.vs_alloca_next < dimword (:256)` by
    (fs[alloca_frontier_inv_def] >> decide_tac) >>
  irule decoded_scope_local_ptrs >>
  reverse conj_tac >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> irule owned_source_scope_lookup >>
  simp[] >>
  qpat_assum `bind_arguments _ _ _ = SOME env` (irule_at Any) >>
  qpat_assum `LIST_REL _ (MAP _ _) outputs` (irule_at Any) >> simp[] >> metis_tac[]
QED
