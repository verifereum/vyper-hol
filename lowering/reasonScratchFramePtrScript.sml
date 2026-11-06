(* Source-state transport for encoder scratch copies. *)
Theory reasonScratchFramePtr
Ancestors
  varsExt reasonTupleCopyPtr exprSimProps exprSimBufferStore exprLoweringProps
  venomState venomMemProofs venomExecSemantics finite_map

Theorem reason_scratch_vars_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  (!name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!p. cenv.ce_imm_alloca = SOME (Var p) ==>
    lookup_var p t = lookup_var p s) ==>
  stmt_state_rel ctx func cenv cx es (s with vs_vars := t.vs_vars)
Proof
  strip_tac >> irule stmt_state_rel_vars_frame >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

Theorem reason_scratch_copy_state_rel:
  stmt_state_rel ctx func cenv cx es (s with vs_vars := t.vs_vars) /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  not_local_ptr cenv es.scopes p /\ n <= capacity /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,capacity) /\
  t = (s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
               vs_inst_idx := t.vs_inst_idx|>) /\
  t.vs_memory = (mcopy dst src n s).vs_memory ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
      (mcopy dst src n (s with vs_vars := t.vs_vars))` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >> metis_tac[]) >>
  `t = (mcopy dst src n (s with vs_vars := t.vs_vars)) with
         vs_inst_idx := t.vs_inst_idx` by
    (gvs[mcopy_def, write_memory_with_expansion_def,
         venom_state_component_equality]) >>
  qpat_x_assum `t = _ with vs_inst_idx := _` (fn th => once_rewrite_tac[th]) >>
  simp[stmt_state_rel_inst_idx]
QED

(* Fresh scratch registers preserve every source-language pointer binding. *)
Theorem reason_scratch_fresh_vars_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  (!p. MEM p outputs ==> lookup_var p s = NONE) /\
  (!p. ~MEM p outputs ==> lookup_var p t = lookup_var p s) ==>
  stmt_state_rel ctx func cenv cx es (s with vs_vars := t.vs_vars)
Proof
  strip_tac >> irule stmt_state_rel_vars_ext >>
  qexists_tac `s` >> simp[vars_ext_def] >>
  simp[SUBMAP_DEF] >> rpt strip_tac >>
  `~MEM x outputs` by
    (metis_tac[lookup_var_def, FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  first_x_assum drule >> simp[lookup_var_def, FLOOKUP_DEF]
QED

Theorem reason_scratch_fresh_copy_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  not_local_ptr cenv es.scopes p /\ n <= capacity /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,capacity) /\
  t = (s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
               vs_inst_idx := t.vs_inst_idx|>) /\
  t.vs_memory = (mcopy dst src n s).vs_memory /\
  (!q. MEM q outputs ==> lookup_var q s = NONE) /\
  (!q. ~MEM q outputs ==> lookup_var q t = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (s with vs_vars := t.vs_vars)` by
    (irule reason_scratch_fresh_vars_state_rel >> metis_tac[]) >>
  drule_all reason_scratch_copy_state_rel >> simp[]
QED

(* Compiler-private outputs may overwrite old runtime scratch values. *)
Theorem reason_scratch_nonlocal_vars_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  (!q. MEM q outputs ==> not_local_ptr cenv es.scopes q) /\
  (!q. ~MEM q outputs ==> lookup_var q t = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx es (s with vs_vars := t.vs_vars)
Proof
  strip_tac >> irule reason_scratch_vars_state_rel >> simp[] >>
  conj_tac >> rpt strip_tac >>
  `~MEM p outputs` by (fs[compileEnvTheory.not_local_ptr_def] >> metis_tac[]) >>
  simp[]
QED

Theorem reason_scratch_nonlocal_copy_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  not_local_ptr cenv es.scopes p /\ n <= capacity /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,capacity) /\
  t = (s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
               vs_inst_idx := t.vs_inst_idx|>) /\
  t.vs_memory = (mcopy dst src n s).vs_memory /\
  (!q. MEM q outputs ==> not_local_ptr cenv es.scopes q) /\
  (!q. ~MEM q outputs ==> lookup_var q t = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (s with vs_vars := t.vs_vars)` by
    (irule reason_scratch_nonlocal_vars_state_rel >> metis_tac[]) >>
  drule_all reason_scratch_copy_state_rel >> simp[]
QED
