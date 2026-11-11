(* Local-pointer reservation at the actual internal-function entry. *)
Theory bodyIntCallActualEntryReserved
Ancestors
  bodyIntCallActualEntryOperands bodyIntCallActualEntryResource
  bodyIntCallActualEntryFields bodyIntCallBodyTrace intCallCallee
  compileEnv loweringStateRelDefs context emitHelper exprLoweringProps finite_map list rich_list
  arithmetic ASCIInumbers

Theorem materialize_internal_params_install_imm:
  materialize_internal_params ce caps st = (ce',st') /\
  local_ptrs_reserved ce' st' /\
  not_fresh_at st x /\ EVERY (\c. SND (SND c) <> Var x) caps /\
  (!n sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar (Var x) sz)) ==>
  local_ptrs_reserved (ce' with ce_imm_alloca := SOME (Var x)) st'
Proof
  strip_tac >> drule_all materialize_internal_params_excludes_old >> strip_tac >>
  drule materialize_internal_params_shape >> strip_tac >>
  gvs[] >> fs[local_ptrs_reserved_def, not_fresh_at_def] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem internal_entry_prefix_caps_reserved:
  compile_internal_entry_prefix ce params has_rb st0 = ((stage_ce,caps,rpc),sc) /\
  sc.cs_next_var <= sr.cs_next_var /\
  ALL_DISTINCT (MAP FST params) /\
  (!i. i < LENGTH params ==>
    ?off sz. FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz)) /\
  (!n off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==>
    MEM n (MAP FST params)) /\
  (!n p sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar p sz)) /\
  ce.ce_imm_alloca = NONE /\
  materialize_internal_params stage_ce caps sr = (ce2,sm) ==>
  local_ptrs_reserved ce2 sm
Proof
  strip_tac >> drule internal_entry_prefix_stages >> strip_tac >>
  drule internal_entry_prefix_shapes >> strip_tac >>
  drule compile_internal_param_decls_shape >> strip_tac >>
  `ALL_DISTINCT (MAP (SND o SND) caps)` by
    (simp[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> rpt strip_tac >>
     gvs[toString_inj]) >>
  irule materialize_internal_params_reserved >>
  qexistsl [`caps`, `stage_ce`, `sr`] >> simp[] >>
  rpt gen_tac >> simp[MEM_EL] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `emit_op RETPC_PARAM _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED
