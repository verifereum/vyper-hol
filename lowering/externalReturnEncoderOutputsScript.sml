(* Task-owned singleton/fresh output certificate for encoder scratch cells. *)
Theory externalReturnEncoderOutputs
Ancestors
  externalReturnEncoderSitesCert abiEncoder abiEncoderAppend abiEncoderCounters
  abiEncoderProps localPtrsProps exprLoweringProps emitHelperProps fragExec
  compileEnv context venomInst list arithmetic pred_set pair emitHelper rich_list

Definition return_encoder_outputs_def:
  return_encoder_outputs (action : 'a compiler) <=>
    cs_appends action /\ abi_encoder_counters_mono action /\
    !st func inst. fn_has_code st (SND (action st)) func /\
      fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
      st.cs_next_id <= inst.inst_id /\
      inst.inst_id < (SND (action st)).cs_next_id /\
      inst.inst_opcode = ALLOCA ==>
      ?n. st.cs_next_var <= n /\
        inst.inst_outputs = [STRING #"%" (toString n)]
End

Theorem return_encoder_outputs_return:
  return_encoder_outputs (comp_return v)
Proof
  simp[return_encoder_outputs_def, cs_appends_return,
    abi_encoder_counters_mono_return, comp_return_def] >>
  rpt strip_tac >> metis_tac[NOT_LESS]
QED

Theorem return_encoder_outputs_bind:
  return_encoder_outputs action /\ (!v. return_encoder_outputs (next v)) ==>
  return_encoder_outputs (comp_bind action next)
Proof
  strip_tac >> rewrite_tac[return_encoder_outputs_def] >> conj_tac
  >- (irule cs_appends_bind >> gvs[return_encoder_outputs_def]) >> conj_tac
  >- (irule abi_encoder_counters_mono_bind >> gvs[return_encoder_outputs_def]) >>
  rpt gen_tac >> Cases_on `action st` >> rename1 `action st = (v,st')` >>
  asm_simp_tac (srw_ss()) [comp_bind_def, LET_THM] >> strip_tac >>
  `cs_extends st st' /\ cs_extends st' (SND (next v st'))` by
    (gvs[return_encoder_outputs_def, cs_appends_def] >> metis_tac[PAIR, SND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `st.cs_next_var <= st'.cs_next_var` by
    (gvs[return_encoder_outputs_def, abi_encoder_counters_mono_def] >>
     metis_tac[SND]) >>
  Cases_on `inst.inst_id < st'.cs_next_id`
  >- (qpat_x_assum `!v. return_encoder_outputs (next v)` kall_tac >>
      gvs[return_encoder_outputs_def] >> metis_tac[SND]) >>
  qpat_x_assum `return_encoder_outputs action` kall_tac >>
  qpat_x_assum `!v. return_encoder_outputs (next v)`
    (qspec_then `v` mp_tac) >>
  rewrite_tac[return_encoder_outputs_def] >> strip_tac >>
  `st'.cs_next_id <= inst.inst_id` by decide_tac >>
  qpat_x_assum `!st func inst. _` drule_all >> strip_tac >>
  qexists `n` >> simp[]
QED

Theorem return_encoder_outputs_ignore_bind:
  return_encoder_outputs action /\ return_encoder_outputs next ==>
  return_encoder_outputs (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule return_encoder_outputs_bind >> simp[]
QED

Theorem return_encoder_outputs_emit_inst:
  opc <> ALLOCA ==> return_encoder_outputs (emit_inst opc ops outs)
Proof
  strip_tac >> simp[return_encoder_outputs_def, cs_appends_emit_helpers,
    abi_encoder_counters_mono_prims] >> rpt gen_tac >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, emit_def, LET_THM] >> strip_tac >>
  `inst.inst_id = st.cs_next_id` by decide_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  `MEM (mk_inst st.cs_next_id opc ops outs) (fn_insts func)` by
    (irule lookup_block_fn_insts >> qexistsl [`bb`, `st.cs_current_bb`] >>
     gvs[IS_PREFIX_APPEND, MEM_APPEND]) >>
  `inst = mk_inst st.cs_next_id opc ops outs` by
    (irule fn_inst_ids_distinct_inj >> conj_tac >- simp[mk_inst_def] >>
     qexists `func` >> simp[]) >> gvs[mk_inst_def]
QED

Theorem return_encoder_outputs_emit_op:
  return_encoder_outputs (emit_op opc ops)
Proof
  simp[return_encoder_outputs_def, cs_appends_emit_helpers,
    abi_encoder_counters_mono_prims] >> rpt gen_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, LET_THM] >> strip_tac >>
  `inst.inst_id = st.cs_next_id` by decide_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  `MEM (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (irule lookup_block_fn_insts >> qexistsl [`bb`, `st.cs_current_bb`] >>
     gvs[IS_PREFIX_APPEND, MEM_APPEND]) >>
  `inst = mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]` by
    (irule fn_inst_ids_distinct_inj >> conj_tac >- simp[mk_inst_def] >>
     qexists `func` >> simp[]) >>
  qexists `st.cs_next_var` >> simp[mk_inst_def]
QED

Theorem return_encoder_outputs_prims:
  return_encoder_outputs fresh_var /\
  (!name. return_encoder_outputs (fresh_label name)) /\
  (!name. return_encoder_outputs (new_block name))
Proof
  simp[return_encoder_outputs_def, cs_appends_prims,
    abi_encoder_counters_mono_def, fresh_var_def, fresh_label_def,
    new_block_def] >> rpt strip_tac >> metis_tac[NOT_LESS]
QED

Theorem return_encoder_outputs_emit_void:
  opc <> ALLOCA ==> return_encoder_outputs (emit_void opc ops)
Proof
  rewrite_tac[emit_void_def, GSYM emit_inst_def] >>
  metis_tac[return_encoder_outputs_emit_inst]
QED

val output_simps = [return_encoder_outputs_return, return_encoder_outputs_prims,
  return_encoder_outputs_emit_op, return_encoder_outputs_emit_void,
  return_encoder_outputs_emit_inst, LET_THM];

fun encoder_outputs_tac extra g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) (extra @ output_simps)],
    first_x_assum (fn th => FIRST_PROVE
      [irule (SRULE[] th) >> asm_simp_tac (srw_ss()) []]),
    ho_match_mp_tac return_encoder_outputs_bind >> conj_tac
      >- encoder_outputs_tac extra >> rpt gen_tac >> encoder_outputs_tac extra,
    ho_match_mp_tac return_encoder_outputs_ignore_bind >> conj_tac >>
      encoder_outputs_tac extra,
    IF_CASES_TAC >> fs[] >> encoder_outputs_tac extra]) g;

Theorem return_encoder_outputs_alloc:
  return_encoder_outputs (compile_alloc_buffer 32)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> encoder_outputs_tac []
QED

Theorem return_encoder_outputs_static:
  return_encoder_outputs (compile_abi_encode_static dst src)
Proof
  rewrite_tac[compile_abi_encode_static_def] >> encoder_outputs_tac []
QED

Theorem return_encoder_outputs_static_info:
  !dst src ei. return_encoder_outputs (compile_abi_encode_static_info dst src ei)
Proof
  rpt gen_tac >> Cases_on `ei` >>
  rewrite_tac[compile_abi_encode_static_info_def] >>
  encoder_outputs_tac [return_encoder_outputs_static]
QED

Theorem return_encoder_outputs_static_loop:
  return_encoder_outputs
    (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  encoder_outputs_tac [return_encoder_outputs_alloc, return_encoder_outputs_static_info]
QED

Theorem return_encoder_outputs_mutual:
  (!dst src ei dyn off ptr.
    return_encoder_outputs (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. return_encoder_outputs (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    return_encoder_outputs (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    return_encoder_outputs (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  ONCE_REWRITE_TAC [compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  imp_res_tac abi_encoder_complex_append_bindings >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  encoder_outputs_tac [return_encoder_outputs_static, return_encoder_outputs_alloc,
    return_encoder_outputs_static_loop]
QED

Theorem return_encoder_alloca_output:
  compile_abi_encode_to_buf dst src ei mid = (out,en) /\
  fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id IN frag_ids mid en ==>
  ?n. mid.cs_next_var <= n /\ inst.inst_outputs = [STRING #"%" (toString n)]
Proof
  strip_tac >> gvs[frag_ids_def] >>
  mp_tac (cj 2 return_encoder_outputs_mutual) >>
  simp_tac (srw_ss()) [return_encoder_outputs_def] >> metis_tac[SND]
QED

Theorem return_encoder_alloca_local_disjoint:
  compile_abi_encode_to_buf dst src ei mid = (out,en) /\
  fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id IN frag_ids mid en /\ local_ptrs_reserved cenv mid /\
  stmt_state_rel ctx func cenv cx es u /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) /\
  local_region cenv es.scopes u name lo len ==>
  venomMemDefs$regions_disjoint (lo,len) (b,sz)
Proof
  strip_tac >> drule_all return_encoder_alloca_output >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString n))` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def, not_fresh_at_def] >>
     metis_tac[]) >>
  `regions_disjoint b sz lo len` by
    (irule local_ptrs_rel_alloca_disjoint >>
     qpat_assum `local_region _ _ _ _ _ _` (irule_at Any) >>
     qexistsl_tac [`STRING #"%" (toString n)`, `inst`, `func`] >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  gvs[regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED
