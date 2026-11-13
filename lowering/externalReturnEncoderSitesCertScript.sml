(* Task-local syntactic certificate for encoder scratch sites. *)
Theory externalReturnEncoderSitesCert
Ancestors
  abiEncoder abiEncoderAppend abiEncoderCounters abiEncoderProps localPtrsProps
  emitHelperProps fragExec compileEnv context venomInst list arithmetic pred_set pair emitHelper rich_list

(* Unlike a property of all instructions in a compile state, this certificate
   makes no assumption about instructions preceding the fragment. *)
Definition return_encoder_sites_def:
  return_encoder_sites (action : 'a compiler) <=>
    cs_appends action /\ abi_encoder_counters_mono action /\
    !st func inst. fn_has_code st (SND (action st)) func /\
      fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
      st.cs_next_id <= inst.inst_id /\
      inst.inst_id < (SND (action st)).cs_next_id /\
      inst.inst_opcode = ALLOCA ==>
      inst.inst_operands = [Lit 32w]
End

Theorem return_encoder_sites_return:
  return_encoder_sites (comp_return v)
Proof
  simp[return_encoder_sites_def, cs_appends_return,
    abi_encoder_counters_mono_return, comp_return_def] >> rpt strip_tac >> metis_tac[NOT_LESS]
QED

Theorem return_encoder_sites_bind:
  return_encoder_sites action /\ (!v. return_encoder_sites (next v)) ==>
  return_encoder_sites (comp_bind action next)
Proof
  strip_tac >> rewrite_tac[return_encoder_sites_def] >> conj_tac
  >- (irule cs_appends_bind >> gvs[return_encoder_sites_def]) >> conj_tac
  >- (irule abi_encoder_counters_mono_bind >> gvs[return_encoder_sites_def]) >>
  rpt gen_tac >> Cases_on `action st` >> rename1 `action st = (v,st')` >>
  asm_simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
  strip_tac >>
  `cs_extends st st' /\ cs_extends st' (SND (next v st'))` by
    (gvs[return_encoder_sites_def, cs_appends_def] >> metis_tac[PAIR, SND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  Cases_on `inst.inst_id < st'.cs_next_id` >>
  gvs[return_encoder_sites_def] >> metis_tac[SND, NOT_LESS]
QED

Theorem return_encoder_sites_ignore_bind:
  return_encoder_sites action /\ return_encoder_sites next ==>
  return_encoder_sites (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule return_encoder_sites_bind >> simp[]
QED

Theorem return_encoder_sites_emit_inst:
  (opc <> ALLOCA \/ ops = [Lit 32w]) ==>
  return_encoder_sites (emit_inst opc ops outs)
Proof
  disch_tac >> simp[return_encoder_sites_def, cs_appends_emit_helpers,
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
     qexists `func` >> simp[]) >>
  gvs[mk_inst_def]
QED

Theorem return_encoder_sites_prims:
  return_encoder_sites fresh_var /\
  (!name. return_encoder_sites (fresh_label name)) /\
  (!name. return_encoder_sites (new_block name))
Proof
  simp[return_encoder_sites_def, cs_appends_prims,
    abi_encoder_counters_mono_def, fresh_var_def, fresh_label_def,
    new_block_def] >> rpt strip_tac >> metis_tac[NOT_LESS]
QED

Theorem return_encoder_emit_op_split[local]:
  emit_op opc ops =
    comp_bind fresh_var (\out.
      comp_ignore_bind (emit_inst opc ops [out]) (comp_return (Var out)))
Proof
  simp[FUN_EQ_THM, emit_op_def, emit_inst_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
    emit_def, LET_THM]
QED

Theorem return_encoder_sites_emit_op:
  (opc <> ALLOCA \/ ops = [Lit 32w]) ==>
  return_encoder_sites (emit_op opc ops)
Proof
  strip_tac >> rewrite_tac[return_encoder_emit_op_split] >>
  irule return_encoder_sites_bind >> simp[return_encoder_sites_prims] >>
  gen_tac >> irule return_encoder_sites_ignore_bind >>
  simp[return_encoder_sites_emit_inst, return_encoder_sites_return]
QED

Theorem return_encoder_sites_emit_void:
  (opc <> ALLOCA \/ ops = [Lit 32w]) ==>
  return_encoder_sites (emit_void opc ops)
Proof
  rewrite_tac[emit_void_def, GSYM emit_inst_def] >>
  metis_tac[return_encoder_sites_emit_inst]
QED

val site_simps = [return_encoder_sites_return, return_encoder_sites_prims,
  return_encoder_sites_emit_op, return_encoder_sites_emit_void,
  return_encoder_sites_emit_inst, LET_THM];

fun encoder_sites_tac extra g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) (extra @ site_simps)],
    first_x_assum (fn th => FIRST_PROVE
      [irule (SRULE[] th) >> asm_simp_tac (srw_ss()) []]),
    ho_match_mp_tac return_encoder_sites_bind >> conj_tac
      >- encoder_sites_tac extra >> rpt gen_tac >> encoder_sites_tac extra,
    ho_match_mp_tac return_encoder_sites_ignore_bind >> conj_tac >>
      encoder_sites_tac extra,
    IF_CASES_TAC >> fs[] >> encoder_sites_tac extra]) g;

Theorem return_encoder_sites_alloc:
  return_encoder_sites (compile_alloc_buffer 32)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> encoder_sites_tac []
QED

Theorem return_encoder_sites_static:
  return_encoder_sites (compile_abi_encode_static dst src)
Proof
  rewrite_tac[compile_abi_encode_static_def] >> encoder_sites_tac []
QED

Theorem return_encoder_sites_static_info:
  !dst src ei. return_encoder_sites (compile_abi_encode_static_info dst src ei)
Proof
  rpt gen_tac >> Cases_on `ei` >>
  rewrite_tac[compile_abi_encode_static_info_def] >>
  encoder_sites_tac [return_encoder_sites_static]
QED

Theorem return_encoder_sites_static_loop:
  return_encoder_sites
    (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  encoder_sites_tac [return_encoder_sites_alloc, return_encoder_sites_static_info]
QED

Theorem return_encoder_sites_mutual:
  (!dst src ei dyn off ptr.
    return_encoder_sites (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. return_encoder_sites (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    return_encoder_sites (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    return_encoder_sites (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  ONCE_REWRITE_TAC [compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  imp_res_tac abi_encoder_complex_append_bindings >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  encoder_sites_tac [return_encoder_sites_static, return_encoder_sites_alloc,
    return_encoder_sites_static_loop]
QED

Theorem return_encoder_alloca_operands:
  compile_abi_encode_to_buf dst src ei mid = (out,en) /\
  fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id IN frag_ids mid en ==>
  inst.inst_operands = [Lit 32w]
Proof
  strip_tac >> gvs[frag_ids_def] >>
  mp_tac (cj 2 return_encoder_sites_mutual) >>
  simp_tac (srw_ss()) [return_encoder_sites_def] >>
  metis_tac[SND]
QED

Theorem return_encoder_site_lower_bound:
  inst.inst_id IN frag_ids mid en ==> mid.cs_next_id <= inst.inst_id
Proof
  simp[frag_ids_def]
QED
