(* Reserved pointer lookups suffice for decoder proof-state reentry. *)
Theory abiMalformedPruneState
Ancestors
  abiDecoderReentry exprLoweringProps localPtrsProps compileEnv loweringStateRelDefs
  venomState finite_map pred_set arithmetic

Theorem abi_malformed_reserved_vars_state:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
  (!x. not_fresh_at st x ==>
       lookup_var x (s with vs_vars := vars) = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es (s with vs_vars := vars)
Proof
  strip_tac >>
  `!name entry p sz.
     lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p (s with vs_vars := vars) = lookup_var p s` by
    (rpt strip_tac >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `local_ptrs_rel func cenv es.scopes (s with vs_vars := vars)` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  irule stmt_state_rel_allocas_frame >> conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >>
      reverse conj_tac >- gvs[stmt_state_rel_def] >>
      rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at st x ==> _` irule >>
      fs[local_ptrs_reserved_def]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
      simp[] >> reverse conj_tac >- gvs[stmt_state_rel_def] >>
      rpt strip_tac >> qexists_tac `id` >>
      fs[local_region_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (qexistsl_tac [`es`, `s`] >> simp[]) >>
  irule state_rel_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`es`, `s`] >> simp[] >>
  gvs[stmt_state_rel_def, state_rel_def, immutables_rel_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_malformed_prune_state:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st ==>
  stmt_state_rel ctx func cenv cx es
    (abi_decoder_prune_vars st.cs_next_var s)
Proof
  strip_tac >> rewrite_tac[abi_decoder_prune_vars_def] >>
  irule abi_malformed_reserved_vars_state >> simp[] >> qexists_tac `st` >> simp[] >>
  simp[not_fresh_at_def, lookup_var_def, FLOOKUP_DRESTRICT,
       abi_decoder_older_vars_def]
QED

Theorem abi_malformed_vars_restore_state:
  stmt_state_rel ctx func cenv cx es (abi_decoder_prune_vars st.cs_next_var s) /\
  local_ptrs_reserved cenv st /\
  (!x. not_fresh_at st x ==>
     lookup_var x (s with vs_vars := vars) =
     lookup_var x (abi_decoder_prune_vars st.cs_next_var s)) ==>
  stmt_state_rel ctx func cenv cx es (s with vs_vars := vars)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
     ((abi_decoder_prune_vars st.cs_next_var s) with vs_vars := vars)` suffices_by
    simp[abi_decoder_prune_vars_def] >>
  irule abi_malformed_reserved_vars_state >> simp[] >>
  qexists_tac `st` >> simp[abi_decoder_prune_vars_def] >>
  gvs[abi_decoder_prune_vars_def]
QED
