Theory exprSimAbiEncodeFreshness
Ancestors
  loweringStateRelDefs
  abiEncoderObserver abiEncoderWindowLookup venomExecProofs venomInstProps
  compileEnv exprLoweringProps finite_map list venomInst venomState
  venomExecSemantics unitShapeDefs exprSimAbiEncodeRegion

(* Execution, unlike a continuation simulation alone, certifies absent high
   registers. This boundary deliberately exposes its instruction premise. *)
Theorem abi_encode_observer_step_non_output:
  abi_observer_step ctx fn cut s t /\
  (!i. MEM i (fn_insts fn) ==> ~MEM x i.inst_outputs) ==>
  lookup_var x t = lookup_var x s
Proof
  simp_tac bool_ss [abi_observer_step_def] >> rpt strip_tac >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     qexists `bb` >> conj_tac >- metis_tac[lookup_block_MEM] >>
     fs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  `lookup_var x middle = lookup_var x s` by
    (Cases_on `is_terminator inst.inst_opcode`
     >- metis_tac[step_terminator_preserves_vars] >>
     metis_tac[step_preserves_non_output_vars]) >>
  gvs[lookup_var_def] >>
  irule EQ_TRANS >> qexists `FLOOKUP middle.vs_vars x` >>
  conj_tac >- (irule eval_phis_flookup_not_phi_output >>
    goal_assum (drule_at Any) >> rpt strip_tac >>
    qpat_x_assum `!i. MEM i (fn_insts fn) ==> _` (qspec_then `inst'` mp_tac) >>
    (impl_tac >- (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
      qexists `target` >> simp[] >> metis_tac[lookup_block_MEM])) >>
    simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem abi_encode_local_prefix_non_output:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
  !x. (!i. MEM i (fn_insts fn) ==> ~MEM x i.inst_outputs) ==>
    lookup_var x t = lookup_var x s
Proof
  ho_match_mp_tac local_prefix_ind >> rpt strip_tac >>
  metis_tac[abi_encode_observer_step_non_output]
QED

Theorem abi_encode_local_prefix_fresh:
  local_prefix ctx fn cut s t /\
  (!i. MEM i (fn_insts fn) ==> EVERY (not_fresh_at en) i.inst_outputs) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> irule abi_window_high_vars_fresh >>
  qexistsl [`en`, `s`] >> simp[] >> rpt strip_tac >>
  irule abi_encode_local_prefix_non_output >>
  goal_assum (drule_at Any) >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_encode_observed_endpoint_fresh:
  local_prefix ctx fn cut s reached /\ stop_view reached = stop_view encoded /\
  (!i. MEM i (fn_insts fn) ==> EVERY (not_fresh_at en) i.inst_outputs) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st encoded
Proof
  strip_tac >> drule_all abi_encode_local_prefix_fresh >>
  drule stop_view_fields >> simp[fresh_vars_wrt_def]
QED

(* The nested dynamic-array observer is block-emitting. Its retained INVOKE
   has no outputs; all generated outputs are below the final frontier. *)
Theorem abi_encode_nested_observer_output_bound:
  !i. MEM i (fn_insts (encode_probe_observer fn)) ==>
    EVERY (not_fresh_at (SND encode_probe_result)) i.inst_outputs
Proof
  `EVERY (\i. EVERY (\x. MEM x
      (MAP (\n. STRING #"%" (toString n)) (GENLIST I 50))) i.inst_outputs)
      (fn_insts (encode_probe_observer fn))` by EVAL_TAC >>
  `EVERY (not_fresh_at (SND encode_probe_result))
      (MAP (\n. STRING #"%" (toString n)) (GENLIST I 50))` by
    (simp[EVERY_MAP, EVERY_GENLIST, not_fresh_at_def,
      ASCIInumbersTheory.toString_inj] >> EVAL_TAC >> simp[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_encode_nested_observer_fresh_probe:
  local_prefix ctx (encode_probe_observer fn) encode_probe_cut s reached /\
  stop_view reached = stop_view encoded /\
  fresh_vars_wrt (SND encode_probe_result) s ==>
  fresh_vars_wrt (SND encode_probe_result) encoded
Proof
  strip_tac >> irule abi_encode_observed_endpoint_fresh >>
  qexistsl [`ctx`, `encode_probe_cut`, `SND encode_probe_result`,
    `encode_probe_observer fn`, `reached`, `s`] >>
  simp[] >> metis_tac[abi_encode_nested_observer_output_bound]
QED
