(* Concrete high-variable frames, independent of the window producer stack. *)
Theory abiEncoderWindowLookup
Ancestors
  venomInstProps venomExecProps venomExecSemantics venomState venomInst
  compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps finite_map list arithmetic

Theorem abi_window_step_non_output:
  step_inst_base inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  ~MEM x inst.inst_outputs ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >>
  `step_inst 0 ctx inst s = OK t` by simp[step_inst_non_invoke] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_terminator_preserves_vars] >>
  metis_tac[step_preserves_non_output_vars]
QED

Theorem abi_window_seq_high_vars:
  !insts en s t.
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
             EVERY (not_fresh_at en) i.inst_outputs) insts ==>
  !x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK s1` >>
  rpt strip_tac >>
  `lookup_var x s1 = lookup_var x s` by
    (irule abi_window_step_non_output >> simp[] >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule >> disch_then (qspec_then `en` mp_tac) >>
  simp[]
QED

Theorem abi_window_seq_fresh:
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
             EVERY (not_fresh_at en) i.inst_outputs) insts /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule abi_window_seq_high_vars >>
  disch_then (qspec_then `en` mp_tac) >> simp[] >> strip_tac >>
  rw[fresh_vars_wrt_def] >>
  `~not_fresh_at en (STRING #"%" (toString n))` by
    (simp[not_fresh_at_def] >> qexists_tac `n` >> simp[]) >>
  first_x_assum drule >>
  gvs[lookup_var_def, fresh_vars_wrt_def, FLOOKUP_DEF]
QED

Theorem abi_window_seq_fresh_idx:
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
             EVERY (not_fresh_at en) i.inst_outputs) insts /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st (t with vs_inst_idx := idx)
Proof
  strip_tac >> drule_all abi_window_seq_fresh >>
  simp[fresh_vars_wrt_def]
QED

Theorem abi_window_emit_register_bounds:
  emit_op opc args st = (out,en) /\ opc <> INVOKE ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\
             EVERY (not_fresh_at en) i.inst_outputs) (emitted_insts st en)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[mk_inst_def, not_fresh_at_def] >> rpt strip_tac >>
  gvs[]
QED

Theorem abi_window_high_vars_trans:
  (!x. ~not_fresh_at mid x ==> lookup_var x t = lookup_var x s) /\
  (!x. ~not_fresh_at en x ==> lookup_var x u = lookup_var x t) /\
  mid.cs_next_var <= en.cs_next_var ==>
  !x. ~not_fresh_at en x ==> lookup_var x u = lookup_var x s
Proof
  rw[] >>
  `~not_fresh_at mid x` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem abi_window_high_vars_idx:
  (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s) ==>
  !x. ~not_fresh_at en x ==>
      lookup_var x (t with vs_inst_idx := ix) = lookup_var x s
Proof
  simp[lookup_var_def]
QED

Theorem abi_window_high_vars_fresh:
  (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> rw[fresh_vars_wrt_def] >>
  `~not_fresh_at en (STRING #"%" (toString n))` by
    (simp[not_fresh_at_def] >> qexists_tac `n` >> simp[]) >>
  first_x_assum drule >>
  gvs[lookup_var_def, fresh_vars_wrt_def, FLOOKUP_DEF]
QED
