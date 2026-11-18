(* Synchronized run composition and planner-field transport for symbolic bodies. *)
Theory symBodyAlgebra
Ancestors
  codegenSymRel stackOpSim

Theorem sym_body_runs_prefix_mode:
  !allow_own lo o2pc prog env own n as as1 ss ss1.
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  sym_steps_mode allow_own prog env own n ss = SymOK ss1 ==>
  !m. asm_steps lo o2pc prog (n + m) as = asm_steps lo o2pc prog m as1 /\
      sym_steps_mode allow_own prog env own (n + m) ss =
        sym_steps_mode allow_own prog env own m ss1
Proof
  rpt strip_tac
  >- metis_tac[asm_steps_add_ok]
  >> simp[sym_steps_mode_add]
QED

Theorem sym_frame_inv_plan_transport_own:
  !ps' ps lo prog env own ctx cp fn ret srest labs0 cs ss.
  ps'.ps_stack = ps.ps_stack /\ ps'.ps_spilled = ps.ps_spilled /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps cs ss ==>
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps' cs ss
Proof
  simp[sym_frame_inv_own_def] >> metis_tac[sym_kinds_ok_plan_transport]
QED
