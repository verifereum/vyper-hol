(* Original/shadow raw-context comparison fixes the changed GAS sites.
   This static classification does not assert a selected source execution. *)
Theory gasExplicitSites
Ancestors
  gasShadowUnitObservations gasShadowUnit gasShadowState venomFnInstsProofs venomInst venomWf
  list pred_set

(* The set is determined by the original and shadow raw contexts. *)
Definition gas_explicit_sites_def:
  gas_explicit_sites c d =
    {site | ?f g i j.
      MEM f c.ctx_functions /\ MEM g d.ctx_functions /\
      MEM i (fn_insts f) /\ MEM j (fn_insts g) /\
      site = (f.fn_name, i.inst_id) /\
      f.fn_name = g.fn_name /\ i.inst_id = j.inst_id /\
      i.inst_opcode = GAS /\ j.inst_opcode = GASPRICE}
End

Theorem gas_explicit_sites_classify:
  gas_shadow_context c d /\ ctx_inst_ids_distinct c /\
  MEM f c.ctx_functions /\ MEM g d.ctx_functions /\
  gas_shadow_function f g /\
  MEM i (fn_insts f) /\ MEM j (fn_insts g) /\
  gas_shadow_inst i j /\ i.inst_opcode = GAS ==>
  ((f.fn_name, i.inst_id) IN gas_explicit_sites c d <=>
   j.inst_opcode = GASPRICE)
Proof
  strip_tac >>
  `ctx_inst_ids_distinct d` by
    metis_tac[gas_shadow_ctx_inst_ids_distinct] >>
  drule gas_shadow_inst_fields >> strip_tac >>
  drule gas_shadow_function_fields >> strip_tac >>
  simp[gas_explicit_sites_def] >> eq_tac
  >- (strip_tac >>
      rename1 `MEM j' (fn_insts g')` >>
      `j' = j` by (irule venomFnInstsProofsTheory.source_instruction_unique >>
                   conj_tac >- simp[] >>
                   qexistsl [`d`, `g'`, `g`] >> simp[]) >>
      qpat_x_assum `j' = j` (SUBST_ALL_TAC) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> qexistsl [`f`, `g`, `i`, `j`] >> simp[]
QED
