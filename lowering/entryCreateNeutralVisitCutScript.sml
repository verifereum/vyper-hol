(* Carry a cut past an administrative window without changing the source
   query. The selected native prefix can be nonempty even with no GAS marks. *)
Theory entryCreateNeutralVisitCut
Ancestors
  entryCreateAdminSequence entryCreateNativeFirstExit entryCreateCompletedCut
  entryCreateFocusSpec entryCreateBodyCut createSizePrefixReplay
  gasSummaryCompose gasSummary

Theorem create_neutral_prefix_visit_cut:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  m.cs_current_bb = a.cs_current_bb /\
  m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts a m) /\
  create_operand_at a s /\ ~s.vs_halted /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_operand_full_scope a m E ctx f s [] (OK u) /\
  create_operand_cut m b E ctx f tops cx st0 source (es,u) ==>
  create_operand_cut a b E ctx f tops cx st0 source (es,s)
Proof
  strip_tac >> simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (`create_operand_cut a m E ctx f tops cx st0 source (es,s)` by
        (irule create_admin_sequence_cut >> simp[]) >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  `t = u /\ create_cut_marks E front = []` by
    (fs[create_operand_at_def] >> drule_all create_operand_full_scope_match >> simp[]) >>
  `gas_explicit (create_cut_marks E back) s.vs_gas_readings =
   gas_explicit (create_cut_marks E back) t.vs_gas_readings` by
    (drule_all create_prefix_gas_path >>
     disch_then (mp_then Any mp_tac gas_explicit_append_path) >>
     simp[gas_explicit_def]) >>
  `create_body_cut E tops cx st0 source (es,t) (back,hit)` by
    metis_tac[create_operand_cut_def] >>
  gvs[create_body_cut_def] >> first_assum ACCEPT_TAC
QED
