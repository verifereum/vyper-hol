Theory deadStoreElimExecution
Ancestors
  deadStoreElimStepSimulation deadStoreElimSafety deadStoreElimStructure
  deadStoreElimLocal deadStoreElimPending deadStoreElimDefs
  venomExecSemantics venomInst venomState venomWf While list

(* Successful prefixes only: an Error does not introduce another source
   safety obligation. Fuel is local to the instruction (not a bound on this
   reflexive prefix relation); the frozen invariant preserves every fuel. *)
val (dse_source_prefix_rules, dse_source_prefix_ind, dse_source_prefix_cases) =
  Hol_reln `
  (!fn ctx start. dse_source_prefix fn ctx start start) /\
  (!fn ctx start s bb s1.
     dse_source_prefix fn ctx start s /\
     lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     s.vs_inst_idx = 0 /\ eval_phis s bb.bb_instructions = OK s1 ==>
     dse_source_prefix fn ctx start
       (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!fn ctx start s bb inst fuel s1.
     dse_source_prefix fn ctx start s /\
     lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst /\
     step_inst fuel ctx inst s = OK s1 ==>
     dse_source_prefix fn ctx start
       (if is_terminator inst.inst_opcode then s1
        else s1 with vs_inst_idx := SUC s.vs_inst_idx))`;

Theorem dse_source_prefix_safe:
  !fn ctx start s.
    dse_source_prefix fn ctx start s ==>
    !safe_inv.
      safe_inv start /\
      (!bb s0 s1.
        lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
        s0.vs_inst_idx = 0 /\ safe_inv s0 /\
        eval_phis s0 bb.bb_instructions = OK s1 ==>
        safe_inv (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
      (!bb inst fuel s0 s1.
        lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s0.vs_inst_idx = SOME inst /\ safe_inv s0 /\
        step_inst fuel ctx inst s0 = OK s1 ==>
        safe_inv (if is_terminator inst.inst_opcode then s1
                  else s1 with vs_inst_idx := SUC s0.vs_inst_idx)) ==>
      safe_inv s
Proof
  ho_match_mp_tac dse_source_prefix_ind >> rpt conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `safe_inv s` by
    (first_x_assum (qspec_then `safe_inv` irule) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_x_assum irule >> metis_tac[]
QED

(* Replacement is same-index; clearing uses exactly the retained-prefix
   index, rather than an assumed equality with the original cursor. *)
Theorem dse_replaced_clear_occurrence:
  get_instruction bb i = SOME inst /\
  (f inst).inst_opcode <> NOP ==>
  get_instruction (clear_nops_block (block_map_transform f bb))
    (LENGTH (FILTER (\x. x.inst_opcode <> NOP)
       (TAKE i (block_map_transform f bb).bb_instructions))) = SOME (f inst)
Proof
  strip_tac >> irule dse_clear_nops_retained_instruction >>
  simp[get_instruction_block_map_transform]
QED
