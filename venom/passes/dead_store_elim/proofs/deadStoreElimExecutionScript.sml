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

(* A source witness is retained, not an assertion that arbitrary safe_inv
   holds of the target state. Pending footprints remain an explicit local
   premise, since they depend on the current pass's analysis. *)
Definition dse_coupled_prefix_def:
  dse_coupled_prefix fn ctx start sp P s t <=>
    dse_source_prefix fn ctx start s /\ dse_local_agrees sp P s t
End

Theorem dse_coupled_prefix_initial:
  dse_coupled_prefix fn ctx s sp [] s s
Proof
  simp[dse_coupled_prefix_def, dse_local_agrees_refl,
       dse_source_prefix_rules]
QED

Theorem dse_coupled_prefix_nonterminator:
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  wf_function fn /\
  all_dead_stores ids (cfg_analyze fn) FEMPTY bp sp fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  dse_coupled_prefix fn ctx start sp P s t /\
  dse_pending_at (cfg_analyze fn) bp sp fn bb s.vs_inst_idx P s /\
  alloca_inv s /\ bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s1 ==>
  ?P1 t1. step_inst fuel ctx (dse_inst ids sp inst) t = OK t1 /\
    dse_coupled_prefix fn ctx start sp P1
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at (cfg_analyze fn) bp sp fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  pure_rewrite_tac[dse_coupled_prefix_def] >> strip_tac >>
  drule_all dse_nonterminator_step >> strip_tac >>
  qexistsl_tac [`P1`, `t1`] >> simp[] >>
  metis_tac[dse_source_prefix_rules]
QED

Theorem dse_coupled_prefix_phis:
  dse_coupled_prefix fn ctx start sp P s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx = 0 /\
  dse_pending_at cfg bp sp fn bb 0 P s /\
  eval_phis s bb.bb_instructions = OK s1 ==>
  ?t1. eval_phis t bb.bb_instructions = OK t1 /\
    dse_coupled_prefix fn ctx start sp P
      (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (t1 with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    dse_pending_at cfg bp sp fn bb
      (phi_prefix_length bb.bb_instructions) P s1
Proof
  pure_rewrite_tac[dse_coupled_prefix_def] >> strip_tac >>
  drule_all dse_local_agrees_eval_phis >> strip_tac >>
  qexists_tac `t1` >> simp[] >>
  metis_tac[dse_source_prefix_rules]
QED

Theorem dse_coupled_prefix_terminator:
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  wf_function fn /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  dse_coupled_prefix fn ctx start sp P s t /\
  dse_pending_at (cfg_analyze fn) bp sp fn bb s.vs_inst_idx P s /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s1 /\
  lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb1 ==>
  ?t1. step_inst fuel ctx (dse_inst ids sp inst) t = OK t1 /\
    dse_coupled_prefix fn ctx start sp P s1 t1 /\
    dse_pending_at (cfg_analyze fn) bp sp fn bb1 0 P s1
Proof
  pure_rewrite_tac[dse_coupled_prefix_def] >> strip_tac >>
  drule_all dse_terminator_step >>
  disch_then (qspec_then `ids` strip_assume_tac) >>
  qexists_tac `t1` >> simp[] >>
  metis_tac[dse_source_prefix_rules]
QED

(* WhileTheory.OWHILE_INV_IND:
   !G f s. P s /\ (!x. P x /\ G x ==> P (f x)) ==>
     !s'. OWHILE G f s = SOME s' ==> P s'.
   This supplies induction over completed pass rounds, not correspondence
   of execution prefixes within each round. *)
