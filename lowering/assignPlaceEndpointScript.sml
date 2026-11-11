Theory assignPlaceEndpoint
Ancestors
  fragGasMode fragExec compileEnv venomExecProofs venomExecSemantics
  venomInst venomState list rich_list

(* At a positive PC the instruction immediately behind it is the one
   whose nontermination must be retained by an execution invariant. *)
Theorem endpoint_prefix_previous:
  !cs bb.
    isPREFIX cs.cs_current_insts bb.bb_instructions /\
    (0 < LENGTH cs.cs_current_insts ==>
      ~is_terminator
        (EL (LENGTH cs.cs_current_insts - 1) bb.bb_instructions).inst_opcode) ==>
    ~block_is_terminated cs
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `cs.cs_current_insts = []` >- simp[block_is_terminated_def] >>
  `0 < LENGTH cs.cs_current_insts` by
    (Cases_on `cs.cs_current_insts` >> gvs[]) >>
  `EL (LENGTH cs.cs_current_insts - 1) bb.bb_instructions =
   LAST cs.cs_current_insts` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     asm_rewrite_tac[] >> simp[EL_APPEND_EQN, LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  Cases_on `cs.cs_current_insts` >> gvs[block_is_terminated_def]
QED

(* Endpoint diagnostic proof map (not a proved runtime bridge):
   Define the prospective runtime property inline as
     0 < s.vs_inst_idx ==> !bb.
       lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
       ~is_terminator (EL (s.vs_inst_idx - 1) bb.bb_instructions).inst_opcode.

   Every successful gas_path_edge should establish it without an input
   invariant. In the ordinary branch, step_preserves_control_flow preserves
   current_bb and the wrapper sets idx to SUC of the fetched index;
   get_instruction_def identifies that preceding instruction. In the PHI
   entry branch, eval_phis_preserves_current_bb identifies the target block,
   and every index below phi_prefix_length has opcode PHI. The raw jump
   branch sets idx to zero (jump_to_def). All exit_result branches exclude
   OK. Consequently gas_path induction needs the property at its initial
   state only for the reflexive/zero-step case.

   Initialisation: cs_extends + fn_has_code give a fetched block containing
   the initial compiler instruction prefix, whether that block was emitted
   or remains current. An open initial prefix then gives the property AT
   ITS BOUNDARY PC. Extraction at the final compiler boundary uses
   endpoint_prefix_previous above and fn_has_code's final prefix.

   Use-site gap: assign_place_pure_continuation currently gives s0 no
   boundary PC premises. stmt_state_rel has no PC constraints, and
   gas_marked_exec may be reflexive. Its caller in compile_assign_place_case
   DOES have initial PC equalities from stmt_framed_frag. Threading those
   two equalities into this task-created continuation is a helper-interface
   repair, not an additional frozen-root hypothesis. The runtime bridge,
   compiler-prefix initialisation, and this repair remain unproved and
   require strategist review before continuation publication.
*)
