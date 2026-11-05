Theory dftCompatibleCrossing
Ancestors
  dftOperationalCrossing dftPositionalFallibleOrder dftOrdinaryStop
  dftOccurrenceFrame dftRunRel venomEffects venomInst venomExecSemantics
  opcodeClass list

Theorem dft_compatible_invoke_partner_success:
  inst_wf x /\ call.inst_opcode = INVOKE /\
  abort_compatible x.inst_opcode call.inst_opcode /\
  ~dft_must_order x call /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. step_inst_base x s = OK t
Proof
  strip_tac >>
  `opcode_fail_class x.inst_opcode = NoFail` by
    metis_tac[dft_invoke_compatible_noninvoke] >>
  drule_all dft_invoke_inversion_disjoint >> strip_tac >>
  irule dft_ordinary_nofail_total >> simp[] >>
  Cases_on `x.inst_opcode` >>
  gvs[is_alloca_op_def, is_pseudo_def, read_effects_def, write_effects_def,
      empty_effects_def, all_effects_def]
QED

Theorem dft_compatible_invoke_operational:
  inst_wf x /\ call.inst_opcode = INVOKE /\
  abort_compatible x.inst_opcode call.inst_opcode /\
  ~dft_must_order x call /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  (!v. MEM v x.inst_outputs ==> ~MEM (Var v) call.inst_operands /\ ~MEM v call.inst_outputs) /\
  (!v. MEM (Var v) x.inst_operands ==> ~MEM v call.inst_outputs) ==>
  dft_operational_crossing_ready x call s
Proof
  strip_tac >>
  drule_all dft_compatible_invoke_partner_success >> strip_tac >>
  drule_all dft_invoke_inversion_disjoint >> strip_tac >>
  simp[dft_operational_crossing_ready_def] >> metis_tac[]
QED

(* Reverse-cut premise audit (no runtime integration asserted here).

   For an extracted positional edge, write the source block as
   pre ++ [x;call] ++ post and the edited block as
   pre ++ [call;x] ++ post.  The guard/edge extractors retain the ORIGINAL
   exclusion ~dft_must_order x call, not its converse.  The compatible
   normalized-path extractor supplies abort compatibility.  Instruction
   shape comes from dft_original_schedule and instruction membership.

   A cut in the edited block at LENGTH pre is a cut at call, not at x.
   dft_original_cut_eval_operand cannot directly be used for x there.
   There is, however, an existing skip boundary:
   dft_original_before_operands (dftOriginalOperands).  Instantiate its
   first instruction with call and its second with x.  It requires the
   ordinary-first schedule_edges fact for the SAME original f,b.  Its
   proof uses dft_original_swap_cut, whose activation-cut proof preserves
   TAKE LENGTH pre; thus this is not an assumption of a fictitious run or
   a returning callee.  dft_original_crossing_cut splits pre into pp++done.

   Labels additionally require ctx_labels_bound C L, source membership
   and s.vs_labels=L.  dft_original_label_iter preserves source membership
   and the label map; ctx_labels_bound_def then covers this non-pseudo,
   non-terminator, non-INVOKE partner.  Literals evaluate unconditionally
   (eval_operand_def).  Neither original_cut nor NoFail implies label
   readiness by itself.

   Still unintegrated: at an actual reverse activation, match the f,b from
   dft_original_runtime_at_projection to the indexed original endpoints
   of the positional edge, so both schedule_edges facts use that SAME
   original.  The needed interface is: original_context Corig C and
   original_context Corig D, D=edit(fi,bi,pre,x,call,post,C), together with
   a live original cut of D's edited block at LENGTH pre, yield a cut of
   C's ordinary-first block at the same state, with indexed original
   f=EL fi Corig.ctx_functions and b=EL bi f.fn_blocks.  Existing runtime
   projection only existentially chooses f,b.  This file does not prove
   that indexed provenance interface, carry root labels through the
   positional transport, or construct recursive crossing certificates.
*)
