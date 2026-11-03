(*
 * Runs of a context and of its DFT schedule, with the same fuel.
 *
 * C' is C with every function rescheduled as dftScheduleOrder describes
 * (dft_fn_rel).  A run of a function of C and the run of its schedule in
 * C', from the function's entry block and with the same fuel, end alike
 * (dft_res_rel): the same continuing, returning or halting state, an
 * abort for an abort, and a revert for a revert.  When the run of C
 * errors, the run of C' does not continue or return either.
 *
 * Why the abort state may differ: the schedule can run instructions with
 * independent effects in another order before an instruction that stops
 * the run (an INVOKE whose callee aborts, a failing ASSERT).  It keeps the
 * fallible instructions in order (dft_fallible_order_kept), so the first
 * one to stop the run is the same on both sides; what can run early is an
 * instruction that cannot stop the run.  ctx_labels_bound keeps one with
 * a label operand (OFFSET) from erroring there.
 *)
Theory dftRunRel
Ancestors
  dftScheduleOrder dftStructural dftDefs venomExecSemantics venomWf
  venomInst venomState venomEffects list finite_map sorting rich_list dftCorrectness

Definition dft_res_rel_def:
  dft_res_rel r r' <=>
    case r of
      OK s => r' = OK s
    | IntRet v s => r' = IntRet v s
    | Halt s => r' = Halt s
    | Abort a s =>
        ?a' s'. r' = Abort a' s' /\ (a = Revert_abort ==> a' = Revert_abort)
    | Error e => (!s. r' <> OK s) /\ (!v s. r' <> IntRet v s)
End

(* Every label an instruction reads as a value is bound in the label map L
   (a state's vs_labels, which no step changes).  Jumps, INVOKE and PHIs
   use their labels as targets, not values. *)
Definition ctx_labels_bound_def:
  ctx_labels_bound C L <=>
    !fn inst l.
      MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
      MEM (Label l) inst.inst_operands /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\ ~is_pseudo inst.inst_opcode ==>
      l IN FDOM L
End

(* fn' is a DFT schedule of the well-formed, ALLOCA-free SSA function fn
   that keeps its fallible instructions in order. *)
Definition dft_fn_rel_def:
  dft_fn_rel fn fn' <=>
    fn'.fn_name = fn.fn_name /\
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\
    LIST_REL dft_block_rel fn.fn_blocks fn'.fn_blocks /\
    dft_fallible_order_kept fn fn'
End

Theorem dft_fn_rel_lookup_function:
  !fs gs name.
    LIST_REL dft_fn_rel fs gs ==>
    OPTREL dft_fn_rel (lookup_function name fs) (lookup_function name gs)
Proof
  Induct >> Cases_on `gs` >>
  simp[lookup_function_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.fn_name = h.fn_name` by fs[dft_fn_rel_def] >>
  simp[] >> IF_CASES_TAC >> gvs[lookup_function_def, lookup_block_def]
QED

Theorem dft_block_rel_lookup_block:
  !bs bs' name.
    LIST_REL dft_block_rel bs bs' ==>
    OPTREL dft_block_rel (lookup_block name bs) (lookup_block name bs')
Proof
  Induct >> Cases_on `bs'` >>
  simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.bb_label = h.bb_label` by fs[dft_block_rel_def] >>
  simp[] >> IF_CASES_TAC >> gvs[lookup_function_def, lookup_block_def]
QED

Theorem dft_fn_rel_entry_label:
  dft_fn_rel fn fn' ==> fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >> fs[dft_fn_rel_def] >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, dft_block_rel_def]
QED

Theorem dft_block_rel_length:
  dft_block_rel bb bb' ==>
  LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[dft_block_rel_def] >>
  drule PERM_LENGTH >> simp[] >>
  strip_tac >>
  `!xs. LENGTH (FILTER (\i. is_pseudo i.inst_opcode) xs) +
        LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) xs) = LENGTH xs`
    suffices_by metis_tac[] >>
  Induct >> simp[] >> gen_tac >>
  Cases_on `is_pseudo h.inst_opcode` >> simp[]
QED

Theorem dft_block_rel_perm_of:
  MEM bb fn.fn_blocks /\ dft_block_rel bb bb' ==> block_perm_of fn bb'
Proof
  rw[dft_block_rel_def] >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) scheduled` by
    (fs[EVERY_MEM, from_block_def] >>
     metis_tac[flip_operands_is_pseudo]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) scheduled = scheduled` by
    simp[FILTER_EQ_ID] >>
  simp[block_perm_of_def] >> qexists_tac `bb` >>
  fs[EVERY_MEM] >>
  simp[FILTER_APPEND_DISTRIB, FILTER_FILTER, FILTER_EQ_ID, FILTER_EQ_NIL,
       GSYM EVERY_NOT_EXISTS, EVERY_MEM]
QED
