(*
 * Step-for-step correspondence of frame runs under a variable renaming,
 * and the ghost transport it gives.
 *
 * frame_sim (o1PassLift) matches each state a frame of fn' reaches with
 * some state of fn, one state at a time.  The ghosts frame_reachable
 * builds along a path (pointer provenance G, taint tn) need more: the
 * matching input states must form a run themselves.  frame_lockstep asks
 * for that run, through a relation R between input and output states:
 *
 *   R p (inst,s) sg (inst',s')
 *
 * sg renames: it maps an output variable to the input variable holding
 * the same value.  A paired state (p) runs the same instruction on both
 * sides, its operands renamed by sg; an unpaired one is an output-only
 * ASSIGN or NOP (a copy a pass inserted), during which the input waits.
 * Paired states sit at the same block, the output at position
 * pos label idx of the input's.  After each step sg may only keep what
 * the step leaves true of every ghost (out_rename_ok, copy_rename_ok,
 * phis_rename_ok); the pass shows the values agree on what it keeps.
 *
 * Every ghost frame_reachable computes is a function of the instruction,
 * its operands' ghosts and values, and the execution frame, so a
 * lockstep carries the ghosts: each state frame_reachable reaches in C'
 * has one in C with equal memory, storage, transient and immutable taint,
 * and provenance and variable taint related through sg, frame by frame
 * down the call stack (frame_reachable_lockstep).  The taint bound
 * follows (taint_within_lockstep).
 *
 * TOP-LEVEL: frame_lockstep, lockstep_sim, lockstep_ctx,
 *   frame_reachable_lockstep, taint_within_lockstep,
 *   frame_reach_lockstep, lockstep_paired_mem_ranges.
 *)
Theory o1FrameLockstep
Ancestors
  o1PassLift ptrDiscipline unitMemInv stateFrame contextCodegenRel
  codegenRel venomExecSemantics venomExecProps venomInst venomState
  list finite_map option pred_set

(* ===== The renaming ===== *)

(* op' is op with its variable renamed by sg (output name to input
   name); other operands are kept. *)
Definition op_rename_def:
  op_rename (sg:(string,string) fmap) op op' <=>
    case op' of
      Var x' => ?x. op = Var x /\ FLOOKUP sg x' = SOME x
    | _ => op' = op
End

(* A paired instruction: same opcode and output count, operands renamed.
   ALLOCA keeps its id, which names its allocation. *)
Definition inst_pair_def:
  inst_pair sg inst inst' <=>
    inst'.inst_opcode = inst.inst_opcode /\
    LIST_REL (op_rename sg) inst.inst_operands inst'.inst_operands /\
    LENGTH inst'.inst_outputs = LENGTH inst.inst_outputs /\
    (inst.inst_opcode = ALLOCA ==> inst'.inst_id = inst.inst_id)
End

Definition vars_rel_def:
  vars_rel sg s s' <=>
    !x' x. FLOOKUP sg x' = SOME x ==> lookup_var x' s' = lookup_var x s
End

(* Equal but for the variables, which agree through sg. *)
Definition state_rel_def:
  state_rel sg s s' <=>
    execution_frame s' = execution_frame s /\
    s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb /\
    vars_rel sg s s'
End

(* After a paired step: an output pairs with an output, anything else
   keeps its pairing and is written by neither side. *)
Definition out_rename_ok_def:
  out_rename_ok sg outs outs' sg' <=>
    !x' x. FLOOKUP sg' x' = SOME x ==>
      (MEM x' outs' /\ MEM x outs) \/
      (~MEM x' outs' /\ ~MEM x outs /\ FLOOKUP sg x' = SOME x)
End

(* After an output-only step: an ASSIGN of a variable takes that
   variable's pairing; anything it doesn't write keeps its own. *)
Definition copy_rename_ok_def:
  copy_rename_ok sg inst' sg' <=>
    !x' x. FLOOKUP sg' x' = SOME x ==>
      (inst'.inst_opcode = ASSIGN /\ inst'.inst_outputs = [x'] /\
       ?z'. inst'.inst_operands = [Var z'] /\ FLOOKUP sg z' = SOME x) \/
      (~MEM x' inst'.inst_outputs /\ FLOOKUP sg x' = SOME x)
End

(* What the leading PHIs of insts write to x, entering from prev: NONE if
   none writes it; SOME (SOME op) if the first that does copies op;
   SOME NONE if it leaves x without a ghost. *)
Definition phi_read_def:
  (phi_read prev x [] = NONE) /\
  (phi_read prev x (inst::rest) =
     if inst.inst_opcode <> PHI then NONE
     else if MEM x inst.inst_outputs then
       SOME (if inst.inst_outputs = [x] then
               case prev of
                 NONE => NONE
               | SOME l => resolve_phi l inst.inst_operands
             else NONE)
     else phi_read prev x rest)
End

(* The operand x holds after the PHIs, read before them. *)
Definition phi_eff_def:
  phi_eff prev x insts =
    case phi_read prev x insts of
      NONE => SOME (Var x)
    | SOME r => r
End

Definition block_insts_def:
  block_insts fn lbl =
    case lookup_block lbl fn.fn_blocks of
      SOME bb => bb.bb_instructions
    | NONE => []
End

(* After entering a block: a pairing reads, through the PHIs, operands
   the old renaming pairs. *)
Definition phis_rename_ok_def:
  phis_rename_ok prev sg insts insts' sg1 <=>
    !x' x. FLOOKUP sg1 x' = SOME x ==>
      OPTREL (op_rename sg) (phi_eff prev x insts) (phi_eff prev x' insts')
End

(* ===== The lockstep ===== *)

(* R relates the states of a frame of fn in C with those of a frame of fn'
   in C' from the same entry state, for entry states with label table L.
   Every output step is matched: an unpaired one (an ASSIGN, or a NOP with
   no operands) stays at the same input
   state; a paired one takes the same step there, to an equal execution
   frame; after a paired INVOKE, matching returns resume in R again. *)
Definition lockstep_sim_def:
  lockstep_sim L C C' fn fn' (pos:string -> num -> num) R <=>
    (!p inst s sg inst' s'.
       R p (inst,s) sg (inst',s') ==>
       active_inst fn inst s /\ active_inst fn' inst' s' /\
       state_rel sg s s' /\
       (p ==> inst_pair sg inst inst' /\
              s'.vs_inst_idx = pos s.vs_current_bb s.vs_inst_idx) /\
       (~p ==> inst'.inst_opcode = ASSIGN \/
               (inst'.inst_opcode = NOP /\ inst'.inst_operands = []))) /\
    (!s0 s1' inst'.
       fn_entry_state fn s0 /\ s0.vs_labels = L /\
       enters_block fn' s0 s1' /\ active_inst fn' inst' s1' ==>
       ?p inst s1 sg. enters_block fn s0 s1 /\ R p (inst,s1) sg (inst',s1')) /\
    (!inst s sg inst' s' t' j' fuel.
       R F (inst,s) sg (inst',s') /\ step_inst fuel C' inst' s' = OK t' /\
       active_inst fn' j' (t' with vs_inst_idx := SUC s'.vs_inst_idx) ==>
       ?p sg'. R p (inst,s) sg' (j', t' with vs_inst_idx := SUC s'.vs_inst_idx) /\
               copy_rename_ok sg inst' sg') /\
    (!inst s sg inst' s' fuel t'.
       R T (inst,s) sg (inst',s') /\ inst'.inst_opcode <> INVOKE /\
       step_inst fuel C' inst' s' = OK t' ==>
       ?t. step_inst fuel C inst s = OK t /\
           execution_frame t' = execution_frame t /\
           (~is_terminator inst'.inst_opcode ==>
            !j'. active_inst fn' j' (t' with vs_inst_idx := SUC s'.vs_inst_idx) ==>
              ?p j sg'.
                R p (j, t with vs_inst_idx := SUC s.vs_inst_idx) sg'
                  (j', t' with vs_inst_idx := SUC s'.vs_inst_idx) /\
                out_rename_ok sg inst.inst_outputs inst'.inst_outputs sg') /\
           (is_terminator inst'.inst_opcode ==>
            t'.vs_current_bb = t.vs_current_bb /\
            t'.vs_prev_bb = t.vs_prev_bb /\
            !t1' j'. ~t'.vs_halted /\ enters_block fn' t' t1' /\
                     active_inst fn' j' t1' ==>
              ?p j t1 sg1. enters_block fn t t1 /\ R p (j,t1) sg1 (j',t1') /\
                phis_rename_ok t.vs_prev_bb sg
                  (block_insts fn t.vs_current_bb)
                  (block_insts fn' t.vs_current_bb) sg1)) /\
    (!inst s sg inst' s' fuel v e'.
       R T (inst,s) sg (inst',s') /\ inst'.inst_opcode <> INVOKE /\
       step_inst fuel C' inst' s' = IntRet v e' ==>
       ?e. step_inst fuel C inst s = IntRet v e /\
           execution_frame e' = execution_frame e) /\
    (!inst s sg inst' s' fuel h'.
       R T (inst,s) sg (inst',s') /\ inst'.inst_opcode <> INVOKE /\
       step_inst fuel C' inst' s' = Halt h' ==>
       ?h. step_inst fuel C inst s = Halt h /\
           execution_frame h' = execution_frame h) /\
    (!inst s sg inst' s' ret e e' t' j'.
       R T (inst,s) sg (inst',s') /\ inst'.inst_opcode = INVOKE /\
       execution_frame e' = execution_frame e /\
       bind_outputs inst'.inst_outputs ret.iret_values
         (adopt_return_fmp ret (merge_callee_state s' e')) = SOME t' /\
       active_inst fn' j' (t' with vs_inst_idx := SUC s'.vs_inst_idx) ==>
       ?p j t sg'.
         bind_outputs inst.inst_outputs ret.iret_values
           (adopt_return_fmp ret (merge_callee_state s e)) = SOME t /\
         R p (j, t with vs_inst_idx := SUC s.vs_inst_idx) sg'
           (j', t' with vs_inst_idx := SUC s'.vs_inst_idx) /\
         out_rename_ok sg inst.inst_outputs inst'.inst_outputs sg')
End

(* Positions advance together within a block. *)
Definition frame_lockstep_def:
  frame_lockstep L C C' fn fn' pos <=>
    (!l k. pos l (SUC k) = SUC (pos l k)) /\
    ?R. lockstep_sim L C C' fn fn' pos R
End

(* Two stage contexts whose functions are in lockstep pairwise, with a
   side condition Q on each pair and its position map. *)
Definition lockstep_ctx_def:
  lockstep_ctx Q L C C' <=>
    C'.ctx_entry = C.ctx_entry /\
    LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                       fn_entry_label fn' = fn_entry_label fn /\
                       ?pos. frame_lockstep L C C' fn fn' pos /\
                             Q fn fn' pos)
      C.ctx_functions C'.ctx_functions
End

(* ===== Ghost relation ===== *)

Definition var_taint_def:
  var_taint (tv:(string, num set) fmap) x =
    case FLOOKUP tv x of SOME m => m | NONE => {}
End

(* Provenance and variable taint agree through sg. *)
Definition vars_ghost_rel_def:
  vars_ghost_rel sg (G:(string, num # num) fmap) tv G' tv' <=>
    !x' x. FLOOKUP sg x' = SOME x ==>
      FLOOKUP G' x' = FLOOKUP G x /\ var_taint tv' x' = var_taint tv x
End

(* The ghosts of corresponding states: the byte taints are equal. *)
Definition ghost_rel_def:
  ghost_rel sg G tn G' tn' <=>
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    vars_ghost_rel sg G tn.t_var G' tn'.t_var
End

(* ===== Basic facts ===== *)

Theorem execution_frame_fields:
  execution_frame s' = execution_frame s ==>
  s'.vs_labels = s.vs_labels /\ s'.vs_allocas = s.vs_allocas /\
  s'.vs_alloca_next = s.vs_alloca_next /\ s'.vs_fmp = s.vs_fmp /\
  s'.vs_initial_fmp = s.vs_initial_fmp /\
  s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
  s'.vs_returndata = s.vs_returndata /\ s'.vs_requests = s.vs_requests /\
  s'.vs_outcomes = s.vs_outcomes /\ s'.vs_call_ctx = s.vs_call_ctx /\
  s'.vs_halted = s.vs_halted /\ s'.vs_accounts = s.vs_accounts /\
  s'.vs_transient = s.vs_transient /\ s'.vs_immutables = s.vs_immutables /\
  s'.vs_memory = s.vs_memory
Proof
  strip_tac >> fs[execution_frame_def, venom_state_component_equality]
QED

Theorem vars_rel_inst_idx[simp]:
  (vars_rel sg (s with vs_inst_idx := k) s' <=> vars_rel sg s s') /\
  (vars_rel sg s (s' with vs_inst_idx := k) <=> vars_rel sg s s')
Proof
  simp[vars_rel_def, lookup_var_def]
QED

Theorem op_rename_not_var:
  op_rename sg op op' /\ (!x. op <> Var x) ==> op' = op
Proof
  Cases_on `op'` >> simp[op_rename_def] >> metis_tac[]
QED

Theorem op_rename_eval:
  op_rename sg op op' /\ vars_rel sg s s' /\ s'.vs_labels = s.vs_labels ==>
  eval_operand op' s' = eval_operand op s
Proof
  Cases_on `op'` >> simp[op_rename_def] >> rpt strip_tac >>
  gvs[eval_operand_def, vars_rel_def]
QED

Theorem op_rename_ghost:
  op_rename sg op op' /\ vars_ghost_rel sg G tn.t_var G' tn'.t_var ==>
  op_prov G' op' = op_prov G op /\ op_taint tn' op' = op_taint tn op
Proof
  Cases_on `op'` >> simp[op_rename_def] >> rpt strip_tac >>
  gvs[op_prov_def, op_taint_def, vars_ghost_rel_def] >>
  first_x_assum drule >> simp[var_taint_def]
QED

Theorem op_taint_var:
  op_taint tn (Var x) = var_taint tn.t_var x
Proof
  simp[op_taint_def, var_taint_def]
QED

Theorem op_rename_label:
  op_rename sg op (Label l) <=> op = Label l
Proof
  simp[op_rename_def] >> metis_tac[]
QED

Theorem op_rename_lit:
  op_rename sg op (Lit w) <=> op = Lit w
Proof
  simp[op_rename_def] >> metis_tac[]
QED

Theorem op_rename_lit_src:
  op_rename sg (Lit w) op' <=> op' = Lit w
Proof
  Cases_on `op'` >> simp[op_rename_def]
QED

Theorem LIST_REL_op_rename_eval:
  !ops ops'. LIST_REL (op_rename sg) ops ops' /\ vars_rel sg s s' /\
    s'.vs_labels = s.vs_labels ==>
    LIST_REL (\op op'. op_rename sg op op' /\
                       eval_operand op' s' = eval_operand op s) ops ops'
Proof
  Induct >> simp[PULL_EXISTS] >> rpt strip_tac >>
  metis_tac[op_rename_eval]
QED

Theorem eval_operands_rel:
  !ops ops'. LIST_REL (\op op'. op_rename sg op op' /\
                                eval_operand op' s' = eval_operand op s)
               ops ops' ==>
    eval_operands ops' s' = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, PULL_EXISTS] >> rpt strip_tac >>
  simp[eval_operands_def]
QED

Theorem first_prov_rename:
  !ops ops'. LIST_REL (op_rename sg) ops ops' /\
    vars_ghost_rel sg G tn.t_var G' tn'.t_var ==>
    first_prov G' ops' = first_prov G ops
Proof
  Induct >> simp[first_prov_def, PULL_EXISTS] >> rpt strip_tac >>
  drule_all op_rename_ghost >> strip_tac >> simp[first_prov_def]
QED

Theorem map_op_prov_rename:
  !ops ops'. LIST_REL (op_rename sg) ops ops' /\
    vars_ghost_rel sg G tn.t_var G' tn'.t_var ==>
    MAP (op_prov G') ops' = MAP (op_prov G) ops
Proof
  Induct >> simp[PULL_EXISTS] >> rpt strip_tac >>
  drule_all op_rename_ghost >> simp[]
QED

Theorem parse_dret_shape_rename:
  LIST_REL (op_rename sg) inst.inst_operands inst'.inst_operands ==>
  parse_dret_shape inst' = parse_dret_shape inst
Proof
  strip_tac >> imp_res_tac LIST_REL_LENGTH >>
  simp[dretShapeDefsTheory.parse_dret_shape_def] >>
  Cases_on `inst.inst_operands` >> Cases_on `inst'.inst_operands` >> gvs[] >>
  Cases_on `h` >> Cases_on `h'` >> gvs[op_rename_def]
QED

(* The operands of a paired instruction, with their values. *)
Definition ops_pair_def:
  ops_pair sg s s' ops ops' <=>
    LIST_REL (\op op'. op_rename sg op op' /\
                       eval_operand op' s' = eval_operand op s) ops ops'
End

Theorem ops_pair_rename:
  ops_pair sg s s' ops ops' ==> LIST_REL (op_rename sg) ops ops'
Proof
  rw[ops_pair_def] >> irule LIST_REL_mono >>
  first_assum (irule_at Any) >> simp[]
QED

Theorem inst_pair_ops:
  inst_pair sg inst inst' /\ state_rel sg s s' ==>
  ops_pair sg s s' inst.inst_operands inst'.inst_operands
Proof
  rw[inst_pair_def, state_rel_def, ops_pair_def] >>
  irule LIST_REL_op_rename_eval >> simp[] >>
  metis_tac[execution_frame_fields]
QED

Theorem write_ranges_pair:
  inst'.inst_opcode = inst.inst_opcode /\
  ops_pair sg s s' inst.inst_operands inst'.inst_operands /\
  s'.vs_call_entry_fmp = s.vs_call_entry_fmp ==>
  source_memory_write_ranges inst' s' = source_memory_write_ranges inst s
Proof
  strip_tac >>
  `eval_operands inst'.inst_operands s' = eval_operands inst.inst_operands s` by
    (irule eval_operands_rel >> fs[ops_pair_def] >> metis_tac[]) >>
  `parse_dret_shape inst' = parse_dret_shape inst` by
    metis_tac[parse_dret_shape_rename, ops_pair_rename] >>
  fs[ops_pair_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[codegenRelTheory.source_memory_write_ranges_def] >>
  simp[codegenRelTheory.fixed_source_write_range_def,
       codegenRelTheory.sized_source_write_range_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os3` ["", "o4 os4"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os4` ["", "o5 os5"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os5` ["", "o6 os6"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os6` ["", "o7 os7"] >> gvs[LIST_REL_CONS1] >>
  Cases_on `os7` >> gvs[LIST_REL_CONS1]
QED

Theorem read_ranges_other:
  ~MEM inst.inst_opcode [MLOAD; ILOAD; MCOPY; DRET; RETURN; REVERT; SHA3; LOG;
                         CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  source_memory_read_ranges inst s = []
Proof
  simp[contextCodegenRelTheory.source_memory_read_ranges_def] >>
  Cases_on `inst.inst_opcode` >> simp[]
QED

Theorem read_ranges_pair:
  inst'.inst_opcode = inst.inst_opcode /\
  ops_pair sg s s' inst.inst_operands inst'.inst_operands ==>
  source_memory_read_ranges inst' s' = source_memory_read_ranges inst s
Proof
  strip_tac >>
  `eval_operands inst'.inst_operands s' = eval_operands inst.inst_operands s` by
    (irule eval_operands_rel >> fs[ops_pair_def] >> metis_tac[]) >>
  `parse_dret_shape inst' = parse_dret_shape inst` by
    metis_tac[parse_dret_shape_rename, ops_pair_rename] >>
  fs[ops_pair_def] >>
  Cases_on `inst.inst_opcode = LOG` >- suspend "log" >>
  Cases_on `MEM inst.inst_opcode [MLOAD; ILOAD; MCOPY; DRET; RETURN; REVERT;
              SHA3; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` >>
  TRY (`source_memory_read_ranges inst s = [] /\
        source_memory_read_ranges inst' s' = []` by
         (conj_tac >> irule read_ranges_other >> gvs[]) >> simp[] >> NO_TAC) >>
  pop_assum (strip_assume_tac o SIMP_RULE list_ss []) >>
  gvs[contextCodegenRelTheory.source_memory_read_ranges_def,
      contextCodegenRelTheory.dret_memory_read_ranges_def,
      contextCodegenRelTheory.memory_range_of_operands_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os3` ["", "o4 os4"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os4` ["", "o5 os5"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os5` ["", "o6 os6"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os6` ["", "o7 os7"] >> gvs[LIST_REL_CONS1] >>
  Cases_on `os7` >> gvs[LIST_REL_CONS1]
QED

Resume read_ranges_pair[log]:
  simp[contextCodegenRelTheory.source_memory_read_ranges_def,
       contextCodegenRelTheory.memory_range_of_operands_def] >>
  Cases_on `inst.inst_operands` >> gvs[LIST_REL_CONS1] >>
  rename1 `op_rename sg h hh` >>
  qpat_x_assum `op_rename sg h hh` mp_tac >>
  Cases_on `h` >> Cases_on `hh` >> simp[op_rename_def] >> strip_tac >> gvs[] >>
  imp_res_tac LIST_REL_LENGTH >> simp[] >> IF_CASES_TAC >> simp[] >>
  qmatch_asmsub_abbrev_tac `LIST_REL RR t t'` >>
  `LIST_REL RR (REVERSE t) (REVERSE t')` by simp[] >>
  `LIST_REL RR (DROP 2 (REVERSE t)) (DROP 2 (REVERSE t'))` by
    simp[rich_listTheory.EVERY2_DROP] >>
  `eval_operands (DROP 2 (REVERSE t')) s' =
   eval_operands (DROP 2 (REVERSE t)) s` by
    (irule eval_operands_rel >> qexists_tac `sg` >> gvs[Abbr `RR`]) >>
  `RR (EL 0 (REVERSE t)) (EL 0 (REVERSE t')) /\
   RR (EL 1 (REVERSE t)) (EL 1 (REVERSE t'))` by
    (qpat_x_assum `LIST_REL RR (REVERSE t) (REVERSE t')` mp_tac >>
     rewrite_tac[LIST_REL_EL_EQN, LENGTH_REVERSE] >> strip_tac >>
     conj_tac >> first_x_assum irule >> simp[]) >>
  gvs[Abbr `RR`]
QED

Finalise read_ranges_pair

Theorem inst_mem_ranges_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' ==>
  inst_mem_ranges inst' s' = inst_mem_ranges inst s
Proof
  strip_tac >> drule_all inst_pair_ops >> strip_tac >>
  fs[inst_pair_def, state_rel_def] >> imp_res_tac execution_frame_fields >>
  simp[inst_mem_ranges_def] >> metis_tac[read_ranges_pair, write_ranges_pair]
QED

(* ===== Ghost updates ===== *)

Theorem FLOOKUP_set_prov:
  FLOOKUP (set_prov G outs p) y =
    if MEM y outs then (if outs = [y] then p else NONE) else FLOOKUP G y
Proof
  Cases_on `outs` >> simp[set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> Cases_on `p` >>
  simp[set_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rw[] >> gvs[]
QED

Theorem var_taint_set:
  var_taint (set_var_taint tv outs m) y =
    if MEM y outs then (if outs = [y] then m else {}) else var_taint tv y
Proof
  Cases_on `outs` >>
  simp[set_var_taint_def, var_taint_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >>
  simp[set_var_taint_def, var_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rw[] >> gvs[]
QED

Theorem var_taint_DRESTRICT:
  var_taint (DRESTRICT tv X) y = if y IN X then var_taint tv y else {}
Proof
  simp[var_taint_def, FLOOKUP_DRESTRICT] >> rw[]
QED

Theorem MEM_singleton_length:
  MEM x l ==> (l = [x] <=> LENGTH l = 1)
Proof
  Cases_on `l` >> simp[] >> Cases_on `t` >> simp[] >> metis_tac[]
QED

(* Writing equal ghosts to paired outputs keeps the relation. *)
Theorem set_ghost_rel:
  out_rename_ok sg outs outs' sg' /\ LENGTH outs' = LENGTH outs /\
  vars_ghost_rel sg G tv G' tv' /\
  (!x x'. outs = [x] /\ outs' = [x'] /\ FLOOKUP sg' x' = SOME x ==>
          p' = p /\ m' = m) ==>
  vars_ghost_rel sg' (set_prov G outs p) (set_var_taint tv outs m)
                     (set_prov G' outs' p') (set_var_taint tv' outs' m')
Proof
  simp[vars_ghost_rel_def, out_rename_ok_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!x' x. FLOOKUP sg' _ = _ ==> _` drule >> strip_tac
  >- (`(outs' = [x'] <=> LENGTH outs' = 1) /\ (outs = [x] <=> LENGTH outs = 1)`
        by metis_tac[MEM_singleton_length] >>
      simp[FLOOKUP_set_prov, var_taint_set] >>
      Cases_on `LENGTH outs = 1` >> gvs[] >>
      first_x_assum (qspecl_then [`x`, `x'`] mp_tac) >> simp[]) >>
  simp[FLOOKUP_set_prov, var_taint_set]
QED

Theorem ret_ghost_rel:
  vars_ghost_rel sg G tv G' tv' /\ out_rename_ok sg outs outs' sg' ==>
  vars_ghost_rel sg' (DRESTRICT G (COMPL (set outs)))
                     (DRESTRICT tv (COMPL (set outs)))
                     (DRESTRICT G' (COMPL (set outs')))
                     (DRESTRICT tv' (COMPL (set outs')))
Proof
  rw[vars_ghost_rel_def, out_rename_ok_def] >>
  first_x_assum drule >> strip_tac >>
  simp[FLOOKUP_DRESTRICT, var_taint_DRESTRICT] >> metis_tac[]
QED

(* The operands of a paired instruction carry equal values and ghosts. *)
Theorem inst_pair_ops_ghost:
  inst_pair sg inst inst' /\ state_rel sg s s' /\
  vars_ghost_rel sg G tn.t_var G' tn'.t_var ==>
  LIST_REL (\op op'. eval_operand op' s' = eval_operand op s /\
                     op_taint tn' op' = op_taint tn op /\
                     op_prov G' op' = op_prov G op /\ op_rename sg op op')
    inst.inst_operands inst'.inst_operands
Proof
  strip_tac >> drule_all inst_pair_ops >> rw[ops_pair_def] >>
  irule LIST_REL_mono >> first_assum (irule_at Any) >> rw[] >>
  metis_tac[op_rename_ghost]
QED

Theorem out_taint_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' /\ ghost_rel sg G tn G' tn' ==>
  out_taint tn' inst' s' = out_taint tn inst s
Proof
  rw[ghost_rel_def] >> drule_all inst_pair_ops_ghost >> strip_tac >>
  fs[inst_pair_def] >> simp[out_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[LIST_REL_CONS1]
QED

Theorem written_taint_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' /\ ghost_rel sg G tn G' tn' ==>
  written_taint tn' inst' s' = written_taint tn inst s
Proof
  rw[ghost_rel_def] >> drule_all inst_pair_ops_ghost >> strip_tac >>
  fs[inst_pair_def] >> simp[written_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os3` ["", "o4 os4"] >> gvs[LIST_REL_CONS1]
QED

Theorem store_taint_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' /\ ghost_rel sg G tn G' tn' ==>
  store_taint opc tn' inst' s' X = store_taint opc tn inst s X
Proof
  rw[ghost_rel_def] >> drule_all inst_pair_ops_ghost >> strip_tac >>
  fs[inst_pair_def] >> simp[store_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[LIST_REL_CONS1]
QED

Theorem imm_taint_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' /\ ghost_rel sg G tn G' tn' ==>
  imm_taint tn' inst' s' = imm_taint tn inst s
Proof
  rw[ghost_rel_def] >> drule_all inst_pair_ops_ghost >> strip_tac >>
  fs[inst_pair_def] >> simp[imm_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[LIST_REL_CONS1]
QED

Theorem ret_taint_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' /\ ghost_rel sg G tn G' tn' ==>
  ret_taint tn' inst' s' = ret_taint tn inst s
Proof
  rw[ghost_rel_def] >> drule_all inst_pair_ops_ghost >> strip_tac >>
  fs[inst_pair_def] >> simp[ret_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[LIST_REL_CONS1] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[LIST_REL_CONS1]
QED

Theorem out_prov_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' /\ ghost_rel sg G tn G' tn' /\
  execution_frame t' = execution_frame t /\
  (!x x'. inst.inst_outputs = [x] /\ inst'.inst_outputs = [x'] ==>
          lookup_var x' t' = lookup_var x t) ==>
  out_prov PG G' inst' t' = out_prov PG G inst t
Proof
  rw[ghost_rel_def] >> drule_all inst_pair_ops_ghost >> strip_tac >>
  `LIST_REL (op_rename sg) inst.inst_operands inst'.inst_operands` by
    fs[inst_pair_def] >>
  `first_prov G' inst'.inst_operands = first_prov G inst.inst_operands` by
    metis_tac[first_prov_rename] >>
  imp_res_tac execution_frame_fields >>
  fs[inst_pair_def] >> simp[out_prov_def] >>
  Cases_on `inst.inst_opcode = ALLOCA` >> gvs[] >>
  Cases_on `inst.inst_opcode = DALLOCA` >> gvs[]
  >- (namedCases_on `inst.inst_outputs` ["", "x xs"] >> gvs[] >>
      Cases_on `inst'.inst_outputs` >> gvs[] >>
      Cases_on `xs` >> gvs[] >> Cases_on `t''` >> gvs[]) >>
  Cases_on `inst.inst_opcode = PARAM` >> gvs[] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[LIST_REL_CONS1] >>
  rename1 `op_rename sg o1 oo` >>
  qpat_x_assum `op_rename sg o1 oo` mp_tac >>
  Cases_on `o1` >> Cases_on `oo` >> simp[op_rename_def] >> rpt strip_tac >>
  gvs[] >> BasicProvers.every_case_tac >> gvs[]
QED

Theorem step_writes_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' /\
  execution_frame t' = execution_frame t ==>
  step_writes inst' s' t' = step_writes inst s t
Proof
  strip_tac >> drule_all inst_pair_ops >> strip_tac >>
  imp_res_tac execution_frame_fields >>
  fs[inst_pair_def, state_rel_def] >> imp_res_tac execution_frame_fields >>
  `source_memory_write_ranges inst' s' = source_memory_write_ranges inst s` by
    metis_tac[write_ranges_pair] >>
  simp[step_writes_def]
QED

Theorem new_site_bytes_frame:
  execution_frame s' = execution_frame s /\
  execution_frame t' = execution_frame t ==>
  new_site_bytes s' t' = new_site_bytes s t
Proof
  strip_tac >> imp_res_tac execution_frame_fields >> simp[new_site_bytes_def]
QED

(* A paired step updates the ghosts alike. *)
Theorem step_ghost_pair:
  inst_pair sg inst inst' /\ state_rel sg s s' /\
  execution_frame t' = execution_frame t /\ vars_rel sg' t t' /\
  out_rename_ok sg inst.inst_outputs inst'.inst_outputs sg' /\
  ghost_rel sg G tn G' tn' ==>
  ghost_rel sg' (step_prov PG G inst t) (step_taint inst s t tn)
                (step_prov PG G' inst' t') (step_taint inst' s' t' tn')
Proof
  strip_tac >>
  `out_taint tn' inst' s' = out_taint tn inst s` by metis_tac[out_taint_pair] >>
  `written_taint tn' inst' s' = written_taint tn inst s` by
    metis_tac[written_taint_pair] >>
  `!X opc. store_taint opc tn' inst' s' X = store_taint opc tn inst s X` by
    metis_tac[store_taint_pair] >>
  `imm_taint tn' inst' s' = imm_taint tn inst s` by metis_tac[imm_taint_pair] >>
  `step_writes inst' s' t' = step_writes inst s t` by
    metis_tac[step_writes_pair] >>
  `execution_frame s' = execution_frame s` by fs[state_rel_def] >>
  `new_site_bytes s' t' = new_site_bytes s t` by
    metis_tac[new_site_bytes_frame] >>
  imp_res_tac execution_frame_fields >>
  `inst'.inst_opcode = inst.inst_opcode /\
   LENGTH inst'.inst_outputs = LENGTH inst.inst_outputs` by fs[inst_pair_def] >>
  fs[ghost_rel_def] >>
  simp[step_taint_def, step_prov_def, mem_taint_def, adopt_reset_def] >>
  irule set_ghost_rel >> simp[] >> reverse conj_tac >- (qexists `sg` >> simp[]) >>
  rpt strip_tac >>
  mp_tac (SPEC_ALL out_prov_pair) >> simp[] >> impl_tac >- gvs[ghost_rel_def, vars_rel_def] >>
  simp[]
QED

Theorem step_inst_copy:
  (inst'.inst_opcode = ASSIGN \/ inst'.inst_opcode = NOP) /\
  step_inst fuel C inst' s' = OK t' ==>
  (inst'.inst_opcode = NOP /\ t' = s') \/
  (?x' op v. inst'.inst_opcode = ASSIGN /\ inst'.inst_operands = [op] /\
             inst'.inst_outputs = [x'] /\ eval_operand op s' = SOME v /\
             t' = update_var x' v s')
Proof
  strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
QED

Theorem step_inst_copy_not_intret:
  (inst'.inst_opcode = ASSIGN \/ inst'.inst_opcode = NOP) ==>
  (!v e. step_inst fuel C inst' s' <> IntRet v e) /\
  (!h. step_inst fuel C inst' s' <> Halt h)
Proof
  strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
QED

Theorem step_inst_invoke_not_intret:
  inst.inst_opcode = INVOKE ==> step_inst fuel C inst s <> IntRet v e
Proof
  rw[Once step_inst_def] >> BasicProvers.every_case_tac >> simp[]
QED

(* An output-only copy leaves the frame and all but its output's ghosts. *)
Theorem step_ghost_copy:
  (inst'.inst_opcode = ASSIGN \/ inst'.inst_opcode = NOP) /\
  step_inst fuel C inst' s' = OK t' /\
  copy_rename_ok sg inst' sg' /\ ghost_rel sg G tn G' tn' ==>
  execution_frame t' = execution_frame s' /\
  ghost_rel sg' G tn (step_prov PG G' inst' t') (step_taint inst' s' t' tn')
Proof
  strip_tac >> drule_at (Pos last) step_inst_copy >> (impl_tac >- fs[]) >>
  strip_tac >>
  `inst'.inst_opcode <> MSTORE /\ inst'.inst_opcode <> ISTORE /\
   inst'.inst_opcode <> MCOPY /\ inst'.inst_opcode <> CALL /\
   inst'.inst_opcode <> SSTORE /\ inst'.inst_opcode <> TSTORE /\
   inst'.inst_opcode <> STATICCALL /\ inst'.inst_opcode <> DELEGATECALL` by
    gvs[] >>
  `written_taint tn' inst' s' = {}` by
    (simp[written_taint_def] >> BasicProvers.every_case_tac >> gvs[]) >>
  `source_memory_write_ranges inst' s' = []` by
    gvs[codegenRelTheory.source_memory_write_ranges_def] >>
  `new_site_bytes s' t' = {}` by
    (gvs[new_site_bytes_def, update_var_def, pred_setTheory.EXTENSION,
         finite_mapTheory.flookup_thm] >> metis_tac[]) >>
  gvs[update_var_def, step_taint_def, step_prov_def, mem_taint_def,
      step_writes_def, range_bytes_def, store_taint_def,
      imm_taint_def, adopt_reset_def, ghost_rel_def] >>
  gvs[vars_ghost_rel_def, copy_rename_ok_def, FLOOKUP_set_prov,
      var_taint_set] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[out_prov_def, out_taint_def, first_prov_def, op_prov_def,
      eval_operand_def, lookup_var_def, op_taint_var] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[]
QED

(* ===== Entering a block ===== *)

Theorem FLOOKUP_phis_prov:
  !insts. FLOOKUP (phis_prov prev G0 insts) x =
    case phi_eff prev x insts of NONE => NONE | SOME op => op_prov G0 op
Proof
  Induct >> simp[phis_prov_def, phi_eff_def, phi_read_def, op_prov_def] >>
  rw[FLOOKUP_set_prov, phi_prov_def] >> gvs[phi_eff_def] >>
  BasicProvers.every_case_tac >> gvs[op_prov_def]
QED

Theorem var_taint_phis_taint:
  !insts. var_taint (phis_taint prev T0 insts) x =
    case phi_eff prev x insts of NONE => {} | SOME op => op_taint T0 op
Proof
  Induct >> simp[phis_taint_def, phi_eff_def, phi_read_def, op_taint_var] >>
  rw[var_taint_set, phi_taint_def] >> gvs[phi_eff_def] >>
  BasicProvers.every_case_tac >> gvs[op_taint_def, var_taint_def]
QED

Theorem phis_ghost_rel:
  phis_rename_ok prev sg insts insts' sg1 /\
  vars_ghost_rel sg G T0.t_var G' T0'.t_var ==>
  vars_ghost_rel sg1 (phis_prov prev G insts) (phis_taint prev T0 insts)
                     (phis_prov prev G' insts') (phis_taint prev T0' insts')
Proof
  strip_tac >>
  simp[vars_ghost_rel_def, FLOOKUP_phis_prov, var_taint_phis_taint] >>
  rpt gen_tac >> strip_tac >> fs[phis_rename_ok_def] >>
  first_x_assum drule >>
  Cases_on `phi_eff prev x insts` >> Cases_on `phi_eff prev x' insts'` >>
  simp[] >> metis_tac[op_rename_ghost]
QED

Theorem entry_ghost_block_insts:
  entry_prov fn s G = phis_prov s.vs_prev_bb G (block_insts fn s.vs_current_bb) /\
  entry_taint_vars fn s tn =
    tn with t_var := phis_taint s.vs_prev_bb tn (block_insts fn s.vs_current_bb)
Proof
  simp[entry_prov_def, entry_taint_vars_def, block_insts_def] >>
  CASE_TAC >> simp[phis_prov_def, phis_taint_def, taint_component_equality]
QED

Theorem entry_ghost_rel:
  ghost_rel sg G tn G' tn' /\
  phis_rename_ok t.vs_prev_bb sg (block_insts fn t.vs_current_bb)
    (block_insts fn' t.vs_current_bb) sg1 /\
  t'.vs_current_bb = t.vs_current_bb /\ t'.vs_prev_bb = t.vs_prev_bb ==>
  ghost_rel sg1 (entry_prov fn t G) (entry_taint_vars fn t tn)
                (entry_prov fn' t' G') (entry_taint_vars fn' t' tn')
Proof
  rw[ghost_rel_def, entry_ghost_block_insts] >>
  irule phis_ghost_rel >> simp[] >> qexists `sg` >> simp[]
QED

(* ===== Labels ===== *)

Theorem foldl_update_var_labels:
  !kvs s. (FOLDL (\s' (k,v). update_var k v s') s kvs).vs_labels = s.vs_labels
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[update_var_def]
QED

Theorem bind_outputs_labels:
  bind_outputs outs vals s = SOME s' ==> s'.vs_labels = s.vs_labels
Proof
  rw[bind_outputs_def] >> simp[foldl_update_var_labels]
QED

Theorem enters_block_labels:
  enters_block fn s s1 ==> s1.vs_labels = s.vs_labels
Proof
  rw[enters_block_def] >> imp_res_tac eval_phis_preserves_labels >> simp[]
QED

Theorem return_state_labels:
  (adopt_return_fmp ret (merge_callee_state c e)).vs_labels = c.vs_labels
Proof
  simp[adopt_return_fmp_def, merge_callee_state_def] >> CASE_TAC >> simp[]
QED

Theorem frame_reachable_labels:
  !vs ctx stk PG G tn fn inst s.
    frame_reachable vs ctx stk PG G tn fn inst s ==>
    s.vs_labels = vs.vs_labels /\
    EVERY (\f. f.cf_state.vs_labels = vs.vs_labels) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> imp_res_tac enters_block_labels >>
  imp_res_tac step_inst_preserves_labels_always >>
  imp_res_tac bind_outputs_labels >>
  gvs[setup_callee_def, return_state_labels, AllCaseEqs()]
QED

(* ===== The ghost transport ===== *)

(* A suspended caller frame of C and one of C', waiting on paired
   INVOKEs. *)
Definition frame_pair_def:
  frame_pair Q L C C' f f' <=>
    f'.cf_params = f.cf_params /\ f'.cf_inst.inst_opcode = INVOKE /\
    ?pos R sg.
      (!l k. pos l (SUC k) = SUC (pos l k)) /\
      lockstep_sim L C C' f.cf_fn f'.cf_fn pos R /\ Q f.cf_fn f'.cf_fn pos /\
      R T (f.cf_inst,f.cf_state) sg (f'.cf_inst,f'.cf_state) /\
      vars_ghost_rel sg f.cf_prov f.cf_tvar f'.cf_prov f'.cf_tvar
End

Theorem lockstep_ctx_lookup:
  lockstep_ctx Q L C C' /\ lookup_function nm C'.ctx_functions = SOME fn' ==>
  ?fn pos R. lookup_function nm C.ctx_functions = SOME fn /\
    fn'.fn_name = fn.fn_name /\ fn_entry_label fn' = fn_entry_label fn /\
    (!l k. pos l (SUC k) = SUC (pos l k)) /\
    lockstep_sim L C C' fn fn' pos R /\ Q fn fn' pos
Proof
  rw[lockstep_ctx_def] >> drule list_rel_lookup_function >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `nm` mp_tac) >>
  Cases_on `lookup_function nm C.ctx_functions` >>
  simp[optionTheory.OPTREL_def, frame_lockstep_def] >> metis_tac[]
QED

(* The n-th clause of lockstep_sim, applied to the assumptions. *)
fun lockstep_clause_tac n =
  strip_tac >>
  qpat_x_assum `lockstep_sim _ _ _ _ _ _ _`
    (fn th => drule_all_then ACCEPT_TAC
       (List.nth (CONJUNCTS (REWRITE_RULE [lockstep_sim_def] th), n)));

Theorem lockstep_rel:
  lockstep_sim L C C' fn fn' pos R /\ R p (inst,s) sg (inst',s') ==>
  active_inst fn inst s /\ active_inst fn' inst' s' /\ state_rel sg s s' /\
  (p ==> inst_pair sg inst inst' /\
         s'.vs_inst_idx = pos s.vs_current_bb s.vs_inst_idx) /\
  (~p ==> inst'.inst_opcode = ASSIGN \/
          (inst'.inst_opcode = NOP /\ inst'.inst_operands = []))
Proof
  lockstep_clause_tac 0
QED

Theorem lockstep_paired:
  lockstep_sim L C C' fn fn' pos R /\ R p (inst,s) sg (inst',s') /\
  inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP ==>
  p /\ inst_pair sg inst inst' /\ state_rel sg s s' /\
  active_inst fn inst s /\ active_inst fn' inst' s'
Proof
  strip_tac >> drule_all lockstep_rel >> Cases_on `p` >> simp[]
QED

Theorem lockstep_entry:
  lockstep_sim L C C' fn fn' pos R /\
  fn_entry_state fn s0 /\ s0.vs_labels = L /\
  enters_block fn' s0 s1' /\ active_inst fn' inst' s1' ==>
  ?p inst s1 sg. enters_block fn s0 s1 /\ R p (inst,s1) sg (inst',s1')
Proof
  lockstep_clause_tac 1
QED

Theorem lockstep_copy:
  lockstep_sim L C C' fn fn' pos R /\
  R F (inst,s) sg (inst',s') /\ step_inst fuel C' inst' s' = OK t' /\
  active_inst fn' j' (t' with vs_inst_idx := SUC s'.vs_inst_idx) ==>
  ?p sg'. R p (inst,s) sg' (j', t' with vs_inst_idx := SUC s'.vs_inst_idx) /\
          copy_rename_ok sg inst' sg'
Proof
  lockstep_clause_tac 2
QED

Theorem lockstep_step:
  lockstep_sim L C C' fn fn' pos R /\
  R T (inst,s) sg (inst',s') /\ inst'.inst_opcode <> INVOKE /\
  step_inst fuel C' inst' s' = OK t' ==>
  ?t. step_inst fuel C inst s = OK t /\
      execution_frame t' = execution_frame t /\
      (~is_terminator inst'.inst_opcode ==>
       !j'. active_inst fn' j' (t' with vs_inst_idx := SUC s'.vs_inst_idx) ==>
         ?p j sg'.
           R p (j, t with vs_inst_idx := SUC s.vs_inst_idx) sg'
             (j', t' with vs_inst_idx := SUC s'.vs_inst_idx) /\
           out_rename_ok sg inst.inst_outputs inst'.inst_outputs sg') /\
      (is_terminator inst'.inst_opcode ==>
       t'.vs_current_bb = t.vs_current_bb /\
       t'.vs_prev_bb = t.vs_prev_bb /\
       !t1' j'. ~t'.vs_halted /\ enters_block fn' t' t1' /\
                active_inst fn' j' t1' ==>
         ?p j t1 sg1. enters_block fn t t1 /\ R p (j,t1) sg1 (j',t1') /\
           phis_rename_ok t.vs_prev_bb sg
             (block_insts fn t.vs_current_bb)
             (block_insts fn' t.vs_current_bb) sg1)
Proof
  lockstep_clause_tac 3
QED

Theorem lockstep_intret:
  lockstep_sim L C C' fn fn' pos R /\
  R T (inst,s) sg (inst',s') /\ inst'.inst_opcode <> INVOKE /\
  step_inst fuel C' inst' s' = IntRet v e' ==>
  ?e. step_inst fuel C inst s = IntRet v e /\
      execution_frame e' = execution_frame e
Proof
  lockstep_clause_tac 4
QED

Theorem lockstep_halt:
  lockstep_sim L C C' fn fn' pos R /\
  R T (inst,s) sg (inst',s') /\ inst'.inst_opcode <> INVOKE /\
  step_inst fuel C' inst' s' = Halt h' ==>
  ?h. step_inst fuel C inst s = Halt h /\
      execution_frame h' = execution_frame h
Proof
  lockstep_clause_tac 5
QED

Theorem lockstep_resume:
  lockstep_sim L C C' fn fn' pos R /\
  R T (inst,s) sg (inst',s') /\ inst'.inst_opcode = INVOKE /\
  execution_frame e' = execution_frame e /\
  bind_outputs inst'.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s' e')) = SOME t' /\
  active_inst fn' j' (t' with vs_inst_idx := SUC s'.vs_inst_idx) ==>
  ?p j t sg'.
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s e)) = SOME t /\
    R p (j, t with vs_inst_idx := SUC s.vs_inst_idx) sg'
      (j', t' with vs_inst_idx := SUC s'.vs_inst_idx) /\
    out_rename_ok sg inst.inst_outputs inst'.inst_outputs sg'
Proof
  lockstep_clause_tac 6
QED

Theorem frame_pair_resume:
  frame_pair Q L C C' f f' /\ execution_frame e' = execution_frame e /\
  bind_outputs f'.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f'.cf_state e')) = SOME t' /\
  active_inst f'.cf_fn j' (t' with vs_inst_idx := SUC f'.cf_state.vs_inst_idx) ==>
  ?posF RF sgF pF jF tF sgF'.
    (!l k. posF l (SUC k) = SUC (posF l k)) /\
    lockstep_sim L C C' f.cf_fn f'.cf_fn posF RF /\ Q f.cf_fn f'.cf_fn posF /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state e)) = SOME tF /\
    RF pF (jF, tF with vs_inst_idx := SUC f.cf_state.vs_inst_idx) sgF'
       (j', t' with vs_inst_idx := SUC f'.cf_state.vs_inst_idx) /\
    out_rename_ok sgF f.cf_inst.inst_outputs f'.cf_inst.inst_outputs sgF' /\
    vars_ghost_rel sgF f.cf_prov f.cf_tvar f'.cf_prov f'.cf_tvar /\
    active_inst f.cf_fn jF (tF with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
    f'.cf_params = f.cf_params
Proof
  rewrite_tac[frame_pair_def] >> strip_tac >>
  drule_all lockstep_resume >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  qexistsl [`pos`, `R`, `sg`] >> simp[] >> metis_tac[]
QED

Theorem frame_reachable_lockstep:
  !vs C' stk' PG G' tn' fn' inst' s'.
    frame_reachable vs C' stk' PG G' tn' fn' inst' s' ==>
    !Q C. lockstep_ctx Q vs.vs_labels C C' /\ vs.vs_vars = FEMPTY /\
          ~vs.vs_halted ==>
      ?stk G tn fn inst s p sg pos R.
        frame_reachable vs C stk PG G tn fn inst s /\
        (!l k. pos l (SUC k) = SUC (pos l k)) /\
        lockstep_sim vs.vs_labels C C' fn fn' pos R /\ Q fn fn' pos /\
        R p (inst,s) sg (inst',s') /\ ghost_rel sg G tn G' tn' /\
        LIST_REL (frame_pair Q vs.vs_labels C C') stk stk'
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_reachable_lockstep[entry]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all lockstep_ctx_lookup >> strip_tac >>
  `C.ctx_entry = SOME name` by fs[lockstep_ctx_def] >>
  qmatch_asmsub_abbrev_tac `enters_block _ s0 _` >>
  `fn_entry_state fn s0` by
    (simp[Abbr `s0`] >> irule context_fn_entry_state >> gvs[]) >>
  `s0.vs_labels = vs.vs_labels` by simp[Abbr `s0`] >>
  drule_all lockstep_entry >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  rename1 `R p (instS,s1S) sg _` >>
  qexistsl [`[]`, `FEMPTY`, `entry_taint`, `fn`, `instS`, `s1S`, `p`, `sg`,
            `pos`, `R`] >>
  simp[ghost_rel_def, vars_ghost_rel_def] >>
  reverse conj_tac >- simp[entry_taint_def, var_taint_def] >>
  irule frame_reachable_entry >> gvs[Abbr `s0`]
QED

Resume frame_reachable_lockstep[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  Cases_on `p`
  >- (gvs[] >>
      drule_all lockstep_step >> strip_tac >>
      `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
        fs[inst_pair_def] >>
      gvs[] >>
      qpat_x_assum `!j'. active_inst fn' j' _ ==> _` drule >> strip_tac >>
      imp_res_tac lockstep_rel >>
      rename1 `R p2 (j,_) sg2 (inst'',_)` >>
      qexistsl [`stk`, `step_prov PG G inst t`, `step_taint inst s t tn`,
                `fn`, `j`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `p2`,
                `sg2`, `pos`, `R`] >>
      simp[] >> conj_tac
      >- (irule frame_reachable_next >> simp[] >> metis_tac[]) >>
      irule step_ghost_pair >> gvs[state_rel_def] >> qexists `sg` >> gvs[]) >>
  fs[] >>
  drule_all lockstep_copy >> strip_tac >>
  rename1 `R pc (inst,s) sgc (inst'',_)` >>
  qexistsl [`stk`, `G`, `tn`, `fn`, `inst`, `s`, `pc`, `sgc`, `pos`, `R`] >>
  simp[] >> irule (cj 2 step_ghost_copy) >> simp[] >> metis_tac[]
QED

Resume frame_reachable_lockstep[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP /\
   inst'.inst_opcode <> INVOKE` by (rpt strip_tac >> gvs[is_terminator_def]) >>
  `p` by (Cases_on `p` >> gvs[]) >>
  gvs[] >>
  `inst.inst_opcode = inst'.inst_opcode` by fs[inst_pair_def] >>
  drule_all lockstep_step >> strip_tac >> gvs[] >>
  qpat_x_assum `!t1' j'. _` drule_all >> strip_tac >>
  imp_res_tac lockstep_rel >>
  rename1 `enters_block fn t t1N` >>
  rename1 `R pN (jN,t1N) sgN _` >>
  `~t.vs_halted` by metis_tac[execution_frame_fields] >>
  qexistsl [`stk`, `entry_prov fn t G`, `entry_taint_vars fn t tn`, `fn`,
            `jN`, `t1N`, `pN`, `sgN`, `pos`, `R`] >>
  simp[] >> conj_tac
  >- (irule frame_reachable_block >> simp[] >> metis_tac[]) >>
  irule entry_ghost_rel >> simp[] >> qexists `sg` >> simp[]
QED

Resume frame_reachable_lockstep[call]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP` by simp[] >>
  drule_all lockstep_paired >> strip_tac >> fs[] >>
  `?ops0. inst.inst_operands = Label nm :: ops0 /\
          LIST_REL (op_rename sg) ops0 ops` by
    (gvs[inst_pair_def, decode_invoke_def, AllCaseEqs(), LIST_REL_CONS2,
         op_rename_label] >> metis_tac[]) >>
  `decode_invoke inst = SOME (nm, ops0) /\ inst.inst_opcode = INVOKE` by
    fs[decode_invoke_def, inst_pair_def] >>
  `vars_ghost_rel sg G tn.t_var G' tn'.t_var` by fs[ghost_rel_def] >>
  `MAP (op_prov G') ops = MAP (op_prov G) ops0` by
    metis_tac[map_op_prov_rename] >>
  `execution_frame s' = execution_frame s /\ vars_rel sg s s'` by
    fs[state_rel_def] >>
  `s'.vs_labels = s.vs_labels` by metis_tac[execution_frame_fields] >>
  `LIST_REL (\op op'. op_rename sg op op' /\
                      eval_operand op' s' = eval_operand op s) ops0 ops` by
    (irule LIST_REL_op_rename_eval >> fs[]) >>
  drule eval_operands_rel >> strip_tac >>
  `eval_operands ops0 s = SOME args` by gvs[] >>
  drule_all lockstep_ctx_lookup >> strip_tac >>
  rename1 `lookup_function nm C.ctx_functions = SOME calleeS` >>
  `setup_callee calleeS args s = SOME cs` by
    metis_tac[setup_callee_execution_frame] >>
  `fn_entry_state calleeS cs` by metis_tac[setup_callee_fn_entry_state] >>
  `cs.vs_labels = vs.vs_labels` by
    (imp_res_tac frame_reachable_labels >>
     qpat_x_assum `setup_callee calleeS _ _ = _` mp_tac >>
     rw[setup_callee_def] >> simp[]) >>
  drule_at (Pos (el 2)) lockstep_entry >> disch_then drule_all >> strip_tac >>
  rename1 `enters_block calleeS cs s1c` >>
  rename1 `R' pc (instc,s1c) sgc _` >>
  imp_res_tac lockstep_rel >>
  `frame_reachable vs C
     (<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
        cf_prov := G; cf_tvar := tn.t_var|> :: stk)
     (MAP (op_prov G) ops0) FEMPTY (tn with t_var := FEMPTY) calleeS instc s1c` by
    (irule frame_reachable_call >> simp[] >> metis_tac[]) >>
  `frame_pair Q vs.vs_labels C C'
     <|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
       cf_prov := G; cf_tvar := tn.t_var|>
     <|cf_fn := fn'; cf_inst := inst'; cf_state := s'; cf_params := PG;
       cf_prov := G'; cf_tvar := tn'.t_var|>` by
    (simp[frame_pair_def] >> qexistsl [`pos`, `R`, `sg`] >> simp[]) >>
  qexistsl [`<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
               cf_prov := G; cf_tvar := tn.t_var|> :: stk`,
            `FEMPTY`, `tn with t_var := FEMPTY`, `calleeS`, `instc`, `s1c`,
            `pc`, `sgc`, `pos'`, `R'`] >>
  fs[ghost_rel_def, vars_ghost_rel_def, var_taint_def]
QED

Resume frame_reachable_lockstep[ret]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `step_inst fuel C' ri' sc' = IntRet ret e'` >>
  rename1 `bind_outputs fr'.cf_inst.inst_outputs ret.iret_values _ = SOME tq'` >>
  rename1 `active_inst fr'.cf_fn jq' _` >>
  rename1 `R p (ri,sc) sg (ri',sc')` >>
  fs[LIST_REL_CONS2] >>
  rename1 `frame_pair Q _ C C' fr fr'` >>
  rename1 `LIST_REL (frame_pair Q _ C C') stkS stk'` >>
  `ri'.inst_opcode <> ASSIGN /\ ri'.inst_opcode <> NOP /\
   ri'.inst_opcode <> INVOKE` by
    (rpt strip_tac >>
     metis_tac[step_inst_copy_not_intret, step_inst_invoke_not_intret]) >>
  drule_all lockstep_paired >> strip_tac >> fs[] >>
  drule_all lockstep_intret >> strip_tac >>
  drule_all frame_pair_resume >> strip_tac >>
  `frame_reachable vs C stkS fr.cf_params
     (DRESTRICT fr.cf_prov (COMPL (set fr.cf_inst.inst_outputs)))
     (tn with t_var := DRESTRICT fr.cf_tvar (COMPL (set fr.cf_inst.inst_outputs)))
     fr.cf_fn jF (tF with vs_inst_idx := SUC fr.cf_state.vs_inst_idx)` by
    (irule frame_reachable_ret >> simp[] >> metis_tac[]) >>
  qexistsl [`stkS`,
            `DRESTRICT fr.cf_prov (COMPL (set fr.cf_inst.inst_outputs))`,
            `tn with t_var :=
               DRESTRICT fr.cf_tvar (COMPL (set fr.cf_inst.inst_outputs))`,
            `fr.cf_fn`, `jF`,
            `tF with vs_inst_idx := SUC fr.cf_state.vs_inst_idx`, `pF`,
            `sgF'`, `posF`, `RF`] >>
  fs[ghost_rel_def] >> irule ret_ghost_rel >> qexists `sgF` >> simp[]
QED

Finalise frame_reachable_lockstep

(* ===== The taint bound ===== *)

Theorem lockstep_req_step:
  frame_reachable vs C' stk' PG G' tn' fn' inst' s' /\
  inst'.inst_opcode <> INVOKE /\ step_inst fuel C' inst' s' = OK t' /\
  LENGTH s'.vs_requests < LENGTH t'.vs_requests /\
  lockstep_ctx Q vs.vs_labels C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  ?stk G tn fn inst s t.
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK t /\
    LENGTH s.vs_requests < LENGTH t.vs_requests /\
    execution_frame s' = execution_frame s /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans
Proof
  strip_tac >> drule_all frame_reachable_lockstep >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  Cases_on `p` >> fs[]
  >- (drule_all lockstep_step >> strip_tac >>
      `inst.inst_opcode <> INVOKE` by fs[inst_pair_def] >>
      fs[state_rel_def, ghost_rel_def] >>
      imp_res_tac execution_frame_fields >>
      qexistsl [`stk`, `G`, `tn`, `fn`, `inst`, `s`, `t`] >> gvs[]) >>
  drule_at (Pos last) step_inst_copy >> (impl_tac >- fs[]) >> strip_tac >>
  gvs[update_var_def]
QED

Theorem lockstep_final:
  frame_reachable vs C' stk' PG G' T0' fn' inst' s' /\
  inst'.inst_opcode <> INVOKE /\ step_inst fuel C' inst' s' = Halt h' /\
  lockstep_ctx Q vs.vs_labels C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  ?h tn R.
    final_taint vs C h tn R /\ execution_frame h' = execution_frame h /\
    (step_taint inst' s' h' T0').t_stor = tn.t_stor /\
    (step_taint inst' s' h' T0').t_trans = tn.t_trans /\
    (step_taint inst' s' h' T0').t_imm = tn.t_imm /\
    ret_taint T0' inst' s' = R
Proof
  strip_tac >> drule_all frame_reachable_lockstep >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP` by
    (rpt strip_tac >> metis_tac[step_inst_copy_not_intret]) >>
  drule_all lockstep_paired >> strip_tac >> fs[] >>
  drule_all lockstep_halt >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[inst_pair_def] >>
  `ghost_rel FEMPTY (step_prov PG G inst h) (step_taint inst s h tn)
     (step_prov PG G' inst' h') (step_taint inst' s' h' T0')` by
    (irule step_ghost_pair >> simp[vars_rel_def, out_rename_ok_def] >>
     reverse conj_tac >- (qexists `sg` >> simp[]) >> fs[]) >>
  `ret_taint T0' inst' s' = ret_taint tn inst s` by
    metis_tac[ret_taint_pair] >>
  qexistsl [`h`, `step_taint inst s h tn`] >>
  fs[ghost_rel_def] >> simp[final_taint_def] >>
  qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `fuel`] >> simp[]
QED

Theorem taint_within_lockstep:
  lockstep_ctx Q vs.vs_labels C C' /\ vs.vs_vars = FEMPTY /\
  ~vs.vs_halted /\ taint_within D C vs ==>
  taint_within D C' vs
Proof
  rewrite_tac[taint_within_def] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all lockstep_req_step >>
      strip_tac >> first_x_assum drule_all >>
      imp_res_tac execution_frame_fields >> simp[]) >>
  rpt gen_tac >> simp[Once final_taint_def] >> strip_tac >>
  drule_all lockstep_final >> strip_tac >>
  first_x_assum drule >> imp_res_tac execution_frame_fields >> gvs[]
QED

(* Paired states touch the same memory. *)
Theorem lockstep_paired_mem_ranges:
  lockstep_sim L C C' fn fn' pos R /\ R T (inst,s) sg (inst',s') ==>
  inst_mem_ranges inst' s' = inst_mem_ranges inst s
Proof
  strip_tac >> drule_all lockstep_rel >> strip_tac >> fs[] >>
  metis_tac[inst_mem_ranges_pair]
QED

(* ===== Single-frame runs ===== *)

(* A paired INVOKE: the callees, related by ctx_bisim, return related
   results, so the caller resumes in lockstep. *)
Theorem lockstep_invoke:
  ctx_bisim C C' /\ lockstep_sim L C C' fn fn' pos R /\
  R T (inst,s) sg (inst',s') /\ inst'.inst_opcode = INVOKE /\
  step_inst fuel C' inst' s' = OK t' /\
  active_inst fn' j' (t' with vs_inst_idx := SUC s'.vs_inst_idx) ==>
  ?fuel0 t p j sg'.
    step_inst fuel0 C inst s = OK t /\
    R p (j, t with vs_inst_idx := SUC s.vs_inst_idx) sg'
      (j', t' with vs_inst_idx := SUC s'.vs_inst_idx)
Proof
  strip_tac >> drule_all lockstep_rel >> simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ C' _ _ = OK _` mp_tac >>
  simp[Once step_inst_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = (_,_)` SUBST_ALL_TAC >>
  rename1 `decode_invoke inst' = SOME (nm, ops')` >>
  rename1 `lookup_function nm C'.ctx_functions = SOME callee'` >>
  rename1 `setup_callee callee' args s' = SOME cs` >>
  rename1 `run_blocks fuel C' callee' cs = IntRet ret e'` >>
  `?ops. inst.inst_operands = Label nm :: ops /\
         LIST_REL (op_rename sg) ops ops'` by
    (gvs[inst_pair_def, decode_invoke_def, AllCaseEqs(), LIST_REL_CONS2,
         op_rename_label] >> metis_tac[]) >>
  `decode_invoke inst = SOME (nm, ops) /\ inst.inst_opcode = INVOKE` by
    fs[decode_invoke_def, inst_pair_def] >>
  `execution_frame s' = execution_frame s /\ vars_rel sg s s'` by
    fs[state_rel_def] >>
  `s'.vs_labels = s.vs_labels` by metis_tac[execution_frame_fields] >>
  `LIST_REL (\op op'. op_rename sg op op' /\
                      eval_operand op' s' = eval_operand op s) ops ops'` by
    (irule LIST_REL_op_rename_eval >> fs[]) >>
  drule eval_operands_rel >> strip_tac >>
  `eval_operands ops s = SOME args` by gvs[] >>
  `?calleeS. lookup_function nm C.ctx_functions = SOME calleeS` by
    (Cases_on `lookup_function nm C.ctx_functions` >> simp[] >>
     `ctx_fn_names C' = ctx_fn_names C` by fs[ctx_bisim_def] >>
     imp_res_tac lookup_function_not_mem >>
     imp_res_tac lookup_function_mem >>
     metis_tac[ctx_fn_names_def]) >>
  qpat_x_assum `ctx_bisim _ _` mp_tac >> rewrite_tac[ctx_bisim_def] >>
  strip_tac >>
  first_x_assum (qspecl_then [`nm`, `calleeS`] mp_tac) >> asm_rewrite_tac[] >>
  disch_then (qx_choose_then `fnB` strip_assume_tac) >>
  `fnB = callee'` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >>
  `setup_callee calleeS args s = SOME cs` by
    metis_tac[setup_callee_execution_frame] >>
  `fn_entry_state calleeS cs` by metis_tac[setup_callee_fn_entry_state] >>
  first_x_assum (qspec_then `cs` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  first_x_assum (qspec_then `fuel` mp_tac) >>
  impl_tac >- simp[passSimulationDefsTheory.terminates_def] >>
  disch_then (qx_choose_then `fuel0` mp_tac) >>
  qpat_x_assum `run_blocks fuel C' callee' cs = _` SUBST1_TAC >>
  Cases_on `run_blocks fuel0 C calleeS cs` >>
  simp_tac pure_ss [frame_result_rel_def, pairTheory.pair_case_def,
                    exec_result_case_def] >>
  strip_tac >>
  qpat_x_assum `ret = _` (SUBST_ALL_TAC o SYM) >>
  rename1 `run_blocks fuel0 C calleeS cs = IntRet ret e` >>
  drule_all lockstep_resume >> strip_tac >>
  qexistsl [`fuel0`, `t`] >> simp[Once step_inst_def] >> metis_tac[]
QED

Theorem frame_reach_lockstep_rel:
  !C' fn' s0 inst' s'.
    frame_reach C' fn' s0 inst' s' ==>
    !L C fn pos R.
      ctx_bisim C C' /\
      lockstep_sim L C C' fn fn' pos R /\
      fn_entry_state fn s0 /\ s0.vs_labels = L ==>
      ?p inst s sg. frame_reach C fn s0 inst s /\ R p (inst,s) sg (inst',s')
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac
  >- suspend "start"
  >- suspend "next"
  >> suspend "block"
QED

Resume frame_reach_lockstep_rel[start]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all lockstep_entry >> strip_tac >>
  imp_res_tac lockstep_rel >> metis_tac[frame_reach_rules]
QED

Resume frame_reach_lockstep_rel[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `R p (instS,sS) sg _` >>
  drule_all lockstep_rel >> strip_tac >>
  Cases_on `p` >> RULE_ASSUM_TAC (REWRITE_RULE []) >>
  rpt (qpat_x_assum `_ /\ _` strip_assume_tac)
  >- (Cases_on `inst'.inst_opcode = INVOKE`
      >- (drule_all lockstep_invoke >> strip_tac >>
          `~is_terminator instS.inst_opcode` by fs[inst_pair_def] >>
          imp_res_tac lockstep_rel >> metis_tac[frame_reach_rules]) >>
      drule_all lockstep_step >> strip_tac >>
      `~is_terminator instS.inst_opcode` by fs[inst_pair_def] >>
      gvs[] >>
      qpat_x_assum `!j'. active_inst _ j' _ ==> _` drule >> strip_tac >>
      imp_res_tac lockstep_rel >> metis_tac[frame_reach_rules]) >>
  drule_all lockstep_copy >> strip_tac >> metis_tac[]
QED

Resume frame_reach_lockstep_rel[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `R p (instS,sS) sg _` >>
  drule_all lockstep_rel >> strip_tac >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP /\
   inst'.inst_opcode <> INVOKE` by (rpt strip_tac >> gvs[is_terminator_def]) >>
  `p` by (Cases_on `p` >> gvs[]) >>
  gvs[] >>
  `is_terminator instS.inst_opcode` by fs[inst_pair_def] >>
  drule_all lockstep_step >> strip_tac >> gvs[] >>
  qpat_x_assum `!t1' j'. _` drule_all >> strip_tac >>
  imp_res_tac lockstep_rel >>
  `~t.vs_halted` by metis_tac[execution_frame_fields] >>
  metis_tac[frame_reach_rules]
QED

Finalise frame_reach_lockstep_rel

(* A target state other than an inserted copy runs the same instruction
   as a source state, on equal operand values and an equal frame. *)
Theorem frame_reach_lockstep:
  frame_reach C' fn' s0 inst' s' /\ ctx_bisim C C' /\
  lockstep_sim L C C' fn fn' pos R /\
  fn_entry_state fn s0 /\ s0.vs_labels = L /\
  inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP ==>
  ?inst s. frame_reach C fn s0 inst s /\
           inst.inst_opcode = inst'.inst_opcode /\
           execution_frame s' = execution_frame s /\
           LIST_REL (\op op'. eval_operand op' s' = eval_operand op s)
             inst.inst_operands inst'.inst_operands
Proof
  strip_tac >> drule frame_reach_lockstep_rel >>
  disch_then drule_all >> strip_tac >>
  drule_all lockstep_paired >> strip_tac >>
  drule_all inst_pair_ops >> strip_tac >>
  qexistsl [`inst`, `s`] >> fs[inst_pair_def, state_rel_def, ops_pair_def] >>
  irule LIST_REL_mono >> first_assum (irule_at Any) >> simp[]
QED
