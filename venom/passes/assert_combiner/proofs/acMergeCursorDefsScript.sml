(* Static prefix processing and the one-emission interface.  No predicate in
   the static interface refers to executions or to an unprocessed suffix. *)
Theory acMergeCursorDefs
Ancestors
  acMergeSimulationProofs acRuntimeInvariantDefs acSupplyProofs
  assertCombinerDefs irSupply venomInst venomState list rich_list
  finite_map pred_set

Inductive ac_merge_prefix_reachable:
  (!xs cs su0. ac_merge_prefix_reachable xs cs su0 0 [] su0) /\
  (!xs cs su0 n mp su mp' out su'.
    ac_merge_prefix_reachable xs cs su0 n mp su /\ n < LENGTH xs /\
    ac_merge_inst cs mp su (EL n xs) = (mp',out,su') ==>
    ac_merge_prefix_reachable xs cs su0 (SUC n) mp' su')
End

Definition ac_merge_crossing_def:
  ac_merge_crossing xs n mc <=>
    ?i j. i < n /\ n <= j /\ j < LENGTH xs /\
          (EL i xs).inst_id = mc.mc_first_id /\
          (EL j xs).inst_id = mc.mc_second_id
End

Definition ac_merge_resolve_def:
  ac_merge_resolve mp mc =
    case ALOOKUP mp mc.mc_first_id of
      NONE => mc.mc_first_pred | SOME p => p
End

Definition ac_merge_pending_def:
  ac_merge_pending xs cs n mp su =
    case FIND (ac_merge_crossing xs n) cs of
      NONE => NONE
    | SOME mc => SOME (mc.mc_first_id, ac_merge_resolve mp mc)
End

Definition ac_merge_static_def:
  ac_merge_static xs cs su0 su_end n mp su <=>
    ac_merge_prefix_reachable xs cs su0 n mp su /\
    ir_supply_extends su su_end
End

(* A stored operand is either generated, or is justified by a previously
   encountered query.  Only this selected operand needs to survive a step. *)
Definition ac_merge_operand_origin_def:
  ac_merge_operand_origin xs dfg X n p <=>
    (?v. p = Var v /\ v IN X) \/
    (?a c. a < n /\ a < LENGTH xs /\
      (EL a xs).inst_opcode = ASSERT /\
      (EL a xs).inst_operands = [c] /\
      ac_get_iszero_operand dfg {} c = SOME p)
End

(* These are the four observable forms of one emission.  The bool 'more'
   records an outgoing edge; equal predicates do not allocate any names. *)
Definition ac_merge_emission_form_def:
  ac_merge_emission_form dfg X inst pin pout out <=>
    (out = [inst] /\ pout = pin /\
      (pin <> NONE ==> ac_is_safe_between inst)) \/
    (?c q. inst.inst_opcode = ASSERT /\ inst.inst_operands = [c] /\
      ac_get_iszero_operand dfg {} c = SOME q /\ pin = NONE /\
      pout = SOME (inst.inst_id,q) /\
      out = [inst with <|inst_opcode := NOP; inst_operands := [];
                         inst_outputs := []|>]) \/
    (?j p c q more.
      inst.inst_opcode = ASSERT /\ inst.inst_operands = [c] /\
      ac_get_iszero_operand dfg {} c = SOME q /\ pin = SOME (j,p) /\
      p = q /\
      pout = (if more then SOME (inst.inst_id,p) else NONE) /\
      out = [if more then
        inst with <|inst_opcode := NOP; inst_operands := []; inst_outputs := []|>
        else inst]) \/
    (?j p c q more oi ov zi zv.
      inst.inst_opcode = ASSERT /\ inst.inst_operands = [c] /\
      ac_get_iszero_operand dfg {} c = SOME q /\ pin = SOME (j,p) /\
      p <> q /\ ov IN X /\ zv IN X /\ ov <> zv /\
      pout = (if more then SOME (inst.inst_id,Var ov) else NONE) /\
      out = [instruction oi OR [p;q] [ov];
             instruction zi ISZERO [Var ov] [zv];
             if more then
               inst with <|inst_opcode := NOP; inst_operands := [];
                            inst_outputs := []|>
             else inst with inst_operands := [Var zv]])
End

(* Static laws for independent live/deferred consumers.  FIND agreement and
   unique crossings are exposed separately from the finite emission form. *)
Definition ac_merge_cursor_laws_def:
  ac_merge_cursor_laws xs dfg cs X su0 S pending <=>
    S 0 [] su0 /\ pending 0 [] su0 = NONE /\
    (!n mp su. S n mp su ==>
      n <= LENGTH xs /\ ir_supply_extends su0 su /\
      (!v. MEM v su.irs_used_vars ==> MEM v su0.irs_used_vars \/ v IN X) /\
      (!j p. pending n mp su = SOME (j,p) ==>
        ac_merge_operand_origin xs dfg X n p) /\
      (n = LENGTH xs ==> pending n mp su = NONE)) /\
    (!n mc mc'. MEM mc cs /\ MEM mc' cs /\
      ac_merge_crossing xs n mc /\ ac_merge_crossing xs n mc' ==> mc = mc') /\
    (!n mc. MEM mc cs /\ ac_merge_crossing xs n mc /\
      (EL n xs).inst_id = mc.mc_second_id /\ n < LENGTH xs ==>
      FIND (\c. c.mc_second_id = (EL n xs).inst_id) cs = SOME mc) /\
    (!n mp su mp' out su'. n < LENGTH xs /\ S n mp su /\
      ac_merge_inst cs mp su (EL n xs) = (mp',out,su') ==>
      S (SUC n) mp' su' /\ ir_supply_extends su su' /\
      ac_merge_emission_form dfg X (EL n xs)
        (pending n mp su) (pending (SUC n) mp' su') out) /\
    (!i v. MEM i xs /\ (MEM (Var v) i.inst_operands \/ MEM v i.inst_outputs)
      ==> v NOTIN X)
End

(* Raw list execution leaves internal indices unchanged.  Normalize only the
   certificate; the raw source/target states remain related by state_equiv. *)
Definition ac_merge_runtime_def:
  ac_merge_runtime fn bb offset n s <=>
    ac_cursor_inv fn bb (offset+n)
      (s with <|vs_current_bb := bb.bb_label; vs_inst_idx := offset+n|>)
End

Definition ac_merge_revert_deferred_def:
  ac_merge_revert_deferred X K S pending n mp su a sa g t <=>
    ac_merge_deferred X K S pending n mp su a sa g t /\ a = Revert_abort
End

Theorem ac_merge_prefix_zero:
  ac_merge_prefix_reachable xs cs su0 0 [] su0
Proof
  simp[ac_merge_prefix_reachable_rules]
QED

Theorem ac_merge_prefix_step:
  ac_merge_prefix_reachable xs cs su0 n mp su /\ n < LENGTH xs /\
  ac_merge_inst cs mp su (EL n xs) = (mp',out,su') ==>
  ac_merge_prefix_reachable xs cs su0 (SUC n) mp' su'
Proof
  metis_tac[ac_merge_prefix_reachable_rules]
QED

Theorem ac_merge_crossing_zero:
  ~ac_merge_crossing xs 0 mc
Proof
  simp[ac_merge_crossing_def]
QED

Theorem ac_merge_crossing_end:
  LENGTH xs <= n ==> ~ac_merge_crossing xs n mc
Proof
  simp[ac_merge_crossing_def] >> decide_tac
QED

Theorem ac_merge_pending_zero:
  ac_merge_pending xs cs 0 mp su = NONE
Proof
  simp[ac_merge_pending_def] >>
  `FIND (ac_merge_crossing xs 0) cs = NONE` suffices_by simp[] >>
  Induct_on `cs` >> simp[FIND_thm, ac_merge_crossing_zero]
QED

Theorem ac_merge_pending_end:
  LENGTH xs <= n ==> ac_merge_pending xs cs n mp su = NONE
Proof
  strip_tac >> simp[ac_merge_pending_def] >>
  `FIND (ac_merge_crossing xs n) cs = NONE` suffices_by simp[] >>
  Induct_on `cs` >> simp[FIND_thm, ac_merge_crossing_end]
QED

(* A->B->C: the crossing edge switches at B; C's original scanner pending
   value is irrelevant once it has no outgoing edge.  mp may contain arbitrary
   bindings, so this also probes selection through the actual accumulator. *)
Theorem ac_merge_pending_chain_probe:
  a.inst_id = 0 /\ b.inst_id = 1 /\ c.inst_id = 2 /\
  ab.mc_first_id = 0 /\ ab.mc_second_id = 1 /\
  bc.mc_first_id = 1 /\ bc.mc_second_id = 2 ==>
  ac_merge_pending [a;b;c] [ab;bc] 1 mp su =
    SOME (0,ac_merge_resolve mp ab) /\
  ac_merge_pending [a;b;c] [ab;bc] 2 mp su =
    SOME (1,ac_merge_resolve mp bc) /\
  ac_merge_pending [a;b;c] [ab;bc] 3 mp su = NONE
Proof
  strip_tac >>
  `!i:num. i < 1 <=> i = 0` by decide_tac >>
  `!i:num. i < 2 <=> i = 0 \/ i = 1` by decide_tac >>
  `!i:num. i < 3 <=> i = 0 \/ i = 1 \/ i = 2` by decide_tac >>
  simp[ac_merge_pending_def, FIND_thm, ac_merge_crossing_def,
       SF DNF_ss]
QED

(* The additional reason constraint is deliberately explicit: the old generic
   deferred relation alone cannot identify the Abort constructor's reason. *)
Theorem ac_merge_revert_deferred_reason:
  ac_merge_revert_deferred X cert shape pending n mp su a sa g t ==>
  a = Revert_abort /\ ac_merge_deferred X cert shape pending n mp su a sa g t
Proof
  simp[ac_merge_revert_deferred_def]
QED

Theorem ac_merge_runtime_entry:
  ac_cursor_inv fn bb 0 s ==>
  ac_merge_runtime fn bb 0 0 s
Proof
  `!op. eval_operand op (s with vs_current_bb := bb.bb_label) =
        eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[ac_merge_runtime_def, ac_cursor_inv_def,
       acChainProofsTheory.ac_dfg_inv_local_def, lookup_var_def] >>
  metis_tac[]
QED
