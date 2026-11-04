(* Bounded ghost replay, independent of concrete target execution success.
   An origin is (visit, source instruction id, output ordinal). *)
Theory makeSsaCurrentTemporalProbe
Ancestors makeSsaCurrentHistoryProbe alist

Definition temporal_lookup_def:
  temporal_lookup m v = ALOOKUP m v
End

Definition temporal_writes_def:
  temporal_writes (visit:num) (site:num) (phase:num) outs m =
    ZIP (outs, GENLIST (\k. ((visit,site,k),phase)) (LENGTH outs)) ++ m
End

Definition temporal_operands_def:
  (temporal_operands s t [] [] = T) /\
  (temporal_operands s t (Var v::xs) (Var w::ys) =
    (IS_SOME (temporal_lookup s v) /\
     OPTION_MAP FST (temporal_lookup s v) =
       OPTION_MAP FST (temporal_lookup t w) /\
     temporal_operands s t xs ys)) /\
  (temporal_operands s t (x::xs) (y::ys) =
    (x = y /\ temporal_operands s t xs ys)) /\
  (temporal_operands s t xs ys = F)
End

Definition temporal_pick_def:
  (temporal_pick p [] = NONE) /\
  (temporal_pick p (Label l::Var v::xs) =
    if p = l then SOME v else temporal_pick p xs) /\
  (temporal_pick p xs = NONE)
End

Definition temporal_copy_def:
  temporal_copy (phase:num) from outs incoming m =
    case temporal_lookup incoming from of
      NONE => (F,m)
    | SOME (origin,last) =>
        (T, MAP (\v. (v,(origin,phase))) outs ++ m)
End

(* Source PHIs write simultaneous fresh origins, not copies of operand origins. *)
Definition temporal_source_phis_def:
  (temporal_source_phis visit [] m = m) /\
  (temporal_source_phis visit (i::xs) m =
    temporal_source_phis visit xs
      (temporal_writes visit i.inst_id 0 i.inst_outputs m))
End

(* Inserted retained PHIs read the incoming snapshot. Original retained PHIs
   create the matching source-write origin after checking selected operands. *)
Definition temporal_target_phis_def:
  (temporal_target_phis visit p (n:num) originals sin tin [] m = ([],m)) /\
  (temporal_target_phis visit p (n:num) originals sin tin (i::xs) m =
    if n > 0 then
      case temporal_pick p i.inst_operands of
        NONE => (F::FST (temporal_target_phis visit p (n-1) originals sin tin xs m),m)
      | SOME v =>
          let r = temporal_copy 0 v i.inst_outputs tin m in
          let rest = temporal_target_phis visit p (n-1) originals sin tin xs (SND r) in
          (FST r::FST rest,SND rest)
    else case originals of
      [] => ([F],m)
    | j::js =>
        let good = case (temporal_pick p j.inst_operands,
                         temporal_pick p i.inst_operands) of
           (SOME v,SOME w) => temporal_operands sin tin [Var v] [Var w]
         | _ => F in
        let rest = temporal_target_phis visit p 0 js sin tin xs
          (temporal_writes visit j.inst_id 0 i.inst_outputs m) in
        (good::FST rest,SND rest))
End

Definition temporal_cleanup_def:
  (temporal_cleanup k [] m = ([],m)) /\
  (temporal_cleanup k (i::xs) m =
    let r = if i.inst_opcode = NOP then (T,m)
      else case i.inst_operands of
        [Var v] => temporal_copy k v i.inst_outputs m m
      | _ => (F,m) in
    let rest = temporal_cleanup (k+1) xs (SND r) in
    (FST r::FST rest,SND rest))
End

Definition temporal_ordinary_def:
  (temporal_ordinary visit k [] [] s t = ([],s,t)) /\
  (temporal_ordinary visit k (i::xs) (j::ys) s t =
    let good = (i.inst_opcode = j.inst_opcode /\
      temporal_operands s t i.inst_operands j.inst_operands) in
    let rest = temporal_ordinary visit (k+1) xs ys
      (temporal_writes visit i.inst_id k i.inst_outputs s)
      (temporal_writes visit i.inst_id k j.inst_outputs t) in
    (good::FST rest,FST (SND rest),SND (SND rest))) /\
  (temporal_ordinary visit k xs ys s t = ([F],s,t))
End

Definition temporal_entry_def:
  temporal_entry visit p source target s t =
    let sp = TAKE (phi_prefix_length source) source in
    let so = DROP (LENGTH sp) source in
    let tp = TAKE (phi_prefix_length target) target in
    let suffix = DROP (LENGTH tp) target in
    let copies = LENGTH suffix - LENGTH so in
    let ph = temporal_target_phis visit p (LENGTH tp - LENGTH sp)
      sp s t tp t in
    let cp = temporal_cleanup 1 (TAKE copies suffix) (SND ph) in
    (FST ph ++ FST cp,temporal_source_phis visit sp s,SND cp)
End

Definition temporal_visit_def:
  temporal_visit visit p source target s t =
    let sp = TAKE (phi_prefix_length source) source in
    let so = DROP (LENGTH sp) source in
    let tp = TAKE (phi_prefix_length target) target in
    let suffix = DROP (LENGTH tp) target in
    let copies = LENGTH suffix - LENGTH so in
    let entry = temporal_entry visit p source target s t in
    let ordinary = temporal_ordinary visit (copies+1) so (DROP copies suffix)
      (FST (SND entry)) (SND (SND entry)) in
    (FST entry ++ FST ordinary,
      FST (SND ordinary),SND (SND ordinary))
End

Definition temporal_replay_def:
  (temporal_replay visit p blocks targets [] s t = ([],s,t)) /\
  (temporal_replay visit p blocks targets (l::ls) s t =
    case (lookup_block l blocks,lookup_block l targets) of
      (SOME b,SOME c) =>
        let r = temporal_visit visit p b.bb_instructions c.bb_instructions s t in
        let rest = temporal_replay (visit+1) l blocks targets ls
          (FST (SND r)) (SND (SND r)) in
        (FST r ++ FST rest,FST (SND rest),SND (SND rest))
    | _ => ([F],s,t))
End

Theorem temporal_diamond_probe:
  EVERY I (FST (temporal_replay 0 "" history_probe_diamond.fn_blocks
    history_probe_diamond_target ["E";"L";"H";"H";"H"] [] []))
Proof
  EVAL_TAC
QED

Theorem temporal_backedges_probe:
  EVERY I (FST (temporal_replay 0 "" history_probe_backedges.fn_blocks
    history_probe_backedges_target ["E";"H";"D";"H";"D";"H"] [] []))
Proof
  EVAL_TAC
QED

Theorem temporal_nested_probe:
  EVERY I (FST (temporal_replay 0 "" history_probe_nested.fn_blocks
    history_probe_nested_target ["E";"H";"I";"D";"I";"D";"I"] [] []))
Proof
  EVAL_TAC
QED

(* This checks the ghost dataflow on the outer backedge, not realizability:
   for the literal-valued example I always branches to D, never to J. *)
Theorem temporal_nested_outer_dataflow_probe:
  EVERY I (FST (temporal_replay 0 "" history_probe_nested.fn_blocks
    history_probe_nested_target ["E";"H";"I";"D";"I";"J";"H";"I"] [] []))
Proof
  EVAL_TAC
QED

Theorem temporal_irreducible_probe:
  EVERY I (FST (temporal_replay 0 "" history_probe_irreducible.fn_blocks
    history_probe_irreducible_target ["E";"H";"I";"H";"I";"H"] [] []))
Proof
  EVAL_TAC
QED

Theorem temporal_control_probe:
  EVERY I (FST (temporal_replay 0 "" current_probe_loop.fn_blocks
    history_probe_control_target ["E";"D";"D";"D"] [] []))
Proof
  EVAL_TAC
QED

(* Check every inserted owner, including dead ones, after parallel PHIs and
   cleanup. No arbitrary valuation or successful target run is a premise. *)
Definition temporal_owner_check_def:
  temporal_owner_check l inserted s t = EVERY (\(label,owners,operands,outs,op).
    label <> l \/ temporal_operands s t
      (MAP Var owners) (MAP Var outs)) inserted
End

Definition temporal_insert_summary_def:
  temporal_insert_summary fn = MAP (\(l,owner,i).
    (l,owner,i.inst_operands,i.inst_outputs,
      (simplify_current_phi i).inst_opcode)) (history_probe_inserted fn)
End

Definition temporal_audit_def:
  (temporal_audit visit p blocks targets inserted [] s t = []) /\
  (temporal_audit visit p blocks targets inserted (l::ls) s t =
    case (lookup_block l blocks,lookup_block l targets) of
      (SOME b,SOME c) =>
        let e = temporal_entry visit p b.bb_instructions c.bb_instructions s t in
        let r = temporal_visit visit p b.bb_instructions c.bb_instructions s t in
        temporal_owner_check l inserted (FST (SND e)) (SND (SND e)) ::
          temporal_audit (visit+1) l blocks targets inserted ls
            (FST (SND r)) (SND (SND r))
    | _ => [F])
End

Theorem temporal_inserted_owner_probes:
  EVERY I (temporal_audit 0 "" history_probe_diamond.fn_blocks
    history_probe_diamond_target (temporal_insert_summary history_probe_diamond)
    ["E";"L";"H";"H";"H"] [] []) /\
  EVERY I (temporal_audit 0 "" history_probe_backedges.fn_blocks
    history_probe_backedges_target (temporal_insert_summary history_probe_backedges)
    ["E";"H";"D";"H";"D";"H"] [] []) /\
  EVERY I (temporal_audit 0 "" history_probe_nested.fn_blocks
    history_probe_nested_target (temporal_insert_summary history_probe_nested)
    ["E";"H";"I";"D";"I";"D";"I"] [] []) /\
  EVERY I (temporal_audit 0 "" history_probe_irreducible.fn_blocks
    history_probe_irreducible_target (temporal_insert_summary history_probe_irreducible)
    ["E";"H";"I";"H";"I";"H"] [] []) /\
  EVERY I (temporal_audit 0 "" current_probe_loop.fn_blocks
    history_probe_control_target (temporal_insert_summary current_probe_loop)
    ["E";"D";"D";"D"] [] [])
Proof
  rewrite_tac[temporal_insert_summary_def,
    history_probe_diamond_insert,history_probe_backedges_insert,
    history_probe_nested_insert,history_probe_irreducible_insert,
    history_probe_control_insert] >> rpt conj_tac >> EVAL_TAC
QED

Theorem temporal_exact_branch_coverage:
  MAP (\(_,_,_,_,op). op)
    (FLAT (MAP temporal_insert_summary
      [history_probe_diamond;history_probe_backedges;history_probe_nested;
       history_probe_irreducible;current_probe_loop])) =
    [PHI;ASSIGN;ASSIGN;PHI;ASSIGN;PHI;PHI;PHI;PHI;ASSIGN] /\
  EVERY (\(_,owners,_,_,op). op = ASSIGN ==> owners = ["v"])
    (FLAT (MAP temporal_insert_summary
      [history_probe_diamond;history_probe_backedges;history_probe_nested;
       history_probe_irreducible;current_probe_loop]))
Proof
  rewrite_tac[listTheory.MAP,temporal_insert_summary_def,
    history_probe_diamond_insert,history_probe_backedges_insert,
    history_probe_nested_insert,history_probe_irreducible_insert,
    history_probe_control_insert] >> EVAL_TAC
QED

(* Dynamic x is written at visit 3, site 9, then transported through I;
   the source x's old spelling and target name differ but their origin agrees.
   Last phase 0 is parallel entry; phase 1 below is cleanup copy. *)
Theorem temporal_nested_initialization_observations:
  temporal_lookup
    (SND (SND (temporal_replay 0 "" history_probe_nested.fn_blocks
      history_probe_nested_target ["E";"H";"I";"D";"I"] [] [])))
    "formal_var_2" = SOME ((3,9,0),0) /\
  temporal_lookup
    (SND (SND (temporal_replay 0 "" history_probe_nested.fn_blocks
      history_probe_nested_target ["E";"H"] [] [])))
    "v" = SOME ((1,4,0),1) /\
  temporal_lookup
    (SND (SND (temporal_replay 0 "" history_probe_nested.fn_blocks
      history_probe_nested_target ["E";"H"] [] [])))
    "formal_var_1" = SOME ((1,4,0),0)
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem temporal_undefined_and_stale_detection:
  ~temporal_operands [] [] [Var "x"] [Var "x"] /\
  ~temporal_operands [("x",(((1:num),(9:num),(0:num)),(1:num)))]
    [("formal_var_2",(((0:num),(9:num),(0:num)),(0:num)))] [Var "x"] [Var "formal_var_2"]
Proof
  EVAL_TAC
QED
