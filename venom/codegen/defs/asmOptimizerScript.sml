(*
 * Vyper's final assembly optimizer.
 *
 * Upstream: vyperlang/vyper@577d2534 (v0.5.0b1),
 *   vyper/evm/assembler/optimizer.py
 *
 * Each rewrite mirrors its Python function, including where Python re-checks
 * the same index after a rewrite and where it moves on. The rules don't
 * commute, so this order is what makes the output bytes match. Each returns
 * the rewritten list and whether it changed anything; optimize_assembly runs
 * them in Python's order until a round changes nothing, failing (as Python
 * raises CompilerPanic) after 1024 rounds.
 *
 * HOL's assembly has no CONST/CONSTREF items, so _prune_unused_consts has no
 * counterpart and _prune_unreachable_code has no declarations to keep.
 *
 * TOP-LEVEL:
 *   optimize_assembly   — the fixpoint, NONE where Python panics
 *   asm_opt_finalizer   — the optimizer as an assembly_finalizer
 *)

Theory asmOptimizer
Ancestors
  asmIR assemblyFinalizer venomCompilerTypes

(* ===== _prune_unreachable_code ===== *)

Definition asm_terminal_op_def:
  asm_terminal_op inst <=>
    MEM inst (MAP AsmOp ["JUMP"; "RETURN"; "REVERT"; "STOP"; "INVALID"])
End

Definition asm_reachable_marker_def:
  (asm_reachable_marker (AsmLabel _) <=> T) /\
  (asm_reachable_marker (AsmDataHeader _) <=> T) /\
  (asm_reachable_marker _ <=> F)
End

(* Code after a terminal op, up to the next label or data header. [dropping]
   says the walk is inside such a stretch. *)
Definition prune_unreachable_walk_def:
  (prune_unreachable_walk dropping [] = ([], F)) /\
  (prune_unreachable_walk dropping (inst :: rest) =
     if dropping /\ ~asm_reachable_marker inst then
       let (out, _) = prune_unreachable_walk T rest in (out, T)
     else
       let (out, changed) =
         prune_unreachable_walk (asm_terminal_op inst) rest in
         (inst :: out, changed))
End

Definition prune_unreachable_code_def:
  prune_unreachable_code asm = prune_unreachable_walk F asm
End

(* ===== _merge_iszero ===== *)

Definition asm_returns_zero_or_one_def:
  asm_returns_zero_or_one inst <=>
    MEM inst (MAP AsmOp ["LT"; "GT"; "SLT"; "SGT"; "EQ"; "ISZERO"; "CALL";
                         "STATICCALL"; "CALLCODE"; "DELEGATECALL"])
End

(* X ISZERO ISZERO -> X, re-checking at X. *)
Definition merge_iszero_pairs_def:
  (merge_iszero_pairs (x :: y :: z :: rest) =
     if asm_returns_zero_or_one x /\ y = AsmOp "ISZERO" /\
        z = AsmOp "ISZERO" then
       let (out, _) = merge_iszero_pairs (x :: rest) in (out, T)
     else
       let (out, changed) = merge_iszero_pairs (y :: z :: rest) in
         (x :: out, changed)) /\
  (merge_iszero_pairs asm = (asm, F))
Termination
  WF_REL_TAC `measure LENGTH` >> rw[]
End

(* ISZERO ISZERO PUSHLABEL l JUMPI -> PUSHLABEL l JUMPI, re-checking there. *)
Definition asm_is_push_label_def:
  asm_is_push_label inst <=> case inst of AsmPushLabel _ => T | _ => F
End

Definition merge_iszero_jumpi_def:
  (merge_iszero_jumpi (a :: b :: c :: d :: rest) =
     if a = AsmOp "ISZERO" /\ b = AsmOp "ISZERO" /\ asm_is_push_label c /\
        d = AsmOp "JUMPI" then
       let (out, _) = merge_iszero_jumpi (c :: d :: rest) in (out, T)
     else
       let (out, changed) = merge_iszero_jumpi (b :: c :: d :: rest) in
         (a :: out, changed)) /\
  (merge_iszero_jumpi asm = (asm, F))
Termination
  WF_REL_TAC `measure LENGTH` >> rw[]
End

Definition merge_iszero_def:
  merge_iszero asm =
    let (asm1, changed1) = merge_iszero_pairs asm in
    let (asm2, changed2) = merge_iszero_jumpi asm1 in
      (asm2, changed1 \/ changed2)
End

(* ===== _merge_jumpdests ===== *)

Definition rename_push_label_def:
  rename_push_label old new inst =
    case inst of
      AsmPushLabel l => if l = old then AsmPushLabel new else inst
    | _ => inst
End

Definition push_label_used_def:
  push_label_used old asm <=> MEM (AsmPushLabel old) asm
End

(* Python walks the list by index and renames PUSHLABELs in the whole list,
   so the walk carries the reversed prefix it has passed. Python's bound
   needs three items left even where only two are inspected. *)
Definition merge_jumpdests_walk_def:
  merge_jumpdests_walk done rest changed =
    case rest of
      AsmLabel x :: next :: third :: more =>
        let target =
          (case next of
             AsmLabel y => if y <> x then SOME y else NONE
           | AsmPushLabel y =>
               if third = AsmOp "JUMP" then SOME y else NONE
           | _ => NONE) in
        (case target of
           NONE =>
             merge_jumpdests_walk (AsmLabel x :: done)
               (next :: third :: more) changed
         | SOME y =>
             let renamed = MAP (rename_push_label x y) rest;
                 renamed_done = MAP (rename_push_label x y) done;
                 hit = push_label_used x (REVERSE done ++ rest) in
               merge_jumpdests_walk (HD renamed :: renamed_done)
                 (TL renamed) (changed \/ hit))
    | inst :: next :: third :: more =>
        merge_jumpdests_walk (inst :: done) (next :: third :: more) changed
    | _ => (REVERSE done ++ rest, changed)
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND)` >> rw[]
End

Definition merge_jumpdests_def:
  merge_jumpdests asm = merge_jumpdests_walk [] asm F
End

(* ===== _prune_inefficient_jumps ===== *)

(* PUSHLABEL x JUMP LABEL x -> LABEL x *)
Definition asm_jump_to_next_def:
  asm_jump_to_next a b c <=>
    b = AsmOp "JUMP" /\
    case (a, c) of
      (AsmPushLabel x, AsmLabel y) => x = y
    | _ => F
End

Definition prune_inefficient_jumps_def:
  (prune_inefficient_jumps (a :: b :: c :: rest) =
     if asm_jump_to_next a b c then
       let (out, _) = prune_inefficient_jumps (c :: rest) in (out, T)
     else
       let (out, changed) = prune_inefficient_jumps (b :: c :: rest) in
         (a :: out, changed)) /\
  (prune_inefficient_jumps asm = (asm, F))
Termination
  WF_REL_TAC `measure LENGTH` >> rw[]
End

(* ===== _optimize_inefficient_jumps ===== *)

(* PUSHLABEL c JUMPI PUSHLABEL x JUMP LABEL c
   -> ISZERO PUSHLABEL x JUMPI LABEL c *)
Definition asm_jumpi_over_jump_def:
  asm_jumpi_over_jump a b c d e <=>
    b = AsmOp "JUMPI" /\ asm_is_push_label c /\ d = AsmOp "JUMP" /\
    case (a, e) of
      (AsmPushLabel x, AsmLabel y) => x = y
    | _ => F
End

Definition optimize_inefficient_jumps_def:
  (optimize_inefficient_jumps (a :: b :: c :: d :: e :: rest) =
     if asm_jumpi_over_jump a b c d e then
       let (out, _) =
         optimize_inefficient_jumps
           (AsmOp "ISZERO" :: c :: AsmOp "JUMPI" :: e :: rest) in
         (out, T)
     else
       let (out, changed) =
         optimize_inefficient_jumps (b :: c :: d :: e :: rest) in
         (a :: out, changed)) /\
  (optimize_inefficient_jumps asm = (asm, F))
Termination
  WF_REL_TAC `measure LENGTH` >> rw[]
End

(* ===== _prune_unused_jumpdests ===== *)

(* Labels referenced by a label push, a label-plus-offset push, or a data
   item (likely a jump table). *)
Definition asm_label_refs_def:
  asm_label_refs asm =
    FLAT (MAP (\inst. case inst of
                        AsmPushLabel l => [l]
                      | AsmPushOfst l _ => [l]
                      | AsmDataLabel l => [l]
                      | _ => []) asm)
End

Definition asm_unused_label_def:
  asm_unused_label used inst <=>
    case inst of AsmLabel l => ~MEM l used | _ => F
End

Definition prune_unused_jumpdests_def:
  prune_unused_jumpdests asm =
    let used = asm_label_refs asm in
      (FILTER ($~ o asm_unused_label used) asm,
       EXISTS (asm_unused_label used) asm)
End

(* ===== _stack_peephole_opts ===== *)

(* Python compares the lowercased name with COMMUTATIVE_OPS. *)
Definition asm_commutative_op_def:
  asm_commutative_op inst <=>
    case inst of
      AsmOp name =>
        MEM (MAP toLower name) ["add"; "mul"; "eq"; "ne"; "and"; "or"; "xor"]
    | _ => F
End

Definition asm_swap_op_def:
  asm_swap_op inst <=>
    case inst of AsmOp name => isPREFIX "SWAP" name | _ => F
End

(* The last three rules run in sequence at the same index (no `continue`),
   each seeing the previous one's result. Python reads past the end of the
   list there without a bound check; that IndexError is NONE here. *)
Definition peep_swap_pair_def:
  peep_swap_pair a b c rest =
    if asm_swap_op a /\ a = b then (c :: rest, T)
    else (a :: b :: c :: rest, F)
End

Definition peep_swap_comm_def:
  peep_swap_comm l =
    case l of
      [] => NONE
    | x :: r =>
        if x = AsmOp "SWAP1" then
          (case r of
             [] => NONE
           | y :: r' => SOME (if asm_commutative_op y then (r, T) else (l, F)))
        else SOME (l, F)
End

Definition peep_dup_swap_def:
  peep_dup_swap l =
    case l of
      [] => NONE
    | x :: r =>
        if x = AsmOp "DUP1" then
          (case r of
             [] => NONE
           | y :: r' =>
               SOME (if y = AsmOp "SWAP1" then (x :: r', T) else (l, F)))
        else SOME (l, F)
End

Theorem peep_swap_pair_length:
  peep_swap_pair a b c rest = (l, ch) ==>
  l <> [] /\ LENGTH l <= LENGTH rest + 3
Proof
  rw[peep_swap_pair_def] >> simp[]
QED

Theorem peep_swap_comm_length:
  peep_swap_comm l = SOME (l', ch) ==> l' <> [] /\ LENGTH l' <= LENGTH l
Proof
  rw[peep_swap_comm_def, AllCaseEqs()] >> simp[]
QED

Theorem peep_dup_swap_length:
  peep_dup_swap l = SOME (l', ch) ==> l' <> [] /\ LENGTH l' <= LENGTH l
Proof
  rw[peep_dup_swap_def, AllCaseEqs()] >> simp[]
QED

Definition stack_peephole_opts_def:
  stack_peephole_opts asm =
    case asm of
      a :: b :: c :: rest =>
        if [a; b; c] = MAP AsmOp ["DUP1"; "SWAP2"; "SWAP1"] then
          OPTION_MAP (\(out, _). (out, T))
            (stack_peephole_opts (AsmOp "SWAP1" :: AsmOp "DUP2" :: rest))
        else if [a; b; c] = MAP AsmOp ["DUP1"; "SWAP1"; "POP"] then
          OPTION_MAP (\(out, _). (out, T)) (stack_peephole_opts rest)
        else if [a; b; c] = MAP AsmOp ["SWAP1"; "POP"; "POP"] then
          OPTION_MAP (\(out, _). (out, T))
            (stack_peephole_opts (b :: c :: rest))
        else
          let (l1, ch1) = peep_swap_pair a b c rest in
          (case peep_swap_comm l1 of
             NONE => NONE
           | SOME (l2, ch2) =>
               (case peep_dup_swap l2 of
                  NONE => NONE
                | SOME (l3, ch3) =>
                    OPTION_MAP (\(out, ch'). (HD l3 :: out,
                                              ch1 \/ ch2 \/ ch3 \/ ch'))
                      (stack_peephole_opts (TL l3))))
    | _ => SOME (asm, F)
Termination
  WF_REL_TAC `measure LENGTH` >> rw[] >>
  qpat_x_assum `(_, _) = peep_swap_pair _ _ _ _` (assume_tac o SYM) >>
  imp_res_tac peep_swap_pair_length >>
  imp_res_tac peep_swap_comm_length >>
  imp_res_tac peep_dup_swap_length >>
  gvs[] >> decide_tac
End

(* ===== The fixpoint ===== *)

Definition optimize_round_def:
  optimize_round asm0 =
    let (asm1, c1) = prune_unreachable_code asm0 in
    let (asm2, c2) = merge_iszero asm1 in
    let (asm3, c3) = merge_jumpdests asm2 in
    let (asm4, c4) = prune_inefficient_jumps asm3 in
    let (asm5, c5) = optimize_inefficient_jumps asm4 in
    let (asm6, c6) = prune_unused_jumpdests asm5 in
      OPTION_MAP (\(asm7, c7). (asm7, c1 \/ c2 \/ c3 \/ c4 \/ c5 \/ c6 \/ c7))
        (stack_peephole_opts asm6)
End

Definition optimize_assembly_rounds_def:
  (optimize_assembly_rounds 0 asm = NONE) /\
  (optimize_assembly_rounds (SUC n) asm =
     case optimize_round asm of
       NONE => NONE
     | SOME (asm', changed) =>
         if changed then optimize_assembly_rounds n asm' else SOME asm')
End

Definition optimize_assembly_def:
  optimize_assembly asm = optimize_assembly_rounds 1024 asm
End

Definition asm_opt_finalizer_def:
  asm_opt_finalizer (rpolicy : resolved_compiler_policy) asm =
    if rpolicy.rpol_final_assembly = FAP_Optimize then optimize_assembly asm
    else SOME asm
End

(* The finalizers the top-level compiler theorems cover: the identity
   (Python's -O none) and the final assembly optimizer (Python's O1). *)
Definition accepted_finalizers_def:
  accepted_finalizers : assembly_finalizer set =
    {K SOME; asm_opt_finalizer}
End
