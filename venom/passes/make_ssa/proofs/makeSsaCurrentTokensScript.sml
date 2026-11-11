Theory makeSsaCurrentTokens
Ancestors
  makeSsaCurrentAnalysis makeSsaCurrentDemandDominance venomInst list

(* Tokens denote occurrences, never supply-generated spellings.  The sequential
   scan below is a static name-stack scan, not parallel PHI evaluation. *)
Datatype:
  current_token = CurrentDefault string
                | CurrentOriginal string num num
                | CurrentInserted string string
End

Definition current_output_token_def:
  (current_output_token v l i j [] t = t) /\
  (current_output_token v l i j (x::xs) t =
    current_output_token v l i (SUC j) xs
      (if x = v then CurrentOriginal l i j else t))
End

Definition current_original_scan_def:
  (current_original_scan v l i [] t = t) /\
  (current_original_scan v l i (inst::insts) t =
    current_original_scan v l (SUC i) insts
      (current_output_token v l i 0 inst.inst_outputs t))
End

Definition current_block_token_def:
  current_block_token fn inserted v l t =
    case lookup_block l fn.fn_blocks of
      NONE => t
    | SOME bb => current_original_scan v l 0 bb.bb_instructions
        (if inserted v l then CurrentInserted v l else t)
End

(* A finite root-to-parent dpath is supplied explicitly.  Consumers must prove
   it is the actual dominator dpath; no total unguarded idom recursion is used. *)
Definition current_chain_token_def:
  (current_chain_token fn inserted v [] t = t) /\
  (current_chain_token fn inserted v (l::ls) t =
    current_chain_token fn inserted v ls
      (current_block_token fn inserted v l t))
End

Definition current_inherited_token_def:
  current_inherited_token fn inserted v dpath =
    current_chain_token fn inserted v dpath (CurrentDefault v)
End

Definition current_token_chain_def:
  (current_token_chain dom root [] l <=> l = root) /\
  (current_token_chain dom root (p::ps) l <=>
    current_token_chain dom root ps p /\ idom_of dom l = SOME p)
End

Theorem current_output_token_absent:
  !xs j t. ~MEM v xs ==> current_output_token v l i j xs t = t
Proof
  Induct >> simp[current_output_token_def] >> rpt strip_tac >> simp[]
QED

Theorem current_original_scan_absent:
  !insts i t. EVERY (\inst. ~MEM v inst.inst_outputs) insts ==>
    current_original_scan v l i insts t = t
Proof
  Induct >> simp[current_original_scan_def] >> rpt strip_tac >>
  simp[current_output_token_absent]
QED

Theorem current_chain_token_append:
  !xs ys t. current_chain_token fn ins v (xs ++ ys) t =
    current_chain_token fn ins v ys (current_chain_token fn ins v xs t)
Proof
  Induct >> simp[current_chain_token_def]
QED

Theorem current_inherited_token_root:
  current_inherited_token fn ins v [] = CurrentDefault v
Proof
  simp[current_inherited_token_def, current_chain_token_def]
QED

Theorem current_inherited_token_step:
  current_inherited_token fn ins v (dpath ++ [p]) =
    current_block_token fn ins v p (current_inherited_token fn ins v dpath)
Proof
  simp[current_inherited_token_def, current_chain_token_append,
       current_chain_token_def]
QED

Theorem current_no_local_token:
  lookup_block l fn.fn_blocks = SOME bb /\ ~ins v l /\
  EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions ==>
  current_block_token fn ins v l t = t
Proof
  simp[current_block_token_def, current_original_scan_absent]
QED

(* Repeated outputs retain distinct positions; the last static update wins. *)
Theorem current_output_token_repeated_probe:
  current_output_token "x" "b" 3 0 ["x"; "y"; "x"]
    (CurrentDefault "x") = CurrentOriginal "b" 3 2
Proof
  EVAL_TAC
QED

Theorem current_token_chain_parent:
  current_token_chain dom root ps p /\ idom_of dom l = SOME p ==>
  current_token_chain dom root (p::ps) l
Proof
  simp[current_token_chain_def]
QED

(* current_token_chain stores parents nearest first; the scan takes their
   reverse, from root to immediate parent. *)
Theorem current_parent_inherited_token:
  current_inherited_token fn ins v (REVERSE (p::ps)) =
    current_block_token fn ins v p
      (current_inherited_token fn ins v (REVERSE ps))
Proof
  simp[current_inherited_token_step]
QED

(* Concrete static scans: entry E defines x; only arm A of a diamond
   redefines it.  This falsifies arbitrary incoming-edge token agreement. *)
Definition current_token_diamond_def:
  current_token_diamond fn = fn with fn_blocks :=
    [<| bb_label := "E";
        bb_instructions := [mk_inst 0 ASSIGN [] ["x"]] |>;
     <| bb_label := "A";
        bb_instructions := [mk_inst 1 ASSIGN [] ["x"]] |>;
     <| bb_label := "B"; bb_instructions := [] |>;
     <| bb_label := "J"; bb_instructions := [] |>]
End

Theorem current_token_straight_probe:
  current_inherited_token (current_token_diamond fn) (\v l. F) "x"
    ["E"; "B"] = CurrentOriginal "E" 0 0
Proof
  simp[current_inherited_token_def, current_token_diamond_def,
       current_chain_token_def, current_block_token_def, lookup_block_def, FIND_thm,
       current_original_scan_def, current_output_token_def, mk_inst_def]
QED

Theorem current_token_diamond_probe:
  current_inherited_token (current_token_diamond fn) (\v l. F) "x"
    ["E"; "A"] <> 
  current_inherited_token (current_token_diamond fn) (\v l. F) "x" ["E"]
Proof
  simp[current_inherited_token_def, current_token_diamond_def,
       current_chain_token_def, current_block_token_def, lookup_block_def, FIND_thm,
       current_original_scan_def, current_output_token_def, mk_inst_def]
QED

Theorem current_token_diamond_inserted_probe:
  current_block_token (current_token_diamond fn) (\v l. l = "J") "x" "J"
    (CurrentOriginal "E" 0 0) = CurrentInserted "x" "J"
Proof
  simp[current_token_diamond_def, current_block_token_def, lookup_block_def, FIND_thm,
       current_original_scan_def]
QED

(* At a loop header an original PHI comes after an inserted PHI.  This
   equation asserts static occurrence order only, not execution order of
   the PHI inputs, which are evaluated in parallel. *)
Theorem current_token_loop_phi_probe:
  current_block_token
    (fn with fn_blocks :=
      [<| bb_label := "H";
          bb_instructions := [mk_inst 2 PHI [Label "E"; Var "x";
                                             Label "H"; Var "y"] ["x"]] |>])
    (\v l. T) "x" "H" (CurrentDefault "x") = CurrentOriginal "H" 0 0
Proof
  simp[current_block_token_def, lookup_block_def, FIND_thm, current_original_scan_def,
       current_output_token_def, mk_inst_def]
QED

Theorem current_token_chain_unique:
  !ps qs l. idom_of dom root = NONE /\
    current_token_chain dom root ps l /\
    current_token_chain dom root qs l ==> ps = qs
Proof
  Induct >> Cases_on `qs` >> simp[current_token_chain_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_token_chain_root:
  idom_of dom root = NONE ==>
  (current_token_chain dom root ps root <=> ps = [])
Proof
  Cases_on `ps` >> simp[current_token_chain_def]
QED

Theorem current_token_chain_same_parent:
  idom_of dom root = NONE /\ current_token_chain dom root ps a /\
  current_token_chain dom root qs b /\ idom_of dom b = SOME a ==>
  qs = a::ps
Proof
  metis_tac[current_token_chain_parent, current_token_chain_unique]
QED

(* Once a graph argument has identified the immediate predecessor as parent,
   token agreement needs neither liveness unfolding nor supply arithmetic. *)
Theorem current_token_parent_edge:
  idom_of dom root = NONE /\ current_token_chain dom root ps a /\
  current_token_chain dom root qs b /\ idom_of dom b = SOME a ==>
  current_inherited_token fn ins v (REVERSE qs) =
  current_block_token fn ins v a
    (current_inherited_token fn ins v (REVERSE ps))
Proof
  strip_tac >> drule_all current_token_chain_same_parent >> strip_tac >>
  simp[current_inherited_token_step]
QED
