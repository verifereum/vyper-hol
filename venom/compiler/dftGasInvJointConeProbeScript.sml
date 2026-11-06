Theory dftGasInvJointConeProbe
Ancestors
  dftGasInvForwardConeProbe dftGasInvAliasNormal list rich_list

(* Extra cases: pseudo prefix, deeper aliases, and an irrelevant producer
   whose only consumer is an unused ASSIGN between COPY and REVERT. *)
Definition inv_joint_extra_def:
  inv_joint_extra =
  [<|bb_label := "entry"; bb_instructions :=
    [mk_inst 0 PARAM [Lit 0w] ["p"];
     mk_inst 1 ASSIGN [Var "p"] ["a"];
     mk_inst 2 ASSIGN [Var "a"] ["b"];
     mk_inst 3 ASSIGN [Lit 8w] ["sz"];
     mk_inst 4 RETURNDATACOPY [Var "b"; Lit 0w; Var "sz"] [];
     mk_inst 5 ASSIGN [Var "a"] ["c"];
     mk_inst 6 ASSIGN [Var "c"] ["d"];
     mk_inst 7 ASSIGN [Var "sz"] ["n"];
     mk_inst 8 REVERT [Var "d"; Var "n"] []]|>;
   <|bb_label := "entry"; bb_instructions :=
    [mk_inst 0 ADD [Lit 2w; Lit 3w] ["z"];
     mk_inst 1 ASSIGN [Lit 32w] ["p"];
     mk_inst 2 RETURNDATACOPY [Var "p"; Lit 0w; Lit 8w] [];
     mk_inst 3 ASSIGN [Var "z"] ["unused"];
     mk_inst 4 ASSIGN [Var "p"] ["q"];
     mk_inst 5 REVERT [Var "q"; Lit 8w] []]|>]
End

Definition inv_joint_blocks_def:
  inv_joint_blocks = inv_cone_blocks ++ inv_joint_extra
End
(* Incremental scan avoids quadratically replaying the initialized run. *)
Definition inv_joint_seek_def:
  inv_joint_seek bi opc 0 n st = n /\
  inv_joint_seek bi opc (SUC fuel) n st =
    if (case st.ds_stack of DfsEmit i :: rest => i.inst_opcode = opc | _ => F)
    then n else inv_joint_seek bi opc fuel (SUC n)
      (dfs_step bi [] (dft_eda bi) (build_offspring_map bi []) T st)
End

Definition inv_joint_before_def:
  inv_joint_before bi opc = inv_joint_seek bi opc 40 0 (inv_cone_state bi [] 0)
End

Definition inv_joint_prefix_def:
  inv_joint_prefix bi n = FILTER (\i. is_pseudo i.inst_opcode) bi ++
    (inv_cone_state bi [] n).ds_output
End

Definition inv_joint_above_def:
  inv_joint_above [] = [] /\
  inv_joint_above (w :: ws) =
    if (case w of DfsEmit i => i.inst_opcode = REVERT | _ => F)
    then [] else w :: inv_joint_above ws
End

(* Bounded least-cone approximation. Emitted and pseudo nodes are stopping
   points, but visited-only nodes are deliberately NOT stopping points. *)
Definition inv_joint_expand_def:
  inv_joint_expand bi emitted nodes = nub (nodes ++ FLAT
    (MAP (\i. if MEM i.inst_id emitted \/ is_pseudo i.inst_opcode then []
          else inst_all_deps bi [] (dft_eda bi) i) nodes))
End

Definition inv_joint_cone_def:
  inv_joint_cone bi st = FUNPOW
    (inv_joint_expand bi (MAP (\i. i.inst_id) st.ds_output)) (LENGTH bi)
    (FLAT (MAP (\w. case w of DfsProcess i => [i] | _ => [])
      (inv_joint_above st.ds_stack)))
End

Definition inv_joint_class_def:
  inv_joint_class bi st <=>
    EVERY (\i. MEM i.inst_id (MAP (\j. j.inst_id) st.ds_output) \/
       is_pseudo i.inst_opcode \/ i.inst_opcode = ASSIGN)
      (inv_joint_cone bi st) /\
    EVERY (\w. case w of DfsEmit i => i.inst_opcode = ASSIGN | _ => T)
      (inv_joint_above st.ds_stack) /\
    EVERY (\i. ~MEM i.inst_id st.ds_visited \/
        MEM i.inst_id (MAP (\j. j.inst_id) st.ds_output) \/
        is_pseudo i.inst_opcode \/
        EXISTS (\w. case w of DfsEmit j => j.inst_id = i.inst_id /\
                       j.inst_opcode = ASSIGN | _ => F) (inv_joint_above st.ds_stack))
      (inv_joint_cone bi st)
End

Definition inv_joint_origins_def:
  inv_joint_origins prefix inst =
    MAP (resolve_block_assigns (REVERSE prefix))
      (if inst.inst_opcode = RETURNDATACOPY then
         [EL 0 inst.inst_operands; EL 2 inst.inst_operands]
       else inst.inst_operands)
End

Theorem inv_joint_times:
  MAP (\bb. (inv_joint_before bb.bb_instructions RETURNDATACOPY,
              inv_joint_before bb.bb_instructions REVERT)) inv_joint_blocks =
  [(4,8); (10,19); (8,12); (9,16); (9,18); (8,12)]
Proof
  simp_tac bool_ss [inv_joint_blocks_def, inv_cone_blocks_def, inv_joint_extra_def,
             MAP, APPEND, CONS_11] >> rpt conj_tac >>
  EVAL_TAC
QED

(* Explicit coordinates: block, before COPY, before REVERT, source COPY,
   source REVERT. The scan above independently checks the scheduler times. *)
Definition inv_joint_cases_def:
  (inv_joint_cases : (num # num # num # num # num) list) =
    [(0,4,8,2,3); (1,10,19,4,8); (2,8,12,4,5);
     (3,9,16,5,6); (4,9,18,4,8); (5,8,12,2,5)]
End

Theorem inv_joint_interval_class:
  EVERY (\(b,c,r,i,j). EVERY (\n.
     inv_joint_class (EL b inv_joint_blocks).bb_instructions
       (inv_cone_state (EL b inv_joint_blocks).bb_instructions [] n))
     (GENLIST (\k. SUC c + k) (r - c))) inv_joint_cases
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``inv_joint_class``]) >>
  simp_tac bool_ss [EVERY_DEF] >> rpt conj_tac >> EVAL_TAC
QED

Theorem inv_joint_use_origins:
  EVERY (\(b,c,r,i,j).
    inv_joint_origins
      (inv_joint_prefix (EL b inv_joint_blocks).bb_instructions c)
      (EL i (EL b inv_joint_blocks).bb_instructions) =
    inv_joint_origins
      (TAKE i (EL b inv_joint_blocks).bb_instructions)
      (EL i (EL b inv_joint_blocks).bb_instructions) /\
    inv_joint_origins
      (inv_joint_prefix (EL b inv_joint_blocks).bb_instructions r)
      (EL j (EL b inv_joint_blocks).bb_instructions) =
    inv_joint_origins
      (TAKE j (EL b inv_joint_blocks).bb_instructions)
      (EL j (EL b inv_joint_blocks).bb_instructions) /\
    inv_joint_origins
      (inv_joint_prefix (EL b inv_joint_blocks).bb_instructions c)
      (EL i (EL b inv_joint_blocks).bb_instructions) =
    inv_joint_origins
      (inv_joint_prefix (EL b inv_joint_blocks).bb_instructions r)
      (EL j (EL b inv_joint_blocks).bb_instructions)) inv_joint_cases
Proof
  simp_tac bool_ss [inv_joint_cases_def, EVERY_DEF] >> rpt conj_tac >> EVAL_TAC
QED

Theorem inv_joint_snapshots:
  MAP (\(b,c,r,i,j).
    (inv_cone_snapshot (inv_cone_state (EL b inv_joint_blocks).bb_instructions [] (SUC c)),
     inv_cone_snapshot (inv_cone_state (EL b inv_joint_blocks).bb_instructions [] r)))
    inv_joint_cases =
  [(([(F,1); (T,3)],[0;2],[0;2;3]), ([(T,3)],[0;2;1],[1;0;2;3]));
   (([(F,7); (F,6); (T,8)],[1;3;0;2;4],[0;2;1;3;4;8]),
    ([(T,8)],[1;3;0;2;4;7;5;6],[5;6;7;0;2;1;3;4;8]));
   (([(F,3); (T,5)],[0;1;2;4],[2;4;5;0;1]),
    ([(T,5)],[0;1;2;4;3],[3;2;4;5;0;1]));
   (([(F,4); (F,3); (T,6)],[0;2;1;5],[1;5;6;0;2]),
    ([(T,6)],[0;2;1;5;4;3],[3;4;1;5;6;0;2]));
   (([(F,7); (F,6); (T,8)],[3;1;2;4],[0;1;2;3;4;8]),
    ([(T,8)],[3;1;2;4;7;5;6],[5;6;7;0;1;2;3;4;8]));
   (([(F,4); (T,5)],[0;3;1;2],[1;2;5;0;3]),
    ([(T,5)],[0;3;1;2;4],[4;1;2;5;0;3]))]
Proof
  EVAL_TAC
QED

Theorem inv_joint_extra_pairs:
  revert_forward_pair (EL 0 inv_joint_extra) 4 8 /\
  revert_forward_pair (EL 1 inv_joint_extra) 2 5 /\
  revert_forward_pair (dft_block [] (EL 0 inv_joint_extra)) 4 8 /\
  revert_forward_pair (dft_block [] (EL 1 inv_joint_extra)) 3 5
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >>
  `k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7` by decide_tac >> gvs[]
QED

Theorem inv_joint_extra_shapes:
  EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    EVERY inst_wf bb.bb_instructions /\
    (LAST bb.bb_instructions).inst_opcode = REVERT) inv_joint_extra
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8` by decide_tac >>
  gvs[] >> EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC >>
  FIRST (map (fn idx => qexists_tac idx >> EVAL_TAC >> NO_TAC)
    [`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`])
QED

(* No irrelevant ASSIGN/producer is assumed to lie in the residual cone. *)
Theorem inv_joint_irrelevant:
  ~MEM 0 (MAP (\i. i.inst_id)
    (inv_joint_cone (EL 1 inv_joint_extra).bb_instructions
      (inv_cone_state (EL 1 inv_joint_extra).bb_instructions [] 9))) /\
  ~MEM 3 (MAP (\i. i.inst_id)
    (inv_joint_cone (EL 1 inv_joint_extra).bb_instructions
      (inv_cone_state (EL 1 inv_joint_extra).bb_instructions [] 9)))
Proof
  EVAL_TAC
QED

Theorem inv_joint_markers:
  EVERY (\(b,c,r,i,j).
    HD (inv_cone_state (EL b inv_joint_blocks).bb_instructions [] c).ds_stack =
      DfsEmit (EL i (EL b inv_joint_blocks).bb_instructions) /\
    HD (inv_cone_state (EL b inv_joint_blocks).bb_instructions [] r).ds_stack =
      DfsEmit (EL j (EL b inv_joint_blocks).bb_instructions)) inv_joint_cases
Proof
  simp_tac bool_ss [inv_joint_cases_def, EVERY_DEF] >> rpt conj_tac >> EVAL_TAC
QED

(* Candidate universal contract (NOT proved by these finite tests).
   Given source pair i<j and an initialized empty-order DFS run S_n,
   let C be the source COPY, R the source REVERT, phis the pseudo prefix,
   E_n = ids(S_n.output), W_n the work above the designated Emit R,
   and K_n the LEAST dependency closure of Process seeds in W_n, stopping
   only at E_n and pseudo nodes. inv_joint_cone approximates K_n here by
   LENGTH bi iterations; universal stabilization still needs a theorem.

   At the cut n=c+1 following Emit C, require:
   (1) stack = W_n ++ [Emit R] ++ tail, with a fixed tail;
   (2) K_n minus E_n/pseudos contains only ASSIGNs;
   (3) every Emit in W_n is ASSIGN, and each visited-but-unemitted
       non-pseudo K_n node has a matching ASSIGN Emit in W_n;
   (4) origins of C at phis++output_c equal its source TAKE i origins;
       R origins at source TAKE j equal those C origins.
   The initial producer must derive (1)-(4) from source SSA/forwarding,
   EDA dependencies and actual initialized DFS lineage, NOT assume them.

   Fresh Process transition: its dependency children remain inside K_n,
   its newly pushed Emit is ASSIGN, and stack tail is unchanged.
   Visited Process transition: skip only with completed-output membership
   or an existing pending ASSIGN Emit above R (never confuse visited/E).
   Pseudo Process: skip with phis already present in the use prefix.
   Emit transition: append an ASSIGN; maintain canonical origins of the
   pending R operands relative to source origins. This needs dependency
   provenance/unique producers; normalization alone does NOT supply it.
   Each transition must preserve (1)-(3) and that origin correspondence.
   At Emit R, origin correspondence yields equality at the two actual
   use prefixes (as checked by inv_joint_use_origins).

   Projection still required: all instructions emitted between C and R
   are ASSIGN; alias normalization and no intervening non-ASSIGN clobber
   turn equal canonical origins into the same_after_assigns conjuncts
   of revert_forward_pair, including COPY's zero source operand. Pseudo
   prefix insertion and the actual dft_block schedule must be related to
   these snapshots. None of initialization, closure stabilization,
   transition preservation, or universal projection is claimed here.

   Diagnostic limit: the irrelevant ADD/unused ASSIGN case is outside
   the residual cone, but both happen to have emitted before COPY. It
   therefore tests locality, not failure of global emitted closure.
   These are bounded examples, not a proof of the frozen task theorem. *)

Theorem inv_joint_unique_outputs:
  EVERY (\bb. ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
    bb.bb_instructions))) inv_joint_extra
Proof
  EVAL_TAC
QED
