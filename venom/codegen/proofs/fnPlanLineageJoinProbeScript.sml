(* Candidate join inventory tests. These are not reachable-state claims. *)
Theory fnPlanLineageJoinProbe
Ancestors
  stackPlanGen stackPlanOps stackPlanTypes stackModel dfgDefs finite_map
  list rich_list pred_set arithmetic
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY]);

Definition join_inventory_def:
  join_inventory target ps <=>
    ALL_DISTINCT target /\ EVERY is_var_operand target /\
    (?n xs. ps.ps_stack = REPLICATE n dead_stack_marker ++ xs /\
      ALL_DISTINCT xs /\ EVERY (\x. MEM x target) xs /\
      (!x. MEM x xs ==> FLOOKUP ps.ps_spilled x = NONE) /\
      (!x. MEM x target <=> MEM x xs \/ x IN FDOM ps.ps_spilled))
End

Definition canonical_join_def:
  canonical_join target ps <=>
    (?n. ps.ps_stack = REPLICATE n dead_stack_marker ++ target) /\
    ps.ps_spilled = FEMPTY
End

Definition join_t18_def:
  join_t18 = MAP Var
    ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i";
     "j"; "k"; "l"; "m"; "n"; "o"; "p"; "q"; "r"]
End

Definition join_all_spilled_def:
  join_all_spilled = (init_plan_state 0) with <|
    ps_spilled := FEMPTY |+ (Var "a", 0) |+ (Var "b", 32)
      |+ (Var "c", 64) |+ (Var "d", 96) |+ (Var "e", 128)
      |+ (Var "f", 160) |+ (Var "g", 192) |+ (Var "h", 224)
      |+ (Var "i", 256) |+ (Var "j", 288) |+ (Var "k", 320)
      |+ (Var "l", 352) |+ (Var "m", 384) |+ (Var "n", 416)
      |+ (Var "o", 448) |+ (Var "p", 480) |+ (Var "q", 512)
      |+ (Var "r", 544);
    ps_alloc := (init_spill_alloc 0) with sa_next_offset := 576 |>
End

Theorem join_all_spilled_first_restore:
  (SND (reorder_one dfg_empty join_t18 0 (Var "a")
    join_all_spilled)).ps_stack =
    [EL 16 ([]:operand list); HD ([]:operand list)] ++
    MAP (\i. EL i ([]:operand list)) (GENLIST SUC 15) ++ [Var "a"]
Proof
  EVAL_TAC
QED

Theorem join_all_spilled_first_fields:
  (SND (reorder_one dfg_empty join_t18 0 (Var "a")
    join_all_spilled)).ps_alloc =
      join_all_spilled.ps_alloc with sa_free_slots := [0] /\
  FLOOKUP (SND (reorder_one dfg_empty join_t18 0 (Var "a")
    join_all_spilled)).ps_spilled (Var "a") = NONE /\
  FLOOKUP (SND (reorder_one dfg_empty join_t18 0 (Var "a")
    join_all_spilled)).ps_spilled (Var "b") = SOME 32
Proof
  EVAL_TAC
QED

Definition join_materialised_def:
  join_materialised n = (init_plan_state 0) with ps_stack :=
    REPLICATE 2 dead_stack_marker ++ REVERSE (TAKE n join_t18)
End

Theorem join_materialised_controls:
  (SND (reorder_plan dfg_empty (TAKE 16 join_t18)
    (join_materialised 16))).ps_stack =
      REPLICATE 2 dead_stack_marker ++ TAKE 16 join_t18 /\
  (SND (reorder_plan dfg_empty (TAKE 17 join_t18)
    (join_materialised 17))).ps_stack =
      REPLICATE 2 dead_stack_marker ++ TAKE 17 join_t18 /\
  (SND (reorder_plan dfg_empty join_t18
    (join_materialised 18))).ps_stack =
      REPLICATE 2 dead_stack_marker ++ join_t18
Proof
  EVAL_TAC
QED

Theorem join_all_spilled_inventory:
  join_inventory join_t18 join_all_spilled
Proof
  simp[join_inventory_def, join_t18_def, join_all_spilled_def, is_var_operand_def] >>
  qexistsl_tac [`0`, `[]`] >> simp[init_plan_state_def] >> metis_tac[]
QED

Theorem join_all_spilled_first_underflow_length:
  LENGTH (SND (reorder_one dfg_empty join_t18 0 (Var "a")
    join_all_spilled)).ps_stack = 18 /\
  LENGTH join_all_spilled.ps_stack = 0
Proof
  simp[join_all_spilled_first_restore, join_all_spilled_def, init_plan_state_def]
QED

Definition join_spilled_def:
  join_spilled n = (init_plan_state 0) with <|
    ps_spilled := FOLDL (\fm (i,op). fm |+ (op, 32*i)) FEMPTY
      (MAPi (\i op. (i,op)) (TAKE n join_t18));
    ps_alloc := (init_spill_alloc 0) with sa_next_offset := 32*n |>
End

Theorem join_spilled16_stack:
  (SND (reorder_plan dfg_empty (TAKE 16 join_t18) (join_spilled 16))).ps_stack =
    MAP Var ["h"; "i"; "b"; "j"; "d"; "k"; "f"; "l";
             "a"; "m"; "e"; "n"; "c"; "o"; "g"; "p"]
Proof
  EVAL_TAC
QED

Theorem join_spilled16_not_canonical:
  ~canonical_join (TAKE 16 join_t18)
    (SND (reorder_plan dfg_empty (TAKE 16 join_t18) (join_spilled 16)))
Proof
  simp[canonical_join_def, join_spilled16_stack, join_t18_def] >>
  strip_tac >>
  qpat_x_assum `_ = REPLICATE _ _ ++ _` (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem join_spilled17_stack:
  (SND (reorder_plan dfg_empty (TAKE 17 join_t18) (join_spilled 17))).ps_stack =
    MAP Var ["i"; "a"; "j"; "c"; "k"; "e"; "l"; "g"; "m";
             "b"; "n"; "f"; "o"; "d"; "p"; "h"; "q"]
Proof
  EVAL_TAC
QED

Theorem join_spilled16_inventory:
  join_inventory (TAKE 16 join_t18) (join_spilled 16)
Proof
  simp[join_inventory_def, join_spilled_def, join_t18_def, is_var_operand_def] >>
  qexistsl_tac [`0`, `[]`] >> simp[init_plan_state_def] >> metis_tac[]
QED

Theorem join_spilled_small_fields:
  (SND (reorder_plan dfg_empty (TAKE 16 join_t18) (join_spilled 16))).ps_alloc =
    <| sa_free_slots := GENLIST (\i. 32*i) 16;
       sa_next_offset := 512; sa_spill_base := 0 |> /\
  (SND (reorder_plan dfg_empty (TAKE 16 join_t18) (join_spilled 16))).ps_spilled = FEMPTY /\
  (SND (reorder_plan dfg_empty (TAKE 17 join_t18) (join_spilled 17))).ps_alloc =
    <| sa_free_slots := GENLIST (\i. 32*i) 17;
       sa_next_offset := 544; sa_spill_base := 0 |> /\
  (SND (reorder_plan dfg_empty (TAKE 17 join_t18) (join_spilled 17))).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Definition join_partial_def:
  join_partial n = (join_spilled n) with <|
    ps_stack := REPLICATE 2 dead_stack_marker ++ TAKE 1 join_t18;
    ps_spilled := (join_spilled n).ps_spilled \\ Var "a" |>
End

Theorem join_partial16_stack:
  (SND (reorder_plan dfg_empty (TAKE 16 join_t18) (join_partial 16))).ps_stack =
    [Var "g"; Var "h"; dead_stack_marker; Var "i"; Var "b"; Var "j";
     Var "d"; Var "k"; Var "f"; Var "l"; Var "a"; Var "m";
     Var "e"; Var "n"; Var "c"; Var "o"; dead_stack_marker; Var "p"]
Proof
  EVAL_TAC
QED

Theorem join_partial17_stack:
  (SND (reorder_plan dfg_empty (TAKE 17 join_t18) (join_partial 17))).ps_stack =
    [Var "h"; dead_stack_marker; Var "i"; Var "a"; Var "j"; Var "c";
     Var "k"; Var "e"; Var "l"; Var "g"; Var "m"; Var "b";
     Var "n"; Var "f"; Var "o"; Var "d"; Var "p"; dead_stack_marker; Var "q"]
Proof
  EVAL_TAC
QED


Theorem join_partial_small_fields:
  (SND (reorder_plan dfg_empty (TAKE 16 join_t18) (join_partial 16))).ps_alloc =
    <| sa_free_slots := GENLIST (\i. 32*(i+1)) 15;
       sa_next_offset := 512; sa_spill_base := 0 |> /\
  (SND (reorder_plan dfg_empty (TAKE 16 join_t18) (join_partial 16))).ps_spilled = FEMPTY /\
  (SND (reorder_plan dfg_empty (TAKE 17 join_t18) (join_partial 17))).ps_alloc =
    <| sa_free_slots := GENLIST (\i. 32*(i+1)) 16;
       sa_next_offset := 544; sa_spill_base := 0 |> /\
  (SND (reorder_plan dfg_empty (TAKE 17 join_t18) (join_partial 17))).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Theorem join_partial_inventory:
  join_inventory (TAKE 16 join_t18) (join_partial 16) /\
  join_inventory (TAKE 17 join_t18) (join_partial 17) /\
  join_inventory join_t18 (join_partial 18)
Proof
  rpt conj_tac >>
  simp[join_inventory_def, join_partial_def, join_spilled_def, join_t18_def,
       is_var_operand_def] >>
  qexistsl_tac [`2`, `[Var "a"]`] >>
  simp[init_plan_state_def, dead_stack_marker_def] >> metis_tac[]
QED

Theorem join_partial_small_not_canonical:
  ~canonical_join (TAKE 16 join_t18)
    (SND (reorder_plan dfg_empty (TAKE 16 join_t18) (join_partial 16))) /\
  ~canonical_join (TAKE 17 join_t18)
    (SND (reorder_plan dfg_empty (TAKE 17 join_t18) (join_partial 17)))
Proof
  conj_tac >>
  simp[canonical_join_def, join_partial16_stack, join_partial17_stack, join_t18_def] >>
  strip_tac >>
  qpat_x_assum `_ = REPLICATE _ _ ++ _`
    (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
  simp[] >> strip_tac >> gvs[dead_stack_marker_def]
QED
