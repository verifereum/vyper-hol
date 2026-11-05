(* Finite data certificates for the static demand experiment. *)
Theory makeSsaCurrentFiniteTables
Ancestors makeSsaCurrentFiniteHistory makeSsaCurrentFiniteDemandProbe
  makeSsaCurrentStaticDemandProbe makeSsaCurrentPlacementCut
  makeSsaCurrentHistoryProbe makeSsaCurrentSimDefs makeSsaCurrentAllocation
  venomInst venomExecSemantics list rich_list

Theorem current_finite_table_contains:
  !fn fn' H table.
    (!c x y. current_finite_seed fn fn' H c x y ==> MEM (c,x,y) table) /\
    (!c d kind x y u v.
      MEM (d,x,y) table /\ current_finite_edge fn fn' c d kind /\
      current_static_back fn fn' c kind x y
        (CurrentStaticRead u) (CurrentStaticRead v) ==> MEM (c,u,v) table) ==>
    !c x y. current_finite_demand fn fn' H c x y ==> MEM (c,x,y) table
Proof
  rpt gen_tac >> strip_tac >>
  `!f g J c x y. current_finite_demand f g J c x y ==>
    f = fn /\ g = fn' /\ J = H ==> MEM (c,x,y) table` suffices_by metis_tac[] >>
  ho_match_mp_tac current_finite_demand_ind >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Definition current_finite_edges_def:
  current_finite_edges fn fn' = FLAT (MAP (\c.
    FLAT (MAP (\d. MAP (\k. (c,d,k))
      (FILTER (\k. current_static_edge fn fn' c d k) [0;1;2;3]))
      (current_finite_cuts fn fn'))) (current_finite_cuts fn fn'))
End

Theorem current_finite_edges_exact:
  MEM (c,d,k) (current_finite_edges fn fn') <=>
    current_finite_edge fn fn' c d k
Proof
  simp[current_finite_edges_def, MEM_FLAT, MEM_MAP, MEM_FILTER,
    PULL_EXISTS, Excl "FILTER", current_finite_edge_def] >>
  eq_tac >- metis_tac[] >>
  strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by
    (gvs[current_static_edge_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem current_history_insert_owners:
  !fn. LIST_REL (\old new. !v.
    current_actual_inserted fn v old.bb_label <=>
    MEM v (FLAT (MAP (\i. i.inst_outputs)
      (TAKE (LENGTH new.bb_instructions - LENGTH old.bb_instructions)
        new.bb_instructions)))) fn.fn_blocks (FST (history_probe_insert fn))
Proof
  gen_tac >>
  mp_tac (Q.INST [`s` |-> `history_probe_supply`,
    `bbs'` |-> `FST (history_probe_insert fn)`,
    `s'` |-> `SND (history_probe_insert fn)`] current_actual_insertion_prefix) >>
  simp[GSYM history_probe_insert_def] >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  rpt strip_tac >>
  `n < LENGTH fn.fn_blocks` by metis_tac[] >>
  first_x_assum drule >> strip_tac >>
  gvs[] >> simp[TAKE_LENGTH_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS]
QED

Theorem current_finite_loop_inserted:
  (current_actual_inserted current_probe_loop v "E" <=> F) /\
  (current_actual_inserted current_probe_loop v "D" <=> v = "v") /\
  (current_actual_inserted current_probe_loop v "X" <=> F)
Proof
  qspec_then `current_probe_loop` mp_tac current_history_insert_owners >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``current_actual_inserted``]) >>
  simp[]
QED

Theorem current_finite_backedges_inserted:
  (current_actual_inserted history_probe_backedges v "E" <=> F) /\
  (current_actual_inserted history_probe_backedges v "H" <=> v = "v" \/ v = "x") /\
  (current_actual_inserted history_probe_backedges v "D" <=> F) /\
  (current_actual_inserted history_probe_backedges v "S" <=> F)
Proof
  qspec_then `history_probe_backedges` mp_tac current_history_insert_owners >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``current_actual_inserted``]) >>
  simp[]
QED

Definition current_finite_original_owners_def:
  current_finite_original_owners fn H h =
    case lookup_block h fn.fn_blocks of NONE => [] | SOME old =>
    FLAT (GENLIST (\i. FLAT (GENLIST (\k.
      case current_token_name H (CurrentOriginal h i k) of NONE => [] | SOME n =>
        [(n,EL k (EL i old.bb_instructions).inst_outputs)])
      (LENGTH (EL i old.bb_instructions).inst_outputs))) (LENGTH old.bb_instructions))
End

Theorem current_finite_original_owners_exact:
  MEM (n,v) (current_finite_original_owners fn H h) <=>
    ?old i k. lookup_block h fn.fn_blocks = SOME old /\
      i < LENGTH old.bb_instructions /\
      k < LENGTH (EL i old.bb_instructions).inst_outputs /\
      EL k (EL i old.bb_instructions).inst_outputs = v /\
      current_token_name H (CurrentOriginal h i k) = SOME n
Proof
  simp[current_finite_original_owners_def] >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
  simp[MEM_FLAT, MEM_GENLIST, PULL_EXISTS] >>
  eq_tac >> rpt strip_tac
  >- (Cases_on `current_token_name H (CurrentOriginal h i k)` >> gvs[] >>
      metis_tac[]) >>
  goal_assum $ drule_at Any >> simp[] >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem current_finite_owner_exact:
  current_static_owner fn H h n v <=>
    (current_actual_inserted fn v h /\
      current_token_name H (CurrentInserted v h) = SOME n) \/
    MEM (n,v) (current_finite_original_owners fn H h)
Proof
  simp[current_static_owner_def, current_finite_original_owners_exact]
QED

Theorem current_finite_loop_owners:
  MEM h ["E";"D";"X"] ==>
  (current_static_owner current_probe_loop (current_finite_history current_probe_loop) h n v <=>
    MEM (h,n,v) [("E","a","a"); ("D","v","v");
      ("D","formal_var_0","v"); ("D","b","b")])
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  simp[current_finite_owner_exact, current_finite_loop_inserted] >>
  CONV_TAC EVAL >> simp[] >> metis_tac[]
QED

Theorem current_finite_backedges_history_data:
  current_finite_history history_probe_backedges =
    [(CurrentOriginal "E" 0 0,"a","a"); (CurrentOriginal "E" 1 0,"b","b");
     (CurrentOriginal "E" 2 0,"x","x"); (CurrentInserted "v" "H","v","v");
     (CurrentInserted "x" "H","x","formal_var_0");
     (CurrentOriginal "H" 0 0,"v","formal_var_1");
     (CurrentOriginal "H" 1 0,"z","z"); (CurrentOriginal "D" 0 0,"x","formal_var_2")]
Proof
  CONV_TAC (LHS_CONV EVAL) >> REFL_TAC
QED

Theorem current_finite_backedges_owners:
  MEM h ["E";"H";"D";"S"] ==>
  (current_static_owner history_probe_backedges (current_finite_history history_probe_backedges) h n v <=>
    MEM (h,n,v) [("E","a","a"); ("E","b","b"); ("E","x","x");
      ("H","v","v"); ("H","formal_var_0","x");
      ("H","formal_var_1","v"); ("H","z","z"); ("D","formal_var_2","x")])
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  simp[current_finite_owner_exact, current_finite_backedges_inserted,
    current_finite_backedges_history_data] >>
  CONV_TAC EVAL >>
  Cases_on `v = "v"` >> simp[] >> Cases_on `v = "x"` >> simp[] >>
  metis_tac[]
QED

Definition current_loop_seed_table_def:
  current_loop_seed_table =
    [(CurrentStaticCut "" "E" 0 0, Lit 1w, Lit 1w);
     (CurrentStaticCut "" "E" 1 1, Label "D", Label "D");
     (CurrentStaticCut "E" "D" 0 0, Var "a", Var "a");
     (CurrentStaticCut "D" "D" 0 0, Var "b", Var "b")] ++
    FLAT (MAP (\p.
      [(CurrentStaticCut p "D" 1 1, Var "v", Var "formal_var_0");
       (CurrentStaticCut p "D" 1 2, Lit 2w, Lit 2w);
       (CurrentStaticCut p "D" 2 3, Var "v", Var "formal_var_0");
       (CurrentStaticCut p "D" 2 3, Label "D", Label "D");
       (CurrentStaticCut p "D" 2 3, Label "X", Label "X")]) ["E";"D"])
End

Theorem current_finite_loop_target_blocks:
  (current_finite_target current_probe_loop).fn_blocks =
    [history_probe_bb "E"
      [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
       current_probe_inst 1 JMP [Label "D"] []];
     history_probe_bb "D"
      [current_probe_inst 100 PHI [Label "E";Var "a";Label "D";Var "b"] ["formal_var_0"];
       current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"];
       current_probe_inst 3 ASSIGN [Lit 2w] ["b"];
       current_probe_inst 4 JNZ [Var "formal_var_0";Label "D";Label "X"] []];
     history_probe_bb "X" [current_probe_inst 5 STOP [] []]]
Proof
  CONV_TAC (LHS_CONV EVAL) >> CONV_TAC (RHS_CONV EVAL) >> REFL_TAC
QED


Definition current_static_seed_data_def:
  current_static_seed_data fn H p h i j old out x y <=>
   (phi_prefix_length old.bb_instructions <= i /\ i < LENGTH old.bb_instructions /\
    j = current_static_body_start old.bb_instructions out.bb_instructions +
      (i - phi_prefix_length old.bb_instructions) /\ j < LENGTH out.bb_instructions /\
    MEM (x,y) (ZIP ((EL i old.bb_instructions).inst_operands,
      (EL j out.bb_instructions).inst_operands))) \/
   (i = phi_prefix_length old.bb_instructions /\
    phi_prefix_length out.bb_instructions <= j /\
    j < current_static_body_start old.bb_instructions out.bb_instructions /\
    ?n v. (EL j out.bb_instructions).inst_opcode = ASSIGN /\
      (EL j out.bb_instructions).inst_outputs = [n] /\
      (EL j out.bb_instructions).inst_operands = [y] /\
      current_static_owner fn H h n v /\ x = Var v) \/
   (i = 0 /\ j = 0 /\
    ?inst n v. MEM inst (TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions) /\
      inst.inst_outputs = [n] /\ resolve_phi p inst.inst_operands = SOME y /\
      ((current_actual_inserted fn v h /\
        current_token_name H (CurrentInserted v h) = SOME n /\ x = Var v) \/
       (?k. k < phi_prefix_length old.bb_instructions /\
        current_token_name H (CurrentOriginal h k 0) = SOME n /\
        resolve_phi p (EL k old.bb_instructions).inst_operands = SOME x)))
End

Theorem current_static_seed_at_cut:
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h fn'.fn_blocks = SOME out ==>
  (current_static_seed fn fn' H (CurrentStaticCut p h i j) x y <=>
    current_static_seed_data fn H p h i j old out x y)
Proof
  strip_tac >>
  simp[current_static_seed_def, current_static_edge_def, current_static_seed_data_def,
    PULL_EXISTS] >>
  eq_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_static_seed_lookup:
  current_static_seed fn fn' H (CurrentStaticCut p h i j) x y <=>
  case lookup_block h fn.fn_blocks of NONE => F | SOME old =>
    case lookup_block h fn'.fn_blocks of NONE => F | SOME out =>
      current_static_seed_data fn H p h i j old out x y
Proof
  Cases_on `lookup_block h fn.fn_blocks` >>
  Cases_on `lookup_block h fn'.fn_blocks` >> simp[]
  >- (simp[current_static_seed_def, current_static_edge_def, PULL_EXISTS] >> metis_tac[])
  >- (simp[current_static_seed_def, current_static_edge_def, PULL_EXISTS] >> metis_tac[])
  >- (simp[current_static_seed_def, current_static_edge_def, PULL_EXISTS] >> metis_tac[]) >>
  irule current_static_seed_at_cut >> simp[]
QED

Theorem current_finite_loop_history_data:
  current_finite_history current_probe_loop =
    [(CurrentOriginal "E" 0 0,"a","a"); (CurrentInserted "v" "D","v","v");
     (CurrentOriginal "D" 0 0,"v","formal_var_0");
     (CurrentOriginal "D" 1 0,"b","b")]
Proof
  CONV_TAC (LHS_CONV EVAL) >> REFL_TAC
QED

Theorem current_finite_loop_source_blocks:
  current_probe_loop.fn_blocks =
    [history_probe_bb "E"
      [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
       current_probe_inst 1 JMP [Label "D"] []];
     history_probe_bb "D"
      [current_probe_inst 2 PHI [Label "E";Var "a";Label "D";Var "b"] ["v"];
       current_probe_inst 3 ASSIGN [Lit 2w] ["b"];
       current_probe_inst 4 JNZ [Var "v";Label "D";Label "X"] []];
     history_probe_bb "X" [current_probe_inst 5 STOP [] []]]
Proof
  EVAL_TAC
QED

Theorem current_loop_seed_covered:
  current_finite_seed current_probe_loop (current_finite_target current_probe_loop)
    (current_finite_history current_probe_loop) c x y ==>
  MEM (c,x,y) current_loop_seed_table
Proof
  simp[current_finite_seed_def] >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >>
  strip_tac >> gvs[] >>
  gvs[current_static_seed_lookup, current_finite_loop_target_blocks,
    current_finite_loop_source_blocks, lookup_block_def, FIND_def, INDEX_FIND_def,
    history_probe_bb_def, current_probe_inst_def] >>
  gvs[current_static_seed_data_def, phi_prefix_length_def,
    current_static_body_start_def, current_finite_loop_owners,
    current_finite_loop_inserted, current_finite_loop_history_data] >>
  gvs[current_loop_seed_table_def, current_token_name_def,
    alistTheory.ALOOKUP_def, resolve_phi_def]
QED
