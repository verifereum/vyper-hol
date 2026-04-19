(*
 * DFT Topological Sort — DFS output respects data dependencies.
 *
 * Key result: schedule_output_producer_before
 *   In the DFS output, every instruction's data-dep producer
 *   (producing_inst result, in the ORIGINAL block order) appears earlier.
 *
 * This is used to prove defs_before_uses (dft_block order bb).bb_instructions.
 *
 * Requires eda_topo_compatible: all deps (data + EDA) respect the
 * original block instruction order. build_eda always satisfies this.
 *)

Theory dftTopoSort
Ancestors
  dftStructural dftDefs venomExecSemantics
  venomInst passSharedDefs
  list rich_list sorting
  finite_map pred_set pair arithmetic
  combin option
Libs
  BasicProvers

(* ===== defs_before_uses: defined here, used by dftCorrectness ===== *)

Definition defs_before_uses_def:
  defs_before_uses insts <=>
    !j var prod.
      j < LENGTH insts /\
      MEM (Var var) (EL j insts).inst_operands /\
      producing_inst insts var = SOME prod ==>
      ?i. i < j /\ EL i insts = prod
End

(* Weakened: only non-pseudo users need producers before them.
   defs_before_uses is FALSE for DFT output blocks with PARAM(Var x)
   where x is defined by a non-pseudo instruction (PARAM(Var x) always
   errors at runtime, so this case is semantically irrelevant).
   non_pseudo_defs_before_uses suffices for all scheduling properties. *)
Definition np_defs_before_uses_def:
  np_defs_before_uses insts <=>
    !j var prod.
      j < LENGTH insts /\
      MEM (Var var) (EL j insts).inst_operands /\
      ~is_pseudo (EL j insts).inst_opcode /\
      producing_inst insts var = SOME prod ==>
      ?i. i < j /\ EL i insts = prod
End

Theorem defs_before_implies_np:
  !insts. defs_before_uses insts ==> np_defs_before_uses insts
Proof
  rw[defs_before_uses_def, np_defs_before_uses_def] >> metis_tac[]
QED

(* ===== Core property: every producing_inst result appears before user ===== *)

Definition output_producer_before_def:
  output_producer_before bi output <=>
    !k var prod.
      k < LENGTH output /\
      MEM (Var var) (EL k output).inst_operands /\
      producing_inst bi var = SOME prod /\
      ~is_pseudo prod.inst_opcode ==>
      ?m. m < k /\ (EL m output).inst_id = prod.inst_id
End

(* output_eda_before: eda deps appear earlier in output *)
Definition output_eda_before_def:
  output_eda_before eda output <=>
    !k d.
      k < LENGTH output /\
      MEM d (case FLOOKUP eda (EL k output).inst_id of
               NONE => [] | SOME ds => ds) /\
      ~is_pseudo d.inst_opcode ==>
      ?m. m < k /\ (EL m output).inst_id = d.inst_id
End

(* ===== EDA topo compatibility: all deps respect block order ===== *)

Definition eda_topo_compatible_def:
  eda_topo_compatible bi eda order <=>
    !inst dep.
      MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
      MEM dep (inst_all_deps bi order eda inst) /\
      ~is_pseudo dep.inst_opcode ==>
      ?i j. i < j /\ j < LENGTH bi /\ i < LENGTH bi /\
            EL i bi = dep /\ EL j bi = inst
End

(* ===== Stack emit ids (must be defined before stack_well_ordered) ===== *)

Definition stack_emit_ids_def:
  stack_emit_ids [] = [] /\
  stack_emit_ids (DfsEmit inst :: rest) = inst.inst_id :: stack_emit_ids rest /\
  stack_emit_ids (DfsProcess _ :: rest) = stack_emit_ids rest
End

Triviality stack_emit_ids_append[local]:
  !l1 l2. stack_emit_ids (l1 ++ l2) =
           stack_emit_ids l1 ++ stack_emit_ids l2
Proof
  Induct >> simp[stack_emit_ids_def] >>
  Cases >> simp[stack_emit_ids_def]
QED

Triviality stack_emit_ids_map_process[local]:
  !entries. stack_emit_ids (MAP DfsProcess entries) = []
Proof
  Induct >> simp[stack_emit_ids_def]
QED

(* ===== Stack well-ordered: key invariant ===== *)

(* Strengthened: DfsEmit entries' data deps must be in resolved AND
   not in stack_emit_ids of the rest (entries below).
   DfsProcess entries' data deps must not be in stack_emit_ids of rest. *)

Definition stack_well_ordered_def:
  stack_well_ordered [] resolved bi order eda = T /\
  stack_well_ordered (DfsProcess inst :: rest) resolved bi order eda =
    ((!dep. ~is_pseudo inst.inst_opcode /\
            MEM dep (inst_all_deps bi order eda inst) /\
            ~is_pseudo dep.inst_opcode ==>
            ~MEM dep.inst_id (stack_emit_ids rest)) /\
     stack_well_ordered rest (inst.inst_id :: resolved) bi order eda) /\
  stack_well_ordered (DfsEmit inst :: rest) resolved bi order eda =
    ((!dep. MEM dep (inst_all_deps bi order eda inst) /\
            ~is_pseudo dep.inst_opcode ==>
            MEM dep.inst_id resolved /\
            ~MEM dep.inst_id (stack_emit_ids rest)) /\
     stack_well_ordered rest (inst.inst_id :: resolved) bi order eda)
End

(* ===== stack_well_ordered helpers ===== *)

Triviality stack_well_ordered_mono[local]:
  !stk res1 blk ord eda res2.
    stack_well_ordered stk res1 blk ord eda /\
    (!x. MEM x res1 ==> MEM x res2) ==>
    stack_well_ordered stk res2 blk ord eda
Proof
  Induct_on `stk` >> rw[stack_well_ordered_def] >>
  Cases_on `h` >> gvs[stack_well_ordered_def] >>
  first_x_assum irule >>
  qexists_tac `i.inst_id :: res1` >> rw[] >> metis_tac[]
QED

Triviality stack_well_ordered_cong[local]:
  !stk res1 blk ord eda res2.
    stack_well_ordered stk res1 blk ord eda /\
    (!x. MEM x res1 <=> MEM x res2) ==>
    stack_well_ordered stk res2 blk ord eda
Proof
  rpt strip_tac >> irule stack_well_ordered_mono >>
  qexists_tac `res1` >> metis_tac[]
QED

Triviality ALL_DISTINCT_MAP_INJ_IMP[local]:
  !l (f:'a -> 'b) x y.
    ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ (f x = f y) ==> (x = y)
Proof
  rpt strip_tac >> gvs[MEM_EL] >>
  `EL n (MAP f l) = EL n' (MAP f l)` by simp[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
  gvs[]
QED

(* ===== Flip operands preserves data deps ===== *)

Triviality flip_operands_mem_ops[local]:
  !inst op. MEM op (flip_operands inst).inst_operands ==>
            MEM op inst.inst_operands
Proof
  rw[flip_operands_def] >>
  BasicProvers.every_case_tac >> gvs[LET_THM]
QED

Triviality flip_not_terminator[local]:
  !inst. is_terminator (flip_operands inst).inst_opcode =
         is_terminator inst.inst_opcode
Proof
  gen_tac >> rw[flip_operands_def] >>
  BasicProvers.every_case_tac >> simp[LET_THM] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def, is_terminator_def]
QED

Triviality map_the_filter_some_mono[local]:
  !l1 l2 f.
    (!x. MEM x l1 ==> MEM x l2) ==>
    !dep. MEM dep (MAP THE (FILTER IS_SOME (MAP f l1))) ==>
          MEM dep (MAP THE (FILTER IS_SOME (MAP f l2)))
Proof
  Induct_on `l1` >> simp[] >> rpt strip_tac >>
  Cases_on `f h` >> gvs[] >>
  simp[MEM_MAP, MEM_FILTER] >>
  qexists_tac `SOME dep` >> simp[] >>
  qexists_tac `h` >> simp[]
QED

Triviality flip_operands_data_deps_subset[local]:
  !bi order inst dep.
    MEM dep (inst_data_deps bi order (flip_operands inst)) ==>
    MEM dep (inst_data_deps bi order inst)
Proof
  rw[inst_data_deps_def, LET_THM, MEM_nub, MEM_APPEND,
     flip_not_terminator]
  >- (disj1_tac >> irule map_the_filter_some_mono >>
      qexists_tac `(flip_operands inst).inst_operands` >>
      simp[flip_operands_mem_ops])
  >- simp[]
  >- (irule map_the_filter_some_mono >>
      qexists_tac `(flip_operands inst).inst_operands` >>
      simp[flip_operands_mem_ops])
QED

Triviality data_deps_subset_all_deps[local]:
  !bi order eda inst dep.
    MEM dep (inst_data_deps bi order inst) ==>
    MEM dep (inst_all_deps bi order eda inst)
Proof
  rw[inst_all_deps_def, LET_THM, MEM_nub, MEM_APPEND]
QED

(* Combined: data_deps of flip_operands ⊆ inst_all_deps of original *)
Triviality flip_data_deps_in_all_deps[local]:
  !bi order eda inst dep.
    MEM dep (inst_data_deps bi order (flip_operands inst)) ==>
    MEM dep (inst_all_deps bi order eda inst)
Proof
  metis_tac[flip_operands_data_deps_subset, data_deps_subset_all_deps]
QED

(* Unified: data_deps of (if cond then flip inst else inst) ⊆ all_deps.
   Eliminates the repeated mp_tac+simp[Abbr]+IF_CASES_TAC pattern in C1/C9. *)
Triviality maybe_flip_data_deps_in_all_deps[local]:
  !bi order eda inst dep cond.
    MEM dep (inst_data_deps bi order
      (if cond then flip_operands inst else inst)) ==>
    MEM dep (inst_all_deps bi order eda inst)
Proof
  rpt strip_tac >> Cases_on `cond` >> gvs[] >>
  metis_tac[flip_data_deps_in_all_deps, data_deps_subset_all_deps]
QED

(* Unified: all_deps of (if cond then flip inst else inst) ⊆ all_deps of inst.
   flip_operands doesn't change inst_id → eda deps identical.
   flip_operands data deps ⊆ original data deps. *)
Triviality maybe_flip_all_deps_in_all_deps[local]:
  !bi order eda inst dep cond.
    MEM dep (inst_all_deps bi order eda
      (if cond then flip_operands inst else inst)) ==>
    MEM dep (inst_all_deps bi order eda inst)
Proof
  rpt strip_tac >> Cases_on `cond` >> gvs[] >>
  gvs[inst_all_deps_def, LET_THM, MEM_nub, MEM_APPEND] >>
  metis_tac[flip_operands_data_deps_subset, MEM_nub, flip_operands_inst_id]
QED

Triviality producing_inst_in_data_deps[local]:
  !bi order inst var prod.
    producing_inst bi var = SOME prod /\
    MEM (Var var) inst.inst_operands ==>
    MEM prod (inst_data_deps bi order inst)
Proof
  rw[inst_data_deps_def, LET_THM, MEM_nub, MEM_APPEND, MEM_MAP,
     MEM_FILTER] >>
  TRY disj1_tac >> qexists_tac `SOME prod` >> simp[] >>
  qexists_tac `Var var` >> simp[operand_producer_def]
QED

(* Combined: producing_inst result is in inst_all_deps *)
Triviality producing_inst_in_all_deps[local]:
  !bi order eda inst var prod.
    producing_inst bi var = SOME prod /\
    MEM (Var var) inst.inst_operands ==>
    MEM prod (inst_all_deps bi order eda inst)
Proof
  metis_tac[producing_inst_in_data_deps, data_deps_subset_all_deps]
QED

(* EDA deps are in inst_all_deps *)
Triviality eda_dep_in_all_deps[local]:
  !bi order eda inst d.
    MEM d (case FLOOKUP eda inst.inst_id of NONE => [] | SOME ds => ds) ==>
    MEM d (inst_all_deps bi order eda inst)
Proof
  rw[inst_all_deps_def, LET_THM, MEM_nub, MEM_APPEND]
QED

(* ===== producing_inst position lemma ===== *)

Triviality producing_inst_position[local]:
  !bi var prod.
    producing_inst bi var = SOME prod ==>
    ?r. r < LENGTH bi /\ EL r bi = prod
Proof
  Induct >> rw[producing_inst_def] >>
  Cases_on `MEM var h.inst_outputs` >> gvs[]
  >- (qexists_tac `0` >> simp[])
  >- (res_tac >> qexists_tac `SUC r` >> simp[])
QED

(* producing_inst gives a position strictly before the user position
   when np_defs_before_uses holds and the user is non-pseudo *)
Triviality producing_inst_before_user[local]:
  !bi var prod j.
    np_defs_before_uses bi /\
    j < LENGTH bi /\
    MEM (Var var) (EL j bi).inst_operands /\
    ~is_pseudo (EL j bi).inst_opcode /\
    producing_inst bi var = SOME prod ==>
    ?r. r < j /\ EL r bi = prod
Proof
  rw[np_defs_before_uses_def] >>
  first_x_assum (qspecl_then [`j`, `var`, `prod`] mp_tac) >>
  simp[]
QED

Triviality producing_inst_mem[local]:
  !bi var prod. producing_inst bi var = SOME prod ==> MEM prod bi
Proof
  rpt strip_tac >> drule producing_inst_position >> strip_tac >>
  metis_tac[MEM_EL]
QED

(* General: strictly earlier position in ALL_DISTINCT list → different inst_id *)
Triviality distinct_pos_neq_id[local]:
  !bi i j.
    ALL_DISTINCT (MAP (\k. k.inst_id) bi) /\
    i < j /\ j < LENGTH bi ==>
    (EL i bi).inst_id <> (EL j bi).inst_id
Proof
  spose_not_then strip_assume_tac >>
  `i < LENGTH (MAP (\k. k.inst_id) bi) /\
   j < LENGTH (MAP (\k. k.inst_id) bi)` by simp[] >>
  `EL i (MAP (\k. k.inst_id) bi) = EL j (MAP (\k. k.inst_id) bi)` by
    simp[EL_MAP] >>
  `i = j` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

Triviality producing_inst_id_neq_user[local]:
  !bi var prod j.
    np_defs_before_uses bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    j < LENGTH bi /\
    MEM (Var var) (EL j bi).inst_operands /\
    ~is_pseudo (EL j bi).inst_opcode /\
    producing_inst bi var = SOME prod ==>
    prod.inst_id <> (EL j bi).inst_id
Proof
  rpt strip_tac >>
  drule_all producing_inst_before_user >> strip_tac >>
  `prod.inst_id = (EL r bi).inst_id` by gvs[] >>
  metis_tac[distinct_pos_neq_id]
QED

(* flip_operands preserves inst_id *)
Triviality flip_operands_inst_id[local]:
  !inst. (flip_operands inst).inst_id = inst.inst_id
Proof
  rw[flip_operands_def] >> BasicProvers.every_case_tac >> simp[LET_THM]
QED

Triviality from_block_inst_id[local]:
  !bi inst. from_block bi inst ==>
    ?orig. MEM orig bi /\ inst.inst_id = orig.inst_id
Proof
  simp[from_block_def] >> metis_tac[flip_operands_inst_id]
QED

Triviality from_block_mem_operands[local]:
  !bi inst var. from_block bi inst /\ MEM (Var var) inst.inst_operands ==>
    ?orig. MEM orig bi /\ MEM (Var var) orig.inst_operands /\
           inst.inst_id = orig.inst_id
Proof
  simp[from_block_def] >> metis_tac[flip_operands_inst_id, flip_operands_mem_ops]
QED

(* ===== Block position ordering for stack ===== *)

(* For each non-pseudo DfsProcess/DfsEmit entry on the stack,
   all stack_emit_ids below it have block positions >= this entry's position.
   DfsProcess entries that are pseudo contribute no ordering constraint
   (they are skipped/expanded and don't appear as emit entries). *)
Definition stack_pos_ordered_def:
  stack_pos_ordered bi [] = T /\
  stack_pos_ordered bi (DfsProcess inst :: rest) =
    ((!x xi yi.
        ~is_pseudo inst.inst_opcode ==>
        MEM x (stack_emit_ids rest) /\
        xi < LENGTH bi /\ (EL xi bi).inst_id = x /\
        yi < LENGTH bi /\ (EL yi bi).inst_id = inst.inst_id ==>
        yi <= xi) /\
     stack_pos_ordered bi rest) /\
  stack_pos_ordered bi (DfsEmit inst :: rest) =
    ((!x xi yi.
        MEM x (stack_emit_ids rest) /\
        xi < LENGTH bi /\ (EL xi bi).inst_id = x /\
        yi < LENGTH bi /\ (EL yi bi).inst_id = inst.inst_id ==>
        yi <= xi) /\
     stack_pos_ordered bi rest)
End

Triviality stack_pos_ordered_append[local]:
  !l1 l2 bi.
    stack_pos_ordered bi (l1 ++ l2) ==>
    stack_pos_ordered bi l2
Proof
  Induct >> simp[] >>
  Cases >> simp[stack_pos_ordered_def]
QED

Triviality stack_pos_ordered_map_process[local]:
  !entries bi. stack_pos_ordered bi (MAP DfsProcess entries)
Proof
  Induct >> simp[stack_pos_ordered_def, stack_emit_ids_map_process]
QED

(* Key derived lemma: if all stack_emit_ids have positions >= inst_pos,
   and dep has position dep_pos < inst_pos, then dep not in stack_emit_ids *)
Triviality pos_ordered_not_in_emit[local]:
  !bi stack inst_id dep_id.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    (!x xi yi.
       MEM x (stack_emit_ids stack) /\
       xi < LENGTH bi /\ (EL xi bi).inst_id = x /\
       yi < LENGTH bi /\ (EL yi bi).inst_id = inst_id ==>
       yi <= xi) /\
    (?dep_pos inst_pos.
       dep_pos < inst_pos /\
       inst_pos < LENGTH bi /\ dep_pos < LENGTH bi /\
       (EL inst_pos bi).inst_id = inst_id /\
       (EL dep_pos bi).inst_id = dep_id) ==>
    ~MEM dep_id (stack_emit_ids stack)
Proof
  spose_not_then strip_assume_tac >>
  `?xi. xi < LENGTH bi /\ (EL xi bi).inst_id = dep_id` by metis_tac[] >>
  `inst_pos <= xi` by metis_tac[] >>
  (* xi must equal dep_pos by ALL_DISTINCT *)
  `EL xi (MAP (\i. i.inst_id) bi) = EL dep_pos (MAP (\i. i.inst_id) bi)` by
    simp[EL_MAP] >>
  `xi < LENGTH (MAP (\i. i.inst_id) bi) /\
   dep_pos < LENGTH (MAP (\i. i.inst_id) bi)` by simp[] >>
  `xi = dep_pos` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  (* inst_pos <= dep_pos but dep_pos < inst_pos — contradiction *)
  gvs[]
QED

(* ===== DFS topo invariant ===== *)

Definition dfs_topo_inv_def:
  dfs_topo_inv bi order eda state <=>
    output_producer_before bi state.ds_output /\
    output_eda_before eda state.ds_output /\
    stack_well_ordered state.ds_stack
      (MAP (\i. i.inst_id) state.ds_output ++ state.ds_visited) bi order eda /\
    (* output deps' ids not pending in stack *)
    (!i var prod.
      MEM i state.ds_output /\
      MEM (Var var) i.inst_operands /\
      producing_inst bi var = SOME prod /\
      ~is_pseudo prod.inst_opcode ==>
      ~MEM prod.inst_id (stack_emit_ids state.ds_stack)) /\
    (* output eda deps' ids not pending in stack *)
    (!i d.
      MEM i state.ds_output /\
      MEM d (case FLOOKUP eda i.inst_id of NONE => [] | SOME ds => ds) /\
      ~is_pseudo d.inst_opcode ==>
      ~MEM d.inst_id (stack_emit_ids state.ds_stack)) /\
    ALL_DISTINCT (stack_emit_ids state.ds_stack) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) state.ds_output) /\
    (!x. MEM x (stack_emit_ids state.ds_stack) ==>
         MEM x state.ds_visited) /\
    (!x. MEM x (MAP (\i. i.inst_id) state.ds_output) ==>
         ~MEM x (stack_emit_ids state.ds_stack)) /\
    (!x. MEM x (MAP (\i. i.inst_id) state.ds_output) ==>
         MEM x state.ds_visited) /\
    (* output elements' producers are visited *)
    (!i var prod.
      MEM i state.ds_output /\
      MEM (Var var) i.inst_operands /\
      producing_inst bi var = SOME prod /\
      ~is_pseudo prod.inst_opcode ==>
      MEM prod.inst_id state.ds_visited) /\
    (* output elements' eda deps are visited *)
    (!i d.
      MEM i state.ds_output /\
      MEM d (case FLOOKUP eda i.inst_id of NONE => [] | SOME ds => ds) /\
      ~is_pseudo d.inst_opcode ==>
      MEM d.inst_id state.ds_visited) /\
    (* visited non-pseudo inst is in output or pending as DfsEmit *)
    (!inst. MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
            MEM inst.inst_id state.ds_visited /\
            ~MEM inst.inst_id (stack_emit_ids state.ds_stack) ==>
            MEM inst.inst_id (MAP (\i. i.inst_id) state.ds_output)) /\
    (* block position ordering of stack *)
    stack_pos_ordered bi state.ds_stack
End

(* ===== dfs_step preservation ===== *)

(* Visited already: stack shrinks, output + visited unchanged *)
Triviality topo_inv_drop_visited[local]:
  !bi order state inst t.
    dfs_topo_inv bi order eda state /\
    state.ds_stack = DfsProcess inst :: t /\
    MEM inst.inst_id state.ds_visited ==>
    dfs_topo_inv bi order eda (state with ds_stack := t)
Proof
  rpt strip_tac >>
  gvs[dfs_topo_inv_def, stack_well_ordered_def, stack_emit_ids_def,
      stack_pos_ordered_def] >>
  rpt conj_tac
  >- (irule stack_well_ordered_mono >>
      qexists_tac `inst.inst_id ::
        MAP (\i. i.inst_id) state.ds_output ++ state.ds_visited` >>
      simp[MEM_APPEND] >> metis_tac[])
  >> rpt strip_tac >> res_tac >> res_tac
QED

(* Pseudo: stack shrinks, pseudo id added to visited *)
Triviality topo_inv_drop_pseudo[local]:
  !bi order state inst t.
    dfs_topo_inv bi order eda state /\
    state.ds_stack = DfsProcess inst :: t /\
    is_pseudo inst.inst_opcode /\
    MEM inst bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    dfs_topo_inv bi order eda
      (state with <| ds_stack := t;
                     ds_visited := inst.inst_id :: state.ds_visited |>)
Proof
  rpt strip_tac >>
  fs[dfs_topo_inv_def, stack_well_ordered_def, stack_emit_ids_def,
     stack_pos_ordered_def] >>
  rpt conj_tac
  (* 1: stack_well_ordered — move inst.inst_id from prefix to resolved *)
  >- (irule stack_well_ordered_cong >>
      qexists_tac `inst.inst_id ::
        MAP (\i. i.inst_id) state.ds_output ++ state.ds_visited` >>
      simp[MEM_APPEND] >> metis_tac[])
  (* 2: output data deps not on stack — from assumption *)
  >- (rpt strip_tac >> res_tac)
  (* 3: output eda deps not on stack — from assumption *)
  >- (rpt strip_tac >> res_tac)
  (* 4: output data deps visited — disj2_tac (was already visited) *)
  >- (rpt strip_tac >> disj2_tac >> res_tac)
  (* 5: output eda deps visited — disj2_tac (was already visited) *)
  >- (rpt strip_tac >> disj2_tac >> res_tac)
  (* 6: visited non-pseudo in output — handle inst.inst_id = case *)
  >> rpt strip_tac >> gvs[] >>
  metis_tac[ALL_DISTINCT_MAP_INJ_IMP]
QED

(* DfsEmit: inst moves from stack head to output tail *)
Theorem topo_inv_emit[local]:
  !bi order state inst rest'.
    dfs_topo_inv bi order eda state /\
    dfs_good_state bi state /\
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    state.ds_stack = DfsEmit inst :: rest' ==>
    dfs_topo_inv bi order eda
      (state with <| ds_stack := rest';
                     ds_output := state.ds_output ++ [inst] |>)
Proof
  rpt strip_tac >>
  qpat_x_assum `dfs_topo_inv _ _ _ _` mp_tac >>
  simp[dfs_topo_inv_def, stack_well_ordered_def,
       stack_emit_ids_def, stack_pos_ordered_def] >>
  strip_tac >>
  `from_block bi inst /\ ~is_pseudo inst.inst_opcode` by
    (gvs[dfs_good_state_def, EVERY_MEM] >>
     first_x_assum (qspec_then `DfsEmit inst` mp_tac) >> simp[]) >>
  `?orig. MEM orig bi /\ inst.inst_id = orig.inst_id` by
    metis_tac[from_block_inst_id] >>
  rpt conj_tac
  (* 1: output_producer_before *)
  >- suspend "G1"
  (* 2: output_eda_before *)
  >- suspend "G1_eda"
  (* 3: stack_well_ordered *)
  >- (irule stack_well_ordered_cong >>
      qexists `inst.inst_id ::
        MAP (\i. i.inst_id) state.ds_output ++ state.ds_visited` >>
      simp[] >> rpt strip_tac >> gvs[MEM_APPEND] >> metis_tac[])
  (* 4: output data deps not pending *)
  >- suspend "G3"
  (* 5: output eda deps not pending *)
  >- suspend "G3_eda"
  (* 6: ALL_DISTINCT (stack_emit_ids) — from assumption, output unchanged *)
  (* 7: ALL_DISTINCT (MAP inst_id (output ++ [inst])) *)
  >- (simp[ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS] >>
      rpt strip_tac >> gvs[] >> res_tac >> gvs[])
  (* 8: stack_emit_ids ⊆ visited — from assumption *)
  (* 9: output++[inst] ids not in stack_emit_ids rest' *)
  >- (rpt strip_tac >> gvs[] >> res_tac >> gvs[])
  (* 10: output++[inst] ids are visited *)
  >- (rpt strip_tac >> gvs[] >> res_tac)
  (* 11: output data deps visited *)
  >- suspend "G6"
  (* 12: output eda deps visited *)
  >- suspend "G6_eda"
  (* 13: visited non-pseudo in output or is inst *)
  >> rpt strip_tac >>
     Cases_on `inst'.inst_id = inst.inst_id` >- simp[] >>
     disj1_tac >> res_tac
QED

(* G3: output++[inst] data deps not in stack_emit_ids rest' *)
Resume topo_inv_emit[G3]:
  rpt gen_tac >> strip_tac
  >- (res_tac >> gvs[])
  >> gvs[] >> metis_tac[producing_inst_in_all_deps]
QED

(* G3_eda: output++[inst] eda deps not in stack_emit_ids rest' *)
Resume topo_inv_emit[G3_eda]:
  rpt gen_tac >> strip_tac
  >- (res_tac >> gvs[])
  >> gvs[] >> metis_tac[eda_dep_in_all_deps]
QED

(* G6: output++[inst] data deps visited *)
Resume topo_inv_emit[G6]:
  rpt gen_tac >> strip_tac
  >- (res_tac >> gvs[])
  >> gvs[] >> metis_tac[producing_inst_in_all_deps]
QED

(* G6_eda: output++[inst] eda deps visited *)
Resume topo_inv_emit[G6_eda]:
  rpt gen_tac >> strip_tac
  >- (res_tac >> gvs[])
  >> gvs[] >> metis_tac[eda_dep_in_all_deps]
QED

(* G1: output_producer_before for output++[inst] *)
Resume topo_inv_emit[G1]:
  simp[output_producer_before_def] >>
  rpt strip_tac >>
  Cases_on `k < LENGTH state.ds_output`
  (* Case 1: k < LENGTH output — use old output_producer_before *)
  >- (gvs[output_producer_before_def, EL_APPEND1] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      qexists `m` >> simp[EL_APPEND1])
  (* Case 2: k = LENGTH output (the new inst) *)
  >> `k = LENGTH state.ds_output` by
       gvs[EL_APPEND2, LENGTH_APPEND] >>
     gvs[EL_APPEND2] >>
     `MEM prod bi` by metis_tac[producing_inst_mem] >>
     (* dep assumption → not on stack *)
     `~MEM prod.inst_id (stack_emit_ids rest')` by
       metis_tac[producing_inst_in_all_deps] >>
     (* dep assumption → visited (via output⊆visited) *)
     `MEM prod.inst_id state.ds_visited` by
       metis_tac[producing_inst_in_all_deps] >>
     (* prod.inst_id ≠ orig.inst_id *)
     `MEM (Var var) orig.inst_operands /\ ~is_pseudo orig.inst_opcode` by
       (qpat_x_assum `from_block _ _` mp_tac >>
        simp[from_block_def] >> strip_tac >>
        `j = orig` by metis_tac[ALL_DISTINCT_MAP_INJ_IMP,
                                 flip_operands_inst_id] >>
        gvs[] >> metis_tac[flip_operands_mem_ops]) >>
     `?j. j < LENGTH bi /\ EL j bi = orig` by metis_tac[MEM_EL] >>
     `prod.inst_id <> orig.inst_id` by
       (qspecl_then [`bi`,`var`,`prod`,`j`] mp_tac producing_inst_id_neq_user >>
        gvs[]) >>
     (* C7: visited + non-pseudo + not-on-stack → in output *)
     `MEM prod.inst_id (MAP (\i. i.inst_id) state.ds_output)` by
       (first_x_assum irule >> gvs[]) >>
     (* MEM in MAP → ∃ element in list with matching id *)
     pop_assum (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
     `?m. m < LENGTH state.ds_output /\ EL m state.ds_output = y` by
       metis_tac[MEM_EL] >>
     qexists `m` >> simp[EL_APPEND1]
QED

(* G1_eda: output_eda_before for output++[inst] *)
Resume topo_inv_emit[G1_eda]:
  simp[output_eda_before_def] >>
  rpt strip_tac >>
  Cases_on `k < LENGTH state.ds_output`
  (* Case 1: k < LENGTH output — use old output_eda_before *)
  >- (gvs[output_eda_before_def, EL_APPEND1] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      qexists `m` >> simp[EL_APPEND1])
  (* Case 2: k = LENGTH output (the new inst) — eda dep d in inst_all_deps *)
  >> `k = LENGTH state.ds_output` by
       gvs[EL_APPEND2, LENGTH_APPEND] >>
     gvs[EL_APPEND2] >>
     (* d is an eda dep of inst (via inst_id = orig.inst_id, so same FLOOKUP) *)
     `MEM d (inst_all_deps bi order eda inst)` by
       metis_tac[eda_dep_in_all_deps] >>
     (* From stack_well_ordered(DfsEmit): d resolved and not on stack *)
     `~MEM d.inst_id (stack_emit_ids rest')` by
       (qpat_assum `!dep. MEM dep (inst_all_deps _ _ _ _) /\ _ ==> _`
          (qspec_then `d` mp_tac) >> simp[]) >>
     `MEM d.inst_id state.ds_visited` by
       (qpat_x_assum `!dep. MEM dep (inst_all_deps _ _ _ _) /\ _ ==> _`
          (qspec_then `d` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
        res_tac) >>
     (* Use orig (which IS in bi) for eda_topo_compatible *)
     `~is_pseudo orig.inst_opcode` by
       (qpat_x_assum `from_block _ _` mp_tac >>
        simp[from_block_def] >> rpt strip_tac >> gvs[] >>
        metis_tac[ALL_DISTINCT_MAP_INJ_IMP, flip_operands_inst_id]) >>
     (* d ∈ inst_all_deps of orig (same inst_id → same eda FLOOKUP) *)
     `MEM d (inst_all_deps bi order eda orig)` by
       metis_tac[eda_dep_in_all_deps] >>
     `?di dj. di < dj /\ dj < LENGTH bi /\ di < LENGTH bi /\
              EL di bi = d /\ EL dj bi = orig` by
       (gvs[eda_topo_compatible_def] >>
        first_x_assum irule >> gvs[]) >>
     `d.inst_id <> orig.inst_id` by
       (`d.inst_id = (EL di bi).inst_id /\
         orig.inst_id = (EL dj bi).inst_id` by gvs[] >>
        metis_tac[distinct_pos_neq_id]) >>
     (* d.inst_id in output (not on stack, visited, non-pseudo) *)
     `MEM d.inst_id (MAP (\i. i.inst_id) state.ds_output)` by
       (`MEM d bi` by metis_tac[MEM_EL] >>
        first_x_assum irule >> gvs[]) >>
     pop_assum (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
     `?m. m < LENGTH state.ds_output /\ EL m state.ds_output = y` by
       metis_tac[MEM_EL] >>
     qexists `m` >> simp[EL_APPEND1]
QED

Finalise topo_inv_emit

Theorem dfs_step_preserves_topo:
  !bi order eda offspring_map do_flip state.
    dfs_topo_inv bi order eda state /\
    dfs_good_state bi state /\
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    dfs_topo_inv bi order eda
      (dfs_step bi order eda offspring_map do_flip state)
Proof
  rpt strip_tac >>
  Cases_on `state.ds_stack`
  (* Empty stack: no-op *)
  >- simp[dfs_step_def]
  >> Cases_on `h`
  (* DfsProcess *)
  >- (rename1 `DfsProcess inst :: rest'` >>
      Cases_on `MEM inst.inst_id state.ds_visited`
      (* Already visited: drop *)
      >- (simp[dfs_step_def] >>
          irule topo_inv_drop_visited >> simp[] >> metis_tac[])
      >> Cases_on `is_pseudo inst.inst_opcode`
      (* Pseudo: drop + mark visited *)
      >- (simp[dfs_step_def] >>
          irule topo_inv_drop_pseudo >> simp[] >>
          gvs[dfs_good_state_def, EVERY_MEM] >>
          first_x_assum (qspec_then `DfsProcess inst` mp_tac) >> simp[])
      (* New non-pseudo: push children + DfsEmit + rest *)
      >> simp[dfs_step_def, LET_THM] >>
         qabbrev_tac `children = inst_all_deps bi order eda inst` >>
         qabbrev_tac `sorted = sort_children bi order eda offspring_map
                                             inst children` >>
         qabbrev_tac `inst' = if do_flip /\ is_flippable inst.inst_opcode /\
                                 sorted <> children
                              then flip_operands inst else inst` >>
         simp[dfs_topo_inv_def] >>
         rpt conj_tac
         (* 1: output_producer_before — output unchanged *)
         >- suspend "C0"
         (* 2: output_eda_before — output unchanged *)
         >- gvs[dfs_topo_inv_def]
         (* 3: stack_well_ordered *)
         >- suspend "C1"
         (* 4: output data deps not on stack *)
         >- suspend "C2"
         (* 5: output eda deps not on stack — same as C2 pattern *)
         >- suspend "C2_eda"
         (* 6: ALL_DISTINCT stack_emit_ids *)
         >- suspend "C3"
         (* 7: ALL_DISTINCT output ids — output unchanged *)
         >- gvs[dfs_topo_inv_def]
         (* 8: stack_emit_ids ⊆ visited *)
         >- suspend "C4"
         (* 9: output ids not in stack *)
         >- suspend "C5"
         (* 10: output ids in visited *)
         >- suspend "C6"
         (* 11: output data deps visited *)
         >- suspend "C7"
         (* 12: output eda deps visited — same as C7 pattern *)
         >- suspend "C7_eda"
         (* 13: visited non-pseudo in output or pending *)
         >- suspend "C8"
         (* 14: stack_pos_ordered *)
         >> suspend "C9")
  (* DfsEmit: use helper *)
  >> (rename1 `DfsEmit inst :: rest'` >>
      simp[dfs_step_def] >>
      irule topo_inv_emit >> simp[])
QED

(* C0: output_producer_before unchanged (output is state.ds_output) *)
Resume dfs_step_preserves_topo[C0]:
  (* output is unchanged, so output_producer_before carries over *)
  gvs[dfs_topo_inv_def]
QED

(* Shared tactic for non-pseudo case Resume blocks:
   Establishes MEM inst bi and inst'.inst_id = inst.inst_id *)
val non_pseudo_setup_tac =
  `MEM inst bi` by
    (fs[dfs_good_state_def, EVERY_MEM] >>
     first_x_assum (qspec_then `DfsProcess inst` mp_tac) >> simp[]) >>
  `inst'.inst_id = inst.inst_id` by
    (simp[Abbr `inst'`] >> IF_CASES_TAC >> simp[flip_operands_inst_id]);

(* Shared emit-id simplification for C2-C5, C8 pattern *)
val emit_id_tac =
  simp[stack_emit_ids_append, stack_emit_ids_map_process,
       stack_emit_ids_def] >>
  `inst'.inst_id = inst.inst_id` by
    (unabbrev_all_tac >> rw[flip_operands_inst_id]) >>
  gvs[dfs_topo_inv_def, stack_emit_ids_def] >>
  metis_tac[];

(* Helper: SWO of DfsProcess prefix ++ suffix *)
Triviality swo_process_prefix[local]:
  !l suffix resolved bi order eda.
    (!si dep. MEM si l /\ ~is_pseudo si.inst_opcode /\
              MEM dep (inst_all_deps bi order eda si) /\
              ~is_pseudo dep.inst_opcode ==>
              ~MEM dep.inst_id (stack_emit_ids suffix)) /\
    stack_well_ordered suffix
      (REVERSE (MAP (\i. i.inst_id) l) ++ resolved) bi order eda ==>
    stack_well_ordered (MAP DfsProcess l ++ suffix) resolved bi order eda
Proof
  Induct >> simp[stack_well_ordered_def, REVERSE_DEF] >>
  rpt strip_tac
  >- (gvs[stack_emit_ids_append, stack_emit_ids_map_process] >>
      first_x_assum (qspecl_then [`h`, `dep`] mp_tac) >> simp[])
  >> last_x_assum irule >> conj_tac
  >- metis_tac[]
  >> first_x_assum mp_tac >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

(* Helper: var-operand dep has position strictly before non-pseudo user. *)
Triviality var_dep_earlier_pos[local]:
  !bi j var prod.
    np_defs_before_uses bi /\
    j < LENGTH bi /\ MEM (Var var) (EL j bi).inst_operands /\
    ~is_pseudo (EL j bi).inst_opcode /\
    producing_inst bi var = SOME prod ==>
    ?dep_pos. dep_pos < j /\ dep_pos < LENGTH bi /\ EL dep_pos bi = prod
Proof
  rw[np_defs_before_uses_def] >>
  first_x_assum (qspecl_then [`j`, `var`, `prod`] mp_tac) >>
  simp[] >> strip_tac >> qexists `i` >> simp[]
QED

(* Helper: position uniqueness from ALL_DISTINCT inst_ids *)
Triviality pos_unique[local]:
  !bi p q.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    p < LENGTH bi /\ q < LENGTH bi /\
    (EL p bi).inst_id = (EL q bi).inst_id ==>
    p = q
Proof
  rpt strip_tac >>
  `p < LENGTH (MAP (\i. i.inst_id) bi)` by simp[] >>
  `q < LENGTH (MAP (\i. i.inst_id) bi)` by simp[] >>
  `EL p (MAP (\i. i.inst_id) bi) = EL q (MAP (\i. i.inst_id) bi)` by
    simp[EL_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Helper: dep of a non-pseudo child of inst has position strictly before inst.
   Uses eda_topo_compatible to get ordering for non-pseudo deps. *)
Triviality dep_of_child_earlier_pos[local]:
  !bi order eda inst si dep.
    np_defs_before_uses bi /\
    eda_topo_compatible bi eda order /\
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    MEM si (inst_all_deps bi order eda inst) /\
    ~is_pseudo si.inst_opcode /\
    MEM dep (inst_all_deps bi order eda si) /\
    ~is_pseudo dep.inst_opcode ==>
    ?dep_pos inst_pos.
      dep_pos < inst_pos /\ inst_pos < LENGTH bi /\ dep_pos < LENGTH bi /\
      EL dep_pos bi = dep /\ EL inst_pos bi = inst
Proof
  rpt strip_tac >>
  `MEM si bi` by metis_tac[inst_all_deps_mem] >>
  `MEM dep bi` by metis_tac[inst_all_deps_mem] >>
  `?inst_j. inst_j < LENGTH bi /\ EL inst_j bi = inst` by
    metis_tac[MEM_EL] >>
  (* Get ordering from eda_topo_compatible for (inst, si) *)
  `?si_j inst_j'.
     si_j < inst_j' /\ inst_j' < LENGTH bi /\ si_j < LENGTH bi /\
     EL si_j bi = si /\ EL inst_j' bi = inst` by
    (fs[eda_topo_compatible_def] >>
     first_x_assum (qspecl_then [`inst`, `si`] mp_tac) >> simp[]) >>
  `inst_j' = inst_j` by metis_tac[pos_unique] >> gvs[] >>
  (* Get ordering from eda_topo_compatible for (si, dep) *)
  `?dep_j si_j'.
     dep_j < si_j' /\ si_j' < LENGTH bi /\ dep_j < LENGTH bi /\
     EL dep_j bi = dep /\ EL si_j' bi = EL si_j bi` by
    (fs[eda_topo_compatible_def] >>
     first_x_assum (qspecl_then [`EL si_j bi`, `dep`] mp_tac) >> simp[]) >>
  `si_j < LENGTH bi` by simp[] >>
  `(EL si_j' bi).inst_id = (EL si_j bi).inst_id` by gvs[] >>
  `si_j' = si_j` by metis_tac[pos_unique] >>
  gvs[] >>
  qexistsl [`dep_j`, `inst_j`] >> simp[]
QED

(* Core helper: dep of a non-pseudo child of inst can't be inst.inst_id
   and can't be in emit_ids of the rest of the stack below inst. *)
Triviality dep_not_in_suffix[local]:
  !bi order eda inst si dep rest'.
    np_defs_before_uses bi /\
    eda_topo_compatible bi eda order /\
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode /\
    MEM si (inst_all_deps bi order eda inst) /\
    ~is_pseudo si.inst_opcode /\
    MEM dep (inst_all_deps bi order eda si) /\
    ~is_pseudo dep.inst_opcode /\
    stack_pos_ordered bi (DfsProcess inst :: rest') ==>
    dep.inst_id <> inst.inst_id /\
    ~MEM dep.inst_id (stack_emit_ids rest')
Proof
  rpt strip_tac
  (* dep.inst_id ≠ inst.inst_id: get positions, derive equality contradiction *)
  >- (drule_all dep_of_child_earlier_pos >> strip_tac >>
      `(EL dep_pos bi).inst_id = (EL inst_pos bi).inst_id` by gvs[] >>
      `dep_pos = inst_pos` by metis_tac[pos_unique] >>
      gvs[])
  (* ¬MEM dep.inst_id (stack_emit_ids rest') — contradicts assumption *)
  >> (drule_all dep_of_child_earlier_pos >> strip_tac >>
      gvs[stack_pos_ordered_def] >>
      first_x_assum (qspecl_then [`dep_pos`, `inst_pos`] mp_tac) >>
      simp[])
QED

(* C1: stack_well_ordered for new stack *)
Resume dfs_step_preserves_topo[C1]:
  non_pseudo_setup_tac >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule swo_process_prefix >> conj_tac
  (* Part a: sorted children's data deps not in emit_ids of suffix *)
  >- (simp[Abbr `sorted`, Abbr `children`,
           stack_emit_ids_append, stack_emit_ids_def] >>
      rpt strip_tac >>
      (`MEM si (inst_all_deps bi order eda inst)` by
         metis_tac[sort_children_mem] >>
       gvs[dfs_topo_inv_def] >> metis_tac[dep_not_in_suffix]))
  (* Part b: [DfsEmit inst'] ++ rest' is well-ordered *)
  >> (simp[stack_well_ordered_def] >> conj_tac
      >- (rpt gen_tac >> strip_tac >> suspend "C1_deps")
      >> suspend "C1_rest")
QED



(* C1_deps: inst' data deps are resolved and not in rest' emit_ids *)
Resume dfs_step_preserves_topo[C1_deps]:
  (* Goal: MEM dep.inst_id resolved ∧ ¬MEM dep.inst_id (stack_emit_ids rest')
     where dep ∈ inst_all_deps of inst' *)
  fs[Abbr `inst'`] >>
  `MEM dep (inst_all_deps bi order eda inst)` by
    metis_tac[maybe_flip_all_deps_in_all_deps] >>
  conj_tac
  (* MEM dep.inst_id in resolved — via sorted children *)
  >- (simp[MEM_MAP] >> disj1_tac >> disj1_tac >>
      qexists `dep` >> simp[Abbr `children`] >>
      metis_tac[sort_children_mem])
  (* ¬MEM dep.inst_id (stack_emit_ids rest') *)
  >> (gvs[dfs_topo_inv_def] >>
      irule pos_ordered_not_in_emit >>
      qexistsl [`bi`, `inst.inst_id`] >> simp[] >> conj_tac
      >- gvs[stack_pos_ordered_def]
      >> (gvs[eda_topo_compatible_def] >>
          first_x_assum (qspecl_then [`inst`, `dep`] mp_tac) >>
          simp[] >> strip_tac >>
          qexistsl [`i`, `j`] >> simp[]))
QED

(* C1_rest: rest' well-ordered with larger resolved set *)
Resume dfs_step_preserves_topo[C1_rest]:
  fs[dfs_topo_inv_def] >>
  qpat_x_assum `stack_well_ordered (DfsProcess inst :: rest') _ _ _ _` mp_tac >>
  simp[stack_well_ordered_def] >> strip_tac >>
  irule stack_well_ordered_mono >>
  qexists `inst.inst_id ::
           (MAP (\i. i.inst_id) state.ds_output ++ state.ds_visited)` >>
  simp[MEM_APPEND, MEM_REVERSE] >> metis_tac[MEM]
QED

(* C2-C5, C8 all follow the emit-id simplification pattern *)
Resume dfs_step_preserves_topo[C2]:
  emit_id_tac
QED
Resume dfs_step_preserves_topo[C2_eda]:
  emit_id_tac
QED
Resume dfs_step_preserves_topo[C3]:
  emit_id_tac
QED
Resume dfs_step_preserves_topo[C4]:
  emit_id_tac
QED
Resume dfs_step_preserves_topo[C5]:
  emit_id_tac
QED
Resume dfs_step_preserves_topo[C6]:
  gvs[dfs_topo_inv_def]
QED
Resume dfs_step_preserves_topo[C7]:
  gvs[dfs_topo_inv_def] >> metis_tac[]
QED
Resume dfs_step_preserves_topo[C7_eda]:
  gvs[dfs_topo_inv_def] >> metis_tac[]
QED
Resume dfs_step_preserves_topo[C8]:
  emit_id_tac
QED

(* Helper: stack_pos_ordered for MAP DfsProcess l ++ suffix
   when suffix is pos_ordered and each l item's position ≤ all emit positions in suffix *)
Triviality spo_map_process_suffix[local]:
  !l suffix bi.
    stack_pos_ordered bi suffix /\
    (!si x xi yi.
       MEM si l /\ ~is_pseudo si.inst_opcode /\
       MEM x (stack_emit_ids suffix) /\
       xi < LENGTH bi /\ (EL xi bi).inst_id = x /\
       yi < LENGTH bi /\ (EL yi bi).inst_id = si.inst_id ==>
       yi <= xi) ==>
    stack_pos_ordered bi (MAP DfsProcess l ++ suffix)
Proof
  Induct >> simp[stack_pos_ordered_def, stack_emit_ids_map_process] >>
  rpt strip_tac
  >- (gvs[stack_emit_ids_append, stack_emit_ids_map_process] >>
      first_x_assum (qspecl_then [`h`, `(EL xi bi).inst_id`,
                                  `xi`, `yi`] mp_tac) >>
      simp[])
  >> first_x_assum irule >> simp[] >> metis_tac[]
QED

(* Helper: sorted child is a dep of inst → has earlier block position *)
Triviality sorted_child_earlier_pos[local]:
  !bi order eda offspring_map inst si.
    MEM si (sort_children bi order eda offspring_map inst
              (inst_all_deps bi order eda inst)) /\
    ~is_pseudo si.inst_opcode /\
    eda_topo_compatible bi eda order /\
    MEM inst bi /\ ~is_pseudo inst.inst_opcode ==>
    ?si_pos inst_pos.
      si_pos < inst_pos /\ inst_pos < LENGTH bi /\ si_pos < LENGTH bi /\
      EL si_pos bi = si /\ EL inst_pos bi = inst
Proof
  rpt strip_tac >>
  `MEM si (inst_all_deps bi order eda inst)` by metis_tac[sort_children_mem] >>
  gvs[eda_topo_compatible_def]
QED

(* C9: stack_pos_ordered *)
Resume dfs_step_preserves_topo[C9]:
  non_pseudo_setup_tac >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule spo_map_process_suffix >>
  simp[stack_pos_ordered_def, stack_emit_ids_def] >>
  gvs[dfs_topo_inv_def, stack_pos_ordered_def] >>
  simp[Abbr `sorted`, Abbr `children`] >>
  rpt strip_tac
  (* sorted child si vs inst.inst_id *)
  >- (drule_all sorted_child_earlier_pos >> strip_tac >>
      `yi = si_pos` by metis_tac[pos_unique] >>
      `xi = inst_pos` by metis_tac[pos_unique] >>
      simp[])
  (* sorted child si vs emit_ids in rest' *)
  >> (drule_all sorted_child_earlier_pos >> strip_tac >>
      `yi = si_pos` by metis_tac[pos_unique] >>
      `inst_pos <= xi` by metis_tac[] >>
      simp[])
QED

Finalise dfs_step_preserves_topo

(* ===== FUNPOW lifting ===== *)

Triviality dfs_topo_funpow[local]:
  !n bi order eda offspring_map do_flip state.
    dfs_topo_inv bi order eda state /\
    dfs_good_state bi state /\
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    dfs_topo_inv bi order eda
      (FUNPOW (dfs_step bi order eda offspring_map do_flip) n state)
Proof
  Induct >> simp[FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >>
  simp[dfs_step_preserves_topo, dfs_step_preserves_good]
QED

Triviality swo_map_process[local]:
  !entries resolved bi order.
    stack_well_ordered (MAP DfsProcess entries) resolved bi order eda
Proof
  Induct >> simp[stack_well_ordered_def, stack_emit_ids_map_process]
QED

Triviality init_topo_inv[local]:
  !entries bi order eda.
    dfs_topo_inv bi order eda
      <| ds_stack := MAP DfsProcess entries;
         ds_output := []; ds_visited := [] |>
Proof
  rw[dfs_topo_inv_def, output_producer_before_def, output_eda_before_def,
     stack_emit_ids_map_process, swo_map_process,
     stack_pos_ordered_map_process]
QED

(* ===== Main results ===== *)

(* The full invariant holds at schedule_from_entries output *)
Triviality schedule_topo_inv[local]:
  !bi order eda offspring_map entries.
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    EVERY (\i. MEM i bi) entries ==>
    dfs_topo_inv bi order eda
      (FUNPOW (dfs_step bi order eda offspring_map T)
         ((LENGTH bi + 1) * (LENGTH bi + 1))
         <| ds_stack := MAP DfsProcess entries;
            ds_output := []; ds_visited := [] |>)
Proof
  rpt strip_tac >>
  irule dfs_topo_funpow >>
  simp[init_topo_inv, init_dfs_state_good]
QED

(* Every non-pseudo producing instruction appears before its user in
   the DFS schedule output. *)
Theorem schedule_output_producer_before:
  !bi order eda offspring_map entries.
    eda_wf eda bi ==>
    eda_topo_compatible bi eda order ==>
    np_defs_before_uses bi ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    bi <> [] ==>
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    EVERY (\i. MEM i bi) entries ==>
    output_producer_before bi
      (schedule_from_entries bi order eda offspring_map entries)
Proof
  rw[schedule_from_entries_def, LET_THM] >>
  drule_all schedule_topo_inv >> simp[dfs_topo_inv_def]
QED

(* Every non-pseudo EDA dependency appears before its dependent
   instruction in the DFS schedule output. *)
Theorem schedule_output_eda_before:
  !bi order eda offspring_map entries.
    eda_wf eda bi ==>
    eda_topo_compatible bi eda order ==>
    np_defs_before_uses bi ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    bi <> [] ==>
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    EVERY (\i. MEM i bi) entries ==>
    output_eda_before eda
      (schedule_from_entries bi order eda offspring_map entries)
Proof
  rw[schedule_from_entries_def, LET_THM] >>
  drule_all schedule_topo_inv >> simp[dfs_topo_inv_def]
QED

(* The DFS schedule output has no duplicate instruction IDs. *)
Theorem schedule_output_all_distinct:
  !bi order eda offspring_map entries.
    eda_wf eda bi ==>
    eda_topo_compatible bi eda order ==>
    np_defs_before_uses bi ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    bi <> [] ==>
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    EVERY (\i. MEM i bi) entries ==>
    ALL_DISTINCT (MAP (\i. i.inst_id)
      (schedule_from_entries bi order eda offspring_map entries))
Proof
  rw[schedule_from_entries_def, LET_THM] >>
  drule_all schedule_topo_inv >> simp[dfs_topo_inv_def]
QED


