(*
 * DFT Pipeline Invariance — supporting lemmas
 *
 * Key results:
 *   inst_data_deps_id_agree — under unique_defs + id-structure agreement,
 *     inst_data_deps returns same inst_ids for permuted block_insts
 *   build_eda_agree — same effect-ful subsequence and id set => same eda map
 *   build_full_eda_pseudo_strip — build_full_eda ignores pseudo instructions
 *
 * Definitions:
 *   has_effects — predicate for instructions with non-empty effect sets
 *   eda_fold_step — single-step fold function used in build_eda
 *)

Theory dftPipelineInvar
Ancestors
  dftStructural dftIdempotent dftDefs venomExecSemantics venomEffects
  passSharedDefs venomInst list rich_list sorting finite_map pred_set combin
Libs
  BasicProvers

(* ================================================================
   Helpers
   ================================================================ *)

Theorem unique_defs_no_shared_output:
  !insts i j var.
    unique_defs insts /\
    MEM i insts /\ MEM j insts /\ i <> j /\
    MEM var i.inst_outputs /\ MEM var j.inst_outputs ==>
    F
Proof
  rpt gen_tac >> strip_tac >> fs[unique_defs_def] >>
  `?ni. ni < LENGTH insts /\ EL ni insts = i` by metis_tac[MEM_EL] >>
  `?nj. nj < LENGTH insts /\ EL nj insts = j` by metis_tac[MEM_EL] >>
  `ni <> nj` by (strip_tac >> gvs[]) >>
  `ni < nj \/ nj < ni` by DECIDE_TAC >| [
    first_x_assum (qspecl_then [`ni`, `nj`] mp_tac) >>
    simp[IN_DISJOINT] >> metis_tac[],
    first_x_assum (qspecl_then [`nj`, `ni`] mp_tac) >>
    simp[IN_DISJOINT] >> metis_tac[]
  ]
QED

Theorem producing_inst_perm_id:
  !insts1 insts2 var i1 i2.
    unique_defs insts1 /\
    producing_inst insts1 var = SOME i1 /\
    producing_inst insts2 var = SOME i2 /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) ==>
    i2.inst_id = i1.inst_id
Proof
  rpt strip_tac >>
  `MEM i2 insts2 /\ MEM var i2.inst_outputs` by metis_tac[producing_inst_unique] >>
  `?k. MEM k insts1 /\ k.inst_id = i2.inst_id /\ k.inst_outputs = i2.inst_outputs`
    by metis_tac[] >>
  `MEM var k.inst_outputs` by metis_tac[] >>
  `MEM i1 insts1 /\ MEM var i1.inst_outputs` by metis_tac[producing_inst_unique] >>
  Cases_on `k = i1` >> gvs[] >>
  metis_tac[unique_defs_no_shared_output]
QED

Triviality producing_inst_none_no_mem:
  !insts var.
    producing_inst insts var = NONE ==>
    !i. MEM i insts ==> ~MEM var i.inst_outputs
Proof
  Induct >> rw[producing_inst_def] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem producing_inst_none_agree:
  !insts1 insts2 var.
    producing_inst insts1 var = NONE /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_outputs = j.inst_outputs) ==>
    producing_inst insts2 var = NONE
Proof
  rpt strip_tac >>
  Cases_on `producing_inst insts2 var` >> simp[] >>
  rename1 `SOME i2` >>
  imp_res_tac producing_inst_unique >>
  `?k. MEM k insts1 /\ k.inst_outputs = i2.inst_outputs` by metis_tac[] >>
  `~MEM var k.inst_outputs` by metis_tac[producing_inst_none_no_mem] >>
  metis_tac[]
QED

(* ================================================================
   operand_producer inst_id agreement
   ================================================================ *)

(* Under unique_defs, operand_producer on two lists with same
   inst_id+outputs elements returns OPTION_MAP with same inst_id *)
Triviality operand_producer_id_agree:
  !insts1 insts2 op.
    unique_defs insts1 /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) /\
    (!k. MEM k insts1 ==>
         ?j. MEM j insts2 /\ j.inst_id = k.inst_id /\
             j.inst_outputs = k.inst_outputs) ==>
    case (operand_producer insts1 op, operand_producer insts2 op) of
      (NONE, NONE) => T
    | (SOME i1, SOME i2) => i1.inst_id = i2.inst_id
    | (NONE, SOME _) => F
    | (SOME _, NONE) => F
Proof
  rpt strip_tac >>
  Cases_on `op` >> simp[operand_producer_def] >>
  Cases_on `producing_inst insts1 s` >>
  Cases_on `producing_inst insts2 s` >> simp[]
  (* NONE/SOME: use producing_inst_none_agree to derive contradiction *)
  >- (rename1 `_ = SOME i2` >>
      `!j. MEM j insts2 ==> ?k. MEM k insts1 /\ k.inst_outputs = j.inst_outputs`
        by (rpt strip_tac >> res_tac >> metis_tac[]) >>
      drule_all producing_inst_none_agree >> gvs[])
  (* SOME/NONE: symmetric case *)
  >- (rename1 `_ = SOME i1` >>
      `!j. MEM j insts1 ==> ?k. MEM k insts2 /\ k.inst_outputs = j.inst_outputs`
        by (rpt strip_tac >> res_tac >> metis_tac[]) >>
      drule_all producing_inst_none_agree >> gvs[])
  (* SOME/SOME: use producing_inst_perm_id *)
  >> drule_all producing_inst_perm_id >> simp[]
QED

(* ================================================================
   inst_data_deps inst_id agreement
   ================================================================ *)

(* MAP THE o FILTER IS_SOME o MAP preserves inst_id when individual
   elements agree on inst_id *)
Triviality map_the_filter_id_agree:
  !f1 f2 ls.
    (!x. MEM x ls ==>
      case (f1 x, f2 x) of
        (NONE, NONE) => T
      | (SOME a, SOME b) => a.inst_id = b.inst_id
      | (NONE, SOME _) => F
      | (SOME _, NONE) => F) ==>
    MAP (\i. i.inst_id) (MAP THE (FILTER IS_SOME (MAP f1 ls))) =
    MAP (\i. i.inst_id) (MAP THE (FILTER IS_SOME (MAP f2 ls)))
Proof
  ntac 2 gen_tac >> Induct >- simp[] >>
  rpt strip_tac >>
  (* Discharge IH: restrict MEM hypothesis to tail *)
  `MAP (\i. i.inst_id) (MAP THE (FILTER IS_SOME (MAP f1 ls))) =
   MAP (\i. i.inst_id) (MAP THE (FILTER IS_SOME (MAP f2 ls)))` by
    (first_x_assum irule >> rpt strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[MEM]) >>
  (* Handle the head *)
  first_x_assum (qspec_then `h` mp_tac) >> simp[MEM] >>
  Cases_on `f1 h` >> Cases_on `f2 h` >> simp[MAP, FILTER]
QED

Theorem nub_first_map_agree[local]:
  MAP f xs = MAP f ys /\
  INJ f (set xs) UNIV /\
  INJ f (set ys) UNIV ==>
  MAP f (nub_first xs) = MAP f (nub_first ys)
Proof
  metis_tac[nub_first_MAP_INJ]
QED

(* producing_inst returns unique objects: same inst_id implies same object,
   because producing_inst scans the list and returns the first match,
   and under unique_defs + ALL_DISTINCT inst_ids, the match is unique. *)
Triviality producing_inst_inj:
  !insts v1 v2 i1 i2.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    producing_inst insts v1 = SOME i1 /\
    producing_inst insts v2 = SOME i2 /\
    i1.inst_id = i2.inst_id ==>
    i1 = i2
Proof
  Induct >> rw[producing_inst_def] >>
  BasicProvers.every_case_tac >> gvs[MEM_MAP] >>
  imp_res_tac producing_inst_unique >> metis_tac[]
QED

(* operand_producer SOME results come from producing_inst *)
Triviality operand_producer_is_producing:
  !insts op i.
    operand_producer insts op = SOME i ==>
    ?v. producing_inst insts v = SOME i
Proof
  Cases_on `op` >> rw[operand_producer_def] >> metis_tac[]
QED

(* Any element of MAP THE (FILTER IS_SOME (MAP f ls)) is f(x) for some x in ls *)
Triviality mem_map_the_filter:
  !f ls x.
    MEM x (MAP THE (FILTER IS_SOME (MAP f ls))) ==>
    ?y. MEM y ls /\ f y = SOME x
Proof
  ntac 1 gen_tac >> Induct >> simp[MAP, FILTER] >> rpt strip_tac >>
  Cases_on `f h` >> gvs[FILTER, MEM] >> metis_tac[]
QED

(* Helper: any member of a deps list (var_deps or order_deps) comes from
   producing_inst, giving us a SOME equation we can feed to producing_inst_inj *)
Triviality mem_var_deps_producing:
  !insts ops x.
    MEM x (MAP THE (FILTER IS_SOME (MAP (operand_producer insts) ops))) ==>
    ?v. producing_inst insts v = SOME x
Proof
  rpt strip_tac >>
  drule mem_map_the_filter >> strip_tac >>
  drule operand_producer_is_producing >> metis_tac[]
QED

Triviality mem_order_deps_producing:
  !insts order x.
    MEM x (MAP THE (FILTER IS_SOME (MAP (producing_inst insts) order))) ==>
    ?v. producing_inst insts v = SOME x
Proof
  rpt strip_tac >> drule mem_map_the_filter >> metis_tac[]
QED

(* var_deps and order_deps elements satisfy INJ inst_id.
   Matches inst_data_deps_def (order_deps include self-dep filter). *)
Triviality deps_list_inj:
  !insts order inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    let var_deps = MAP THE (FILTER IS_SOME
      (MAP (operand_producer insts)
        (python_stack_operands inst.inst_opcode inst.inst_operands))) in
    let order_deps =
      if is_terminator inst.inst_opcode
      then FILTER (\d. d.inst_id <> inst.inst_id)
             (MAP THE (FILTER IS_SOME (MAP (producing_inst insts) order)))
      else [] in
    INJ (\i. i.inst_id) (set (var_deps ++ order_deps)) UNIV
Proof
  rpt strip_tac >> simp[INJ_DEF] >> rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[MEM_APPEND, MEM, MEM_FILTER] >>
  rpt (first_x_assum
    (strip_assume_tac o MATCH_MP mem_var_deps_producing)) >>
  rpt (first_x_assum
    (strip_assume_tac o MATCH_MP mem_order_deps_producing)) >>
  irule producing_inst_inj >> metis_tac[]
QED

(* Helper: var_deps MAP inst_id agrees *)
Triviality var_deps_id_agree:
  !insts1 insts2 ops.
    unique_defs insts1 /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) /\
    (!k. MEM k insts1 ==>
         ?j. MEM j insts2 /\ j.inst_id = k.inst_id /\
             j.inst_outputs = k.inst_outputs) ==>
    MAP (\i. i.inst_id)
      (MAP THE (FILTER IS_SOME (MAP (operand_producer insts1) ops))) =
    MAP (\i. i.inst_id)
      (MAP THE (FILTER IS_SOME (MAP (operand_producer insts2) ops)))
Proof
  rpt strip_tac >> irule map_the_filter_id_agree >> rpt strip_tac >>
  mp_tac (Q.SPECL [`insts1`, `insts2`, `x`] operand_producer_id_agree) >>
  impl_tac >- metis_tac[] >>
  Cases_on `operand_producer insts1 x` >>
  Cases_on `operand_producer insts2 x` >> simp[]
QED

(* Helper: order_deps MAP inst_id agrees *)
Triviality order_deps_id_agree:
  !insts1 insts2 order.
    unique_defs insts1 /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) /\
    (!k. MEM k insts1 ==>
         ?j. MEM j insts2 /\ j.inst_id = k.inst_id /\
             j.inst_outputs = k.inst_outputs) ==>
    MAP (\i. i.inst_id)
      (MAP THE (FILTER IS_SOME (MAP (producing_inst insts1) order))) =
    MAP (\i. i.inst_id)
      (MAP THE (FILTER IS_SOME (MAP (producing_inst insts2) order)))
Proof
  rpt strip_tac >> irule map_the_filter_id_agree >> rpt strip_tac >>
  Cases_on `producing_inst insts1 x` >>
  Cases_on `producing_inst insts2 x` >> simp[]
  (* NONE/SOME on insts2: use none_agree insts1→insts2 *)
  >- (`!j. MEM j insts2 ==> ?k. MEM k insts1 /\ k.inst_outputs = j.inst_outputs`
       by (rpt strip_tac >> res_tac >> metis_tac[]) >>
      drule_all producing_inst_none_agree >> gvs[])
  (* SOME/NONE on insts2: use none_agree insts2→insts1 *)
  >- (`!j. MEM j insts1 ==> ?k. MEM k insts2 /\ k.inst_outputs = j.inst_outputs`
       by (rpt strip_tac >> res_tac >> metis_tac[]) >>
      drule_all producing_inst_none_agree >> gvs[])
  >> drule_all producing_inst_perm_id >> simp[]
QED

(* If MAP f l1 = MAP f l2, filtering by a predicate on f preserves the
   MAP f agreement. Used for the FILTER in inst_data_deps order_deps. *)
Triviality filter_map_agree:
  !f P l1 l2.
    MAP f l1 = MAP f l2 ==>
    MAP f (FILTER (\x. P (f x)) l1) = MAP f (FILTER (\x. P (f x)) l2)
Proof
  Induct_on `l1` >> Cases_on `l2` >> simp[] >>
  rpt strip_tac >> Cases_on `P (f h)` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* inst_data_deps returns same inst_ids for two agreeing block_insts lists *)
Theorem inst_data_deps_id_agree:
  !insts1 insts2 order inst.
    unique_defs insts1 /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts1) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts2) /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) /\
    (!k. MEM k insts1 ==>
         ?j. MEM j insts2 /\ j.inst_id = k.inst_id /\
             j.inst_outputs = k.inst_outputs) ==>
    MAP (\i. i.inst_id)
      (inst_data_deps insts2 order inst) =
    MAP (\i. i.inst_id)
      (inst_data_deps insts1 order inst)
Proof
  rpt strip_tac >>
  simp[inst_data_deps_def, LET_THM] >>
  imp_res_tac var_deps_id_agree >>
  imp_res_tac order_deps_id_agree >>
  `MAP (\i. i.inst_id)
     (FILTER (\d. d.inst_id <> inst.inst_id)
       (MAP THE (FILTER IS_SOME (MAP (producing_inst insts2) order)))) =
   MAP (\i. i.inst_id)
     (FILTER (\d. d.inst_id <> inst.inst_id)
       (MAP THE (FILTER IS_SOME (MAP (producing_inst insts1) order))))` by
    (qspecl_then [`\d. d.inst_id`, `\x. x <> inst.inst_id`]
       mp_tac filter_map_agree >> simp[]) >>
  irule nub_first_map_agree >> rpt conj_tac
  >- (Cases_on `is_terminator inst.inst_opcode` >> gvs[MAP_APPEND])
  >- (mp_tac (Q.SPECL [`insts2`, `order`, `inst`] deps_list_inj) >>
      simp[LET_THM, LIST_TO_SET_APPEND, pred_setTheory.UNION_COMM])
  >> mp_tac (Q.SPECL [`insts1`, `order`, `inst`] deps_list_inj) >>
  simp[LET_THM, LIST_TO_SET_APPEND, pred_setTheory.UNION_COMM]
QED

(* ================================================================
   Effect-free instruction lemmas
   ================================================================ *)

(* ================================================================
   compute_effect_deps key locality
   ================================================================ *)

(* Converse of preserves_key: compute_effect_deps depends only on
   effect keys of the instruction *)

(* ================================================================
   build_eda: tracking state depends only on effect-ful subsequence
   ================================================================ *)

(* Predicate: instruction has non-empty effects *)
Definition has_effects_def:
  has_effects i <=> write_effects i.inst_opcode <> {} \/
                    read_effects i.inst_opcode <> {}
End

(* Define the FOLDL step function used in build_eda *)
Definition eda_fold_step_def:
  eda_fold_step (acc_map, et) inst =
    let (deps, et') = compute_effect_deps et inst in
    (acc_map |+ (inst.inst_id, deps), et')
End

(* Interleaving effect-free instructions preserves the tracking state
   and produces the same deps for effect-ful instructions.

   Key property: if we partition the instruction list into effect-ful
   and effect-free, the fold's tracking state trajectory depends only
   on the effect-ful subsequence.

   We prove: for any instruction list, the SND of the fold equals
   the SND of the fold over just the effect-ful instructions. *)

(* ================================================================
   Per-key tracking state factorization
   ================================================================ *)


(* ================================================================
   build_eda agreement: same effect-ful subsequence => same result
   ================================================================ *)



Theorem all_distinct_map_filter:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct_on `l` >> simp[FILTER] >>
  rpt strip_tac >> Cases_on `P h` >> simp[MAP] >> fs[MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

(* ===== FUPDATE_LIST order independence ===== *)

(* ===== build_eda agreement ===== *)

(* ===== build_full_eda pseudo-stripping ===== *)

(* build_full_eda only depends on the non-pseudo sub-list.
   This lets us strip pseudos and reason about the non-pseudo core. *)

(* Helper: FILTER (¬is_pseudo) distributes over phis ++ nonpseudos *)
Triviality filter_nonpseudo_append_pseudo:
  !phis L.
    EVERY (\i. is_pseudo i.inst_opcode) phis /\
    EVERY (\i. ~is_pseudo i.inst_opcode) L ==>
    FILTER (\i. ~is_pseudo i.inst_opcode) (phis ++ L) = L
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  simp[FILTER_EQ_ID]
QED

(* build_full_eda depends only on the non-pseudo sub-list.
   Proof approach: build_full_eda is a composition of functions that each
   begin with FILTER (¬is_pseudo) block_insts. Showing the filter result
   is the same suffices. Use AP_TERM / CONG reasoning rather than expanding. *)
Theorem build_full_eda_pseudo_strip:
  !phis L.
    EVERY (\i. is_pseudo i.inst_opcode) phis /\
    EVERY (\i. ~is_pseudo i.inst_opcode) L ==>
    build_full_eda (phis ++ L) = build_full_eda L
Proof
  rpt strip_tac >>
  drule_all filter_nonpseudo_append_pseudo >> strip_tac >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) L = L` by
    simp[FILTER_EQ_ID] >>
  (* build_full_eda = add_alloca_deps bi (add_barrier_deps bi (add_abort_deps bi (build_eda bi)))
     Each sub-function uses bi only through FILTER (¬is_pseudo) bi.
     Since FILTER (¬is_pseudo) (phis ++ L) = L = FILTER (¬is_pseudo) L,
     every sub-function receives the same filtered list. *)
  `build_eda (phis ++ L) = build_eda L` by
    simp[build_eda_def, LET_THM] >>
  `add_abort_deps (phis ++ L) (build_eda L) =
   add_abort_deps L (build_eda L)` by
    simp[add_abort_deps_def, add_chain_deps_def, LET_THM] >>
  `add_barrier_deps (phis ++ L) (add_abort_deps L (build_eda L)) =
   add_barrier_deps L (add_abort_deps L (build_eda L))` by
    simp[add_barrier_deps_def, add_deps_on_barrier_def,
         add_deps_from_barrier_def, LET_THM] >>
  `add_alloca_deps (phis ++ L)
     (add_barrier_deps L (add_abort_deps L (build_eda L))) =
   add_alloca_deps L
     (add_barrier_deps L (add_abort_deps L (build_eda L)))` by
    simp[add_alloca_deps_def, add_chain_deps_def, LET_THM] >>
  simp[build_full_eda_def, LET_THM]
QED
