(* Complete a cut observer's resource metadata without adding reachable code. *)
Theory extcallReturnObserver
Ancestors
  extcallReturnCountedCheck exprSimAbiGasBridge abiMalformedRecursiveInterface
  venomInst compileEnv exprLoweringProps fragExec list unitShapeDefs callLayoutDefs
  venomWf localPtrsProps dftPipelineInvar sorting

Definition return_observer_complete_def:
  return_observer_complete func obs keep =
    obs with fn_blocks := obs.fn_blocks ++
      [<|bb_label := keep;
         bb_instructions := FILTER
           (\i. i.inst_opcode = ALLOCA /\ ~MEM i (fn_insts obs))
           (fn_insts func)|>]
End

Theorem return_observer_complete_members:
  MEM i (fn_insts (return_observer_complete func obs keep)) <=>
  MEM i (fn_insts obs) \/
  i.inst_opcode = ALLOCA /\ MEM i (fn_insts func)
Proof
  simp[return_observer_complete_def, fn_insts_def,
    MEM_fn_insts_blocks_iff, MEM_APPEND, MEM_FILTER,
    RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> metis_tac[]
QED

Theorem return_observer_complete_allocas:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts (return_observer_complete func obs keep)) <=>
     MEM i (fn_insts func)))
Proof
  simp[return_observer_complete_members] >> metis_tac[]
QED

Theorem return_observer_complete_scratch:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  abi_malformed_scratch_sites st en (return_observer_complete func obs keep) =
  abi_malformed_scratch_sites st en func
Proof
  strip_tac >> drule return_observer_complete_allocas >>
  simp[abi_malformed_scratch_sites_def, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem return_observer_complete_destination:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (abi_malformed_destination (return_observer_complete func obs keep)
      cenv scopes aid d n s <=>
   abi_malformed_destination func cenv scopes aid d n s)
Proof
  strip_tac >> drule return_observer_complete_allocas >>
  simp[abi_malformed_destination_def] >> metis_tac[]
QED

Theorem return_observer_complete_local_backed:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (local_backed (return_observer_complete func obs keep) p s b n <=>
   local_backed func p s b n)
Proof
  strip_tac >> drule return_observer_complete_allocas >>
  simp[local_backed_def] >> metis_tac[]
QED

Theorem return_observer_complete_local_ptrs:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (local_ptrs_rel (return_observer_complete func obs keep) cenv scopes s <=>
   local_ptrs_rel func cenv scopes s)
Proof
  strip_tac >> simp[local_ptrs_rel_def] >>
  metis_tac[return_observer_complete_local_backed]
QED

Theorem return_observer_complete_state_rel:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (state_rel (return_observer_complete func obs keep) cenv cx es s <=>
   state_rel func cenv cx es s)
Proof
  strip_tac >> drule return_observer_complete_local_ptrs >>
  simp[state_rel_def]
QED

Theorem return_observer_complete_immutable_sep:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (immutable_alloca_sep (return_observer_complete func obs keep) cenv cx es s <=>
   immutable_alloca_sep func cenv cx es s)
Proof
  strip_tac >> drule return_observer_complete_allocas >>
  simp[immutable_alloca_sep_def] >> metis_tac[]
QED

Theorem return_observer_complete_lookup:
  lookup_block lbl obs.fn_blocks = SOME bb ==>
  lookup_block lbl (return_observer_complete func obs keep).fn_blocks = SOME bb
Proof
  simp[return_observer_complete_def, lookup_block_def, FIND_APPEND_CASE]
QED

Theorem return_observer_complete_has_code:
  fn_has_code st en obs ==>
  fn_has_code st en (return_observer_complete func obs keep)
Proof
  rw[fn_has_code_def] >> metis_tac[return_observer_complete_lookup]
QED

Theorem return_observer_complete_fresh_label:
  ?keep. ~MEM keep (MAP (\bb. bb.bb_label) obs.fn_blocks) /\
    EVERY (\i. ~MEM (Label keep) i.inst_operands) (fn_insts obs)
Proof
  qspec_then `MAP (\bb. bb.bb_label) obs.fn_blocks ++
    FLAT (MAP (\i. MAP (\op. case op of Label l => l | _ => "")
      i.inst_operands) (fn_insts obs))` mp_tac frag_fresh_label >>
  simp[MEM_FLAT, MEM_MAP, EVERY_MEM] >> strip_tac >>
  qexists_tac `L` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!l. _` (qspec_then
    `MAP (\op. case op of Label l => l | _ => "") i.inst_operands` mp_tac) >>
  simp[MEM_MAP] >> conj_tac
  >- (qexists_tac `i` >> simp[]) >>
  qexists_tac `Label L` >> simp[]
QED

Theorem return_observer_complete_ids:
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i j. MEM i (fn_insts func) /\ MEM j (fn_insts obs) /\
         i.inst_id = j.inst_id ==> i = j) ==>
  fn_inst_ids_distinct (return_observer_complete func obs keep)
Proof
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
      FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
    fs[fn_inst_ids_distinct_def, fn_insts_def] >>
  simp[fn_inst_ids_distinct_def, return_observer_complete_def,
    MAP_APPEND, ALL_DISTINCT_APPEND] >> conj_tac
  >- fs[fn_inst_ids_distinct_def] >> conj_tac
  >- (irule all_distinct_map_filter >> simp[]) >>
  qpat_assum `!bbs. MAP _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  simp[MEM_MAP, MEM_FILTER, GSYM fn_insts_def] >> metis_tac[]
QED

Theorem return_observer_allocas_permutation:
  ALL_DISTINCT (fn_insts func) /\ ALL_DISTINCT (fn_insts obs) /\
  (!i. i.inst_opcode = ALLOCA ==>
       (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) ==>
  PERM (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs))
       (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func))
Proof
  strip_tac >> irule sortingTheory.PERM_ALL_DISTINCT >>
  conj_tac
  >- (simp[MEM_FILTER] >> metis_tac[]) >>
  conj_tac >> irule listTheory.FILTER_ALL_DISTINCT >> simp[]
QED

Theorem return_observer_pending_charge:
  PERM (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs))
       (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func)) ==>
  pending_alloca_size obs s = pending_alloca_size func s
Proof
  strip_tac >> simp[pending_alloca_size_def] >>
  `!code. FILTER (\i. i.inst_opcode = ALLOCA /\
                      i.inst_id NOTIN FDOM s.vs_allocas) code =
          FILTER (\i. i.inst_id NOTIN FDOM s.vs_allocas)
            (FILTER (\i. i.inst_opcode = ALLOCA) code)` by
    (Induct >> simp[] >> gen_tac >>
     Cases_on `h.inst_opcode = ALLOCA` >> simp[]) >>
  asm_rewrite_tac[] >> irule PERM_SUM >>
  irule PERM_MAP >> irule PERM_FILTER >> simp[]
QED
