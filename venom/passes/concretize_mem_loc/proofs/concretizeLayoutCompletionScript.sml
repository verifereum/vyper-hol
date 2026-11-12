Theory concretizeLayoutCompletion
Ancestors concretizeLayoutExtension concretizeMemLocDefs finite_map list
  venomInst

(* Existing success certificates require completion_state_inv.  Preservation
   alone needs no validity, size, uniqueness or interval hypotheses. *)
Theorem complete_alloc_positions_aux_preserves_lookup:
  !insts positions occupied completed a p.
  complete_alloc_positions_aux insts positions occupied = SOME completed /\
  FLOOKUP positions a = SOME p ==>
  FLOOKUP completed a = SOME p
Proof
  Induct_on `insts`
  >- simp[complete_alloc_positions_aux_def]
  >> rpt gen_tac
  >> simp[Once complete_alloc_positions_aux_def]
  >> Cases_on `h.inst_opcode = ALLOCA` >> simp[]
  >- (Cases_on `exact_static_alloca_size h` >> simp[]
      >> Cases_on `FLOOKUP positions (Allocation h.inst_id)` >> simp[]
      >- (Cases_on `checked_first_fit occupied x` >> simp[]
          >> rpt strip_tac >> first_x_assum irule
          >> goal_assum (drule_at (Pat `complete_alloc_positions_aux _ _ _ = _`))
          >> Cases_on `Allocation h.inst_id = a` >> gvs[FLOOKUP_UPDATE])
      >> metis_tac[])
  >> metis_tac[]
QED

Theorem complete_alloc_positions_with_imports_preserves_lookup:
  complete_alloc_positions_with_imports items forced reserved imported fn positions = SOME completed /\
  merge_forced_positions items forced positions = SOME merged /\
  FLOOKUP merged a = SOME p ==>
  FLOOKUP completed a = SOME p
Proof
  simp[complete_alloc_positions_with_imports_def]
  >> rpt strip_tac >> gvs[AllCaseEqs()]
  >> metis_tac[complete_alloc_positions_aux_preserves_lookup]
QED

Theorem complete_alloc_positions_with_imports_preserves_placements:
  complete_alloc_positions_with_imports items forced reserved imported fn positions = SOME completed /\
  merge_forced_positions items forced positions = SOME merged /\
  (!a l p s. MEM (a,l,p,s) E ==> FLOOKUP merged a = SOME p) ==>
  (!a l p s. MEM (a,l,p,s) E ==> FLOOKUP completed a = SOME p)
Proof
  metis_tac[complete_alloc_positions_with_imports_preserves_lookup]
QED
