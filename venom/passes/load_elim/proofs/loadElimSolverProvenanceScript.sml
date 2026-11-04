Theory loadElimSolverProvenance
Ancestors
  loadElimLatticeSoundHelpers loadElimDefs finite_map list

Theorem le_join_selected_lookup:
  b = SOME m /\
  FLOOKUP (unwrap_load_lattice (load_join a b)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  strip_tac >> gvs[] >> Cases_on `a` >>
  gvs[load_join_def, unwrap_load_lattice_def] >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_join_selected_lookup_left:
  a = SOME m /\
  FLOOKUP (unwrap_load_lattice (load_join a b)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  strip_tac >> gvs[] >> Cases_on `b` >>
  gvs[load_join_def, unwrap_load_lattice_def] >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_join_fold_lookup_acc[local]:
  !xs m vs.
  FLOOKUP (unwrap_load_lattice (FOLDL load_join (SOME m) xs)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  Induct_on `xs` >- (simp[unwrap_load_lattice_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h` >> gvs[load_join_def] >>
  first_x_assum drule >> strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_join_fold_selected_lookup_general[local]:
  !xs a vs.
  MEM (SOME m) xs /\
  FLOOKUP (unwrap_load_lattice (FOLDL load_join a xs)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> simp[] >> strip_tac
  >- (gvs[] >>
      Cases_on `a` >> gvs[load_join_def] >>
      drule le_join_fold_lookup_acc >> simp[] >> strip_tac >>
      drule load_join_raw_lookup >> strip_tac >> gvs[] >>
      metis_tac[mem_operand_list_union]) >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem le_join_fold_selected_lookup:
  MEM (SOME m) xs /\
  FLOOKUP (unwrap_load_lattice (FOLDL load_join NONE xs)) k = SOME vs ==>
  ?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  metis_tac[le_join_fold_selected_lookup_general]
QED

Theorem le_boundary_absorbed_lookup:
  boundary = load_join boundary (SOME exit) /\
  FLOOKUP (unwrap_load_lattice boundary) k = SOME vs ==>
  ?ws. FLOOKUP exit k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)
Proof
  metis_tac[le_join_selected_lookup]
QED
