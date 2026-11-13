Theory loadElimSupportHelpers
Ancestors
  loadElimDefs loadElimLatticeSoundHelpers loadElimTransferProvenance
  finite_map pred_set list rich_list

Definition le_generated_keys_def:
  le_generated_keys ctx insts =
    set (MAP (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
                (normalize_operand ctx.lctx_dfg [])) insts) UNION
    set (MAP (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
                (normalize_operand ctx.lctx_dfg [])) insts)
End

Definition le_generated_operands_def:
  le_generated_operands insts =
    set (FLAT (MAP (\i. MAP Var i.inst_outputs ++ i.inst_operands) insts))
End

Definition le_lattice_supported_def:
  le_lattice_supported keys vals ll <=>
    !k vs. FLOOKUP (unwrap_load_lattice ll) k = SOME vs ==>
      k IN keys /\ EVERY (\v. v IN vals) vs /\ ALL_DISTINCT vs
End

Theorem le_generated_keys_finite[simp]:
  FINITE (le_generated_keys ctx insts)
Proof
  simp[le_generated_keys_def]
QED

Theorem le_generated_operands_finite[simp]:
  FINITE (le_generated_operands insts)
Proof
  simp[le_generated_operands_def]
QED

Theorem le_transfer_generates_supported:
  MEM inst insts /\ le_transfer_generates ctx inst k v ==>
  k IN le_generated_keys ctx insts /\ v IN le_generated_operands insts
Proof
  rw[le_transfer_generates_def, le_generated_keys_def,
     le_generated_operands_def, MEM_MAP, MEM_FLAT]
  >- (disj1_tac >> qexists `inst` >> simp[])
  >- (qexists `MAP Var inst.inst_outputs ++ inst.inst_operands` >>
      simp[] >> qexists `inst` >> simp[])
  >- (disj2_tac >> qexists `inst` >> simp[]) >>
  qexists `MAP Var inst.inst_outputs ++ inst.inst_operands` >>
  simp[] >> qexists `inst` >> simp[]
QED

Theorem le_lattice_supported_empty[simp]:
  le_lattice_supported keys vals NONE /\
  le_lattice_supported keys vals (SOME FEMPTY)
Proof
  simp[le_lattice_supported_def, unwrap_load_lattice_def]
QED

Theorem le_transfer_supported:
  MEM inst insts /\
  le_lattice_supported (le_generated_keys ctx insts)
    (le_generated_operands insts) initial ==>
  le_lattice_supported (le_generated_keys ctx insts)
    (le_generated_operands insts) (load_transfer ctx inst initial)
Proof
  simp[le_lattice_supported_def] >> rpt strip_tac >>
  drule le_transfer_lookup_origin >> strip_tac >>
  gvs[] >> metis_tac[le_transfer_generates_supported]
QED

Theorem le_operand_union_distinct:
  ALL_DISTINCT xs /\ ALL_DISTINCT ys ==>
  ALL_DISTINCT (operand_list_union xs ys)
Proof
  simp[operand_list_union_def, ALL_DISTINCT_APPEND,
       MEM_FILTER] >> metis_tac[FILTER_ALL_DISTINCT]
QED

Theorem le_join_supported:
  le_lattice_supported keys vals a /\
  le_lattice_supported keys vals b ==>
  le_lattice_supported keys vals (load_join a b)
Proof
  Cases_on `a` >- simp[load_join_def] >>
  Cases_on `b` >- simp[load_join_def] >>
  simp[le_lattice_supported_def, load_join_def, unwrap_load_lattice_def] >>
  rpt strip_tac >> drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[le_operand_union_distinct, EVERY_MEM, mem_operand_list_union]
QED

Theorem le_operand_union_absorb_right:
  operand_list_union (operand_list_union xs ys) ys = operand_list_union xs ys
Proof
  simp[Once operand_list_union_def, mem_operand_list_union,
       FILTER_EQ_NIL, EVERY_MEM]
QED

Theorem le_operand_union_absorb_left:
  operand_list_union xs (operand_list_union xs ys) = operand_list_union xs ys
Proof
  simp[operand_list_union_def, FILTER_APPEND, FILTER_FILTER, FILTER_EQ_NIL, EVERY_MEM]
QED

Theorem le_transfer_fold_supported:
  !xs initial.
  EVERY (\i. MEM i insts) xs /\
  le_lattice_supported (le_generated_keys ctx insts)
    (le_generated_operands insts) initial ==>
  le_lattice_supported (le_generated_keys ctx insts)
    (le_generated_operands insts)
    (FOLDL (\ll i. load_transfer ctx i ll) initial xs)
Proof
  Induct >- simp[] >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  irule le_transfer_supported >> simp[]
QED
