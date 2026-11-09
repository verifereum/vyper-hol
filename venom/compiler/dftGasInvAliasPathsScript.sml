Theory dftGasInvAliasPaths
Ancestors
  dftGasInvForwardOrigins dftGasInvAliasNormal dftIdempotent dftTopoSort dftDefs relation list rich_list
  contextCodegenRel contextCodegenRelProps venomInst venomWf arithmetic

Definition inv_assign_edge_def:
  inv_assign_edge xs a b <=>
    ?v inst. a = Var v /\ producing_inst xs v = SOME inst /\
      inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [v] /\
      inst.inst_operands = [b]
End

Definition inv_alias_terminal_def:
  inv_alias_terminal xs a b <=>
    RTC (inv_assign_edge xs) a b /\ ~(?c. inv_assign_edge xs b c)
End

Definition inv_terminal_producer_def:
  inv_terminal_producer xs a prod <=>
    ?b. inv_alias_terminal xs a b /\ operand_producer xs b = SOME prod /\
        prod.inst_opcode <> ASSIGN
End

Theorem inv_assign_edge_functional:
  inv_assign_edge xs a b /\ inv_assign_edge xs a c ==> b = c
Proof
  rpt strip_tac >> gvs[inv_assign_edge_def]
QED

Theorem inv_functional_terminal_unique[local]:
  (!a b c. rel a b /\ rel a c ==> b = c) ==>
  !a b. RTC rel a b ==> !c.
    RTC rel a c /\ ~(?d. rel b d) /\ ~(?d. rel c d) ==> b = c
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- (gvs[Once RTC_CASES1] >> metis_tac[]) >>
  qpat_x_assum `RTC rel _ c` mp_tac >>
  rewrite_tac[Once RTC_CASES1] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem inv_alias_terminal_unique:
  inv_alias_terminal xs a b /\ inv_alias_terminal xs a c ==> b = c
Proof
  simp[inv_alias_terminal_def] >>
  metis_tac[inv_functional_terminal_unique, inv_assign_edge_functional]
QED

Theorem inv_alias_scan_producer[local]:
  !k xs h v.
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) xs)) /\
  h < k /\ k <= LENGTH xs /\ MEM v (EL h xs).inst_outputs ==>
  resolve_block_assigns (REVERSE (TAKE k xs)) (Var v) =
  resolve_block_assigns (EL h xs :: REVERSE (TAKE h xs)) (Var v)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `k < LENGTH xs` by decide_tac >>
  `TAKE (SUC k) xs = TAKE k xs ++ [EL k xs]` by
    simp[TAKE_EL_SNOC, ADD1] >>
  simp[REVERSE_APPEND] >>
  Cases_on `h = k` >- gvs[] >>
  `h < k /\ h < LENGTH xs` by decide_tac >>
  `~MEM v (EL k xs).inst_outputs` by
    metis_tac[inv_alias_output_index_unique] >>
  qpat_x_assum `!xs h v. _` (qspecl_then [`xs`, `h`, `v`] mp_tac) >>
  simp[resolve_block_assigns_def]
QED

Theorem inv_alias_scan_no_producer[local]:
  producing_inst xs v = NONE ==>
  resolve_block_assigns (REVERSE (TAKE k xs)) (Var v) = Var v
Proof
  `!xs. producing_inst xs v = NONE ==>
     EVERY (\inst. ~MEM v inst.inst_outputs) xs` by
    (Induct >> simp[producing_inst_def] >> rpt strip_tac >>
     gvs[AllCaseEqs()]) >>
  strip_tac >> irule resolve_block_assigns_no_write >>
  simp[EVERY_REVERSE] >> irule EVERY_TAKE >> metis_tac[]
QED

Theorem inv_alias_use_endpoint:
  !k xs a.
  EVERY inst_wf xs /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) xs)) /\
  np_defs_before_uses xs /\ k < LENGTH xs /\
  ~is_pseudo (EL k xs).inst_opcode /\ MEM a (EL k xs).inst_operands ==>
  inv_alias_terminal xs a (resolve_block_assigns (REVERSE (TAKE k xs)) a)
Proof
  completeInduct_on `k` >> rpt gen_tac >> strip_tac >>
  Cases_on `a` >>
  simp[resolve_block_assigns_def, inv_alias_terminal_def,
       inv_assign_edge_def, RTC_REFL] >>
  rename1 `MEM (Var v) (EL k xs).inst_operands` >>
  Cases_on `producing_inst xs v`
  >- (simp[inv_alias_scan_no_producer, inv_alias_terminal_def,
           inv_assign_edge_def, RTC_REFL]) >>
  rename1 `producing_inst xs v = SOME prod` >>
  `?h. h < k /\ EL h xs = prod` by
    metis_tac[np_defs_before_uses_def] >>
  `h < LENGTH xs` by decide_tac >>
  `MEM v prod.inst_outputs` by metis_tac[producing_inst_unique] >>
  `inst_wf prod` by metis_tac[EVERY_EL] >>
  `resolve_block_assigns (REVERSE (TAKE k xs)) (Var v) =
   resolve_block_assigns (prod :: REVERSE (TAKE h xs)) (Var v)` by
    metis_tac[inv_alias_scan_producer, LESS_IMP_LESS_OR_EQ] >>
  Cases_on `prod.inst_opcode = ASSIGN`
  >- (`prod.inst_outputs = [v] /\ LENGTH prod.inst_operands = 1` by
        (gvs[inst_wf_def] >>
         qpat_x_assum `LENGTH _.inst_outputs = 1` mp_tac >>
         simp[LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[]) >>
      Cases_on `prod.inst_operands` >> gs[] >>
      rename1 `prod.inst_operands = [b]` >>
      `inv_alias_terminal xs b
         (resolve_block_assigns (REVERSE (TAKE h xs)) b)` by
        (first_x_assum irule >> simp[is_pseudo_def] >> metis_tac[]) >>
      gvs[resolve_block_assigns_def, inv_alias_terminal_def] >>
      reverse conj_tac >- metis_tac[inv_assign_edge_def] >>
      irule RTC_TRANS >> qexists `b` >> simp[] >>
      irule RTC_SINGLE >> simp[inv_assign_edge_def] >> metis_tac[]) >>
  simp[resolve_block_assigns_def, inv_alias_terminal_def,
       inv_assign_edge_def, RTC_REFL]
QED

Theorem inv_alias_use_terminal:
  EVERY inst_wf xs /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) xs)) /\
  np_defs_before_uses xs /\ k < LENGTH xs /\
  ~is_pseudo (EL k xs).inst_opcode /\ MEM a (EL k xs).inst_operands ==>
  (inv_alias_terminal xs a b <=>
   b = resolve_block_assigns (REVERSE (TAKE k xs)) a)
Proof
  strip_tac >> drule_all inv_alias_use_endpoint >>
  metis_tac[inv_alias_terminal_unique]
QED

Theorem inv_terminal_producer_use:
  EVERY inst_wf xs /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) xs)) /\
  np_defs_before_uses xs /\ k < LENGTH xs /\
  ~is_pseudo (EL k xs).inst_opcode /\ MEM a (EL k xs).inst_operands ==>
  (inv_terminal_producer xs a prod <=>
   operand_producer xs (resolve_block_assigns (REVERSE (TAKE k xs)) a) =
     SOME prod /\ prod.inst_opcode <> ASSIGN)
Proof
  strip_tac >> simp[inv_terminal_producer_def] >>
  drule_all inv_alias_use_terminal >> metis_tac[]
QED
