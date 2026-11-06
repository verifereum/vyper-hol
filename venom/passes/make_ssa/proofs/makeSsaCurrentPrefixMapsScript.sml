Theory makeSsaCurrentPrefixMaps
Ancestors
  o1FrameLockstep finite_map pred_set list

Definition current_prefix_pull_def:
  current_prefix_pull inst R z x <=>
    (?d src. inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [d] /\
      inst.inst_operands = [Var src] /\ z = src /\ R d x) \/
    (~MEM z inst.inst_outputs /\ R z x)
End

Definition current_prefix_back_def:
  (current_prefix_back [] M z x <=> FLOOKUP M z = SOME x) /\
  (current_prefix_back (inst::rest) M z x <=>
    current_prefix_pull inst (current_prefix_back rest M) z x)
End

Definition current_prefix_functional_def:
  current_prefix_functional R <=> !z x y. R z x /\ R z y ==> x = y
End

Definition current_prefix_map_def:
  current_prefix_map xs M =
    @m. !z x. FLOOKUP m z = SOME x <=> current_prefix_back xs M z x
End

Theorem current_prefix_pull_finite:
  FINITE {z | ?x. R z x} ==>
  FINITE {z | ?x. current_prefix_pull inst R z x}
Proof
  strip_tac >>
  Cases_on `?d src. inst.inst_opcode = ASSIGN /\
    inst.inst_outputs = [d] /\ inst.inst_operands = [Var src]`
  >- (pop_assum strip_assume_tac >>
      irule SUBSET_FINITE >>
      qexists `src INSERT {z | ?x. R z x}` >>
      simp[SUBSET_DEF, current_prefix_pull_def] >> metis_tac[]) >>
  irule SUBSET_FINITE >> qexists `{z | ?x. R z x}` >>
  simp[SUBSET_DEF, current_prefix_pull_def] >> metis_tac[]
QED

Theorem current_prefix_back_finite:
  !xs M. FINITE {z | ?x. current_prefix_back xs M z x}
Proof
  Induct >> simp[current_prefix_back_def]
  >- (gen_tac >>
      `{z | ?x. FLOOKUP M z = SOME x} = FDOM M` by
        (simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >> simp[]) >>
  rpt gen_tac >> irule current_prefix_pull_finite >> simp[]
QED

Theorem current_prefix_relation_map[local]:
  FINITE {z | ?x. R z x} /\ current_prefix_functional R ==>
  ?m. !z x. FLOOKUP m z = SOME x <=> R z x
Proof
  strip_tac >>
  qexists `FUN_FMAP (\z. @x. R z x) {z | ?x. R z x}` >>
  simp[FLOOKUP_FUN_FMAP] >> rpt gen_tac >>
  Cases_on `?v. R z v` >> simp[]
  >- (SELECT_ELIM_TAC >> fs[current_prefix_functional_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem current_prefix_map_lookup:
  current_prefix_functional (current_prefix_back xs M) ==>
  (FLOOKUP (current_prefix_map xs M) z = SOME x <=>
   current_prefix_back xs M z x)
Proof
  strip_tac >>
  `?m. !z x. FLOOKUP m z = SOME x <=> current_prefix_back xs M z x` by
    (irule current_prefix_relation_map >> simp[current_prefix_back_finite]) >>
  simp[current_prefix_map_def] >> SELECT_ELIM_TAC >> metis_tac[]
QED

Theorem current_prefix_map_nil:
  current_prefix_map [] M = M
Proof
  `current_prefix_functional (current_prefix_back [] M)` by
    (simp[current_prefix_functional_def, current_prefix_back_def] >>
     rpt strip_tac >> gvs[]) >>
  simp[fmap_eq_flookup] >> gen_tac >>
  Cases_on `FLOOKUP M x` >>
  metis_tac[current_prefix_map_lookup, current_prefix_back_def,
    optionTheory.option_CASES, optionTheory.NOT_NONE_SOME]
QED

Theorem current_prefix_copy_collision:
  inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [dst] /\
  inst.inst_operands = [Var src] /\ dst <> src /\
  FLOOKUP M dst = SOME x /\ FLOOKUP M src = SOME y /\ x <> y ==>
  ~current_prefix_functional (current_prefix_back [inst] M)
Proof
  simp[current_prefix_functional_def, current_prefix_back_def,
    current_prefix_pull_def] >> metis_tac[]
QED
