Theory algebraicOptSsaCmpProofs
Ancestors
  algebraicOptDefs algebraicOptSupplyProofs venomInst venomWf
  list pred_set alist

Theorem ao_named_lookup_value:
  ALOOKUP named key = SOME (out,id,v) ==>
  MEM v (MAP (\(a,(out,id,v)). v) named)
Proof
  strip_tac >> drule ALOOKUP_MEM >> strip_tac >>
  simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ao_named_lookup_injective:
  !named k1 k2 out1 id1 out2 id2 v.
    ALL_DISTINCT (MAP (\(a,(out,id,v)). v) named) /\
    ALOOKUP named k1 = SOME (out1,id1,v) /\
    ALOOKUP named k2 = SOME (out2,id2,v) ==> k1 = k2
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[] >> rpt strip_tac >>
  Cases_on `h0 = k1` >> Cases_on `h0 = k2` >>
  gvs[] >> metis_tac[ao_named_lookup_value]
QED

Theorem ao_cmp_flip_apply_inst_outputs:
  FLAT (MAP (\i. i.inst_outputs) (ao_cmp_flip_apply_inst flips removes named inst)) =
    (case ALOOKUP flips inst.inst_id of
       SOME _ => []
     | NONE => if MEM inst.inst_id removes then [] else
         case ALOOKUP named inst.inst_id of
           NONE => [] | SOME (out,id,v) => [v]) ++ inst.inst_outputs
Proof
  rewrite_tac[ao_cmp_flip_apply_inst_def] >>
  Cases_on `ALOOKUP flips inst.inst_id` >> simp[]
  >- (Cases_on `MEM inst.inst_id removes` >> simp[] >>
      Cases_on `ALOOKUP named inst.inst_id` >> simp[] >>
      PairCases_on `x` >> simp[]) >>
  PairCases_on `x` >> simp[]
QED

Theorem ao_cmp_flip_apply_inst_output_mem:
  MEM v (FLAT (MAP (\i. i.inst_outputs)
    (ao_cmp_flip_apply_inst flips removes named inst))) ==>
  MEM v inst.inst_outputs \/
  ?out id. ALOOKUP named inst.inst_id = SOME (out,id,v)
Proof
  rewrite_tac[ao_cmp_flip_apply_inst_outputs] >>
  Cases_on `ALOOKUP flips inst.inst_id` >> simp[] >>
  Cases_on `MEM inst.inst_id removes` >> simp[] >>
  Cases_on `ALOOKUP named inst.inst_id` >> simp[] >>
  PairCases_on `x` >> simp[] >> metis_tac[]
QED

Theorem ao_cmp_flip_apply_output_mem:
  MEM v (FLAT (MAP (\i. i.inst_outputs)
    (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) xs)))) ==>
  MEM v (FLAT (MAP (\i. i.inst_outputs) xs)) \/
  ?inst out id. MEM inst xs /\ ALOOKUP named inst.inst_id = SOME (out,id,v)
Proof
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> rename1 `MEM i (ao_cmp_flip_apply_inst flips removes named inst)` >>
  `MEM v (FLAT (MAP (\i. i.inst_outputs)
     (ao_cmp_flip_apply_inst flips removes named inst)))` by
    (simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  drule ao_cmp_flip_apply_inst_output_mem >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem ao_cmp_flip_apply_output_disjoint:
  DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs) xs))) /\
  DISJOINT V (set (MAP (\(a,(out,id,v)). v) named)) ==>
  DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs)
    (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) xs)))))
Proof
  simp[DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  drule ao_cmp_flip_apply_output_mem >>
  metis_tac[ao_named_lookup_value]
QED

Theorem ao_cmp_flip_apply_lookup_fresh:
  ALL_DISTINCT (MAP (\(a,(out,id,v)). v) named) /\
  DISJOINT (set (MAP (\(a,(out,id,v)). v) named))
    (set (FLAT (MAP (\i. i.inst_outputs) xs))) /\
  ALOOKUP named key = SOME (out,id,v) /\
  ~MEM key (MAP (\i. i.inst_id) xs) ==>
  ~MEM v (FLAT (MAP (\i. i.inst_outputs)
    (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) xs))))
Proof
  simp[DISJOINT_DEF, EXTENSION] >> rpt strip_tac >>
  drule ao_cmp_flip_apply_output_mem >> strip_tac
  >- metis_tac[ao_named_lookup_value] >>
  `key = inst.inst_id` by metis_tac[ao_named_lookup_injective] >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem ao_cmp_flip_apply_inst_output_shape:
  FLAT (MAP (\i. i.inst_outputs) (ao_cmp_flip_apply_inst flips removes named inst)) =
    inst.inst_outputs \/
  ?out id v. ALOOKUP named inst.inst_id = SOME (out,id,v) /\
    FLAT (MAP (\i. i.inst_outputs) (ao_cmp_flip_apply_inst flips removes named inst)) =
      v :: inst.inst_outputs
Proof
  rewrite_tac[ao_cmp_flip_apply_inst_outputs] >>
  Cases_on `ALOOKUP flips inst.inst_id` >> simp[] >>
  Cases_on `MEM inst.inst_id removes` >> simp[] >>
  Cases_on `ALOOKUP named inst.inst_id` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

Theorem ao_cmp_flip_apply_insts_ssa:
  !xs.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
    ALL_DISTINCT (MAP (\(a,(out,id,v)). v) named) /\
    DISJOINT (set (MAP (\(a,(out,id,v)). v) named))
      (set (FLAT (MAP (\i. i.inst_outputs) xs))) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) xs))))
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[MAP_APPEND, ALL_DISTINCT_APPEND] >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) xs))))` by
    (first_x_assum irule >> simp[DISJOINT_SYM]) >>
  `DISJOINT (set h.inst_outputs)
    (set (FLAT (MAP (\i. i.inst_outputs)
      (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) xs)))))` by
    (irule ao_cmp_flip_apply_output_disjoint >>
     gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  mp_tac (Q.INST [`inst` |-> `h`] ao_cmp_flip_apply_inst_output_shape) >>
  strip_tac >> gvs[DISJOINT_DEF, EXTENSION]
  >- metis_tac[] >>
  `~MEM v (FLAT (MAP (\i. i.inst_outputs)
    (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) xs))))` by
    (irule ao_cmp_flip_apply_lookup_fresh >>
     simp[DISJOINT_DEF, EXTENSION] >>
     conj_tac >- (qexistsl [`id`,`h.inst_id`,`out`] >> simp[]) >>
     metis_tac[]) >>
  gvs[] >> metis_tac[ao_named_lookup_value]
QED

Theorem ao_cmp_flip_apply_fn_insts:
  fn_insts (ao_cmp_flip_apply_fn flips removes named fn) =
    FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) (fn_insts fn))
Proof
  `!bbs. fn_insts_blocks
    (MAP (\bb. bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) bbs) =
    FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) (fn_insts_blocks bbs))` by
    (Induct >> simp[fn_insts_blocks_def, MAP_APPEND]) >>
  simp[ao_cmp_flip_apply_fn_def, fn_insts_def]
QED

Theorem ao_cmp_flip_apply_fn_ssa:
  ssa_form fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\(a,(out,id,v)). v) named) /\
  DISJOINT (set (MAP (\(a,(out,id,v)). v) named))
    (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))) ==>
  ssa_form (ao_cmp_flip_apply_fn flips removes named fn)
Proof
  rewrite_tac[ssa_form_def, ao_cmp_flip_apply_fn_insts] >>
  strip_tac >> irule ao_cmp_flip_apply_insts_ssa >> simp[]
QED

Theorem ao_cmp_flip_function_supply_ssa:
  ao_cmp_flip_function_supply dfg s fn = (fn',t) /\
  ssa_form fn /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) SUBSET set s.irs_used_vars ==>
  ssa_form fn'
Proof
  rewrite_tac[ao_cmp_flip_function_supply_def] >>
  Cases_on `ao_cmp_flip_scan dfg (fn_insts fn)` >>
  PairCases_on `r` >> simp[] >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  Cases_on `ao_name_inserts_supply s r1` >> simp[] >> strip_tac >> gvs[] >>
  irule ao_cmp_flip_apply_fn_ssa >> simp[] >>
  drule ao_name_inserts_supply_fresh >>
  gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED
