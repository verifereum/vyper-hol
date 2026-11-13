Theory dftGasInvAliasNormal
Ancestors
  contextCodegenRel contextCodegenRelProps dftGasInvAlias venomInst list rich_list
  dftScheduleOrder dftWf dftRunRel venomWf dftTopoSort

Theorem inv_alias_resolve_opaque:
  !xs a v.
  EVERY (\i. i.inst_opcode = ASSIGN ==> ~MEM (Var v) i.inst_operands) xs /\
  a <> Var v ==>
  resolve_block_assigns xs a <> Var v
Proof
  Induct >> simp[resolve_block_assigns_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `a` >> simp[resolve_block_assigns_def] >>
  rename1 `Var name <> Var v` >>
  Cases_on `MEM name h.inst_outputs` >> simp[] >>
  Cases_on `h.inst_opcode = ASSIGN /\ h.inst_outputs = [name] /\
            LENGTH h.inst_operands = 1` >> simp[] >>
  first_x_assum irule >> gvs[] >>
  Cases_on `h.inst_operands` >> gvs[]
QED

Definition inv_alias_prefix_def:
  (inv_alias_prefix [] <=> T) /\
  (inv_alias_prefix (inst :: rest) <=> inv_alias_prefix rest /\
    !v. MEM v inst.inst_outputs ==>
      EVERY (\i. ~MEM v i.inst_outputs /\
        (i.inst_opcode = ASSIGN ==> ~MEM (Var v) i.inst_operands)) rest)
End

Theorem inv_alias_resolve_step:
  step_back_assign inst a = SOME b ==>
  resolve_block_assigns (inst :: rest) a = resolve_block_assigns rest b
Proof
  Cases_on `a` >> simp[step_back_assign_def, resolve_block_assigns_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >> gvs[]
QED

Theorem inv_alias_clobber_opaque:
  (!v. MEM v inst.inst_outputs ==>
    EVERY (\i. ~MEM v i.inst_outputs /\
      (i.inst_opcode = ASSIGN ==> ~MEM (Var v) i.inst_operands)) rest) /\
  step_back_assign inst a = NONE /\ a <> b ==>
  resolve_block_assigns (inst :: rest) a <>
  resolve_block_assigns (inst :: rest) b
Proof
  strip_tac >> Cases_on `a` >> gvs[step_back_assign_def] >>
  rename1 `MEM name inst.inst_outputs` >>
  `resolve_block_assigns (inst :: rest) (Var name) = Var name` by
    (simp[resolve_block_assigns_def] >> metis_tac[]) >>
  simp[] >> Cases_on `b` >> simp[resolve_block_assigns_def] >>
  rename1 `Var name <> Var other` >>
  Cases_on `MEM other inst.inst_outputs` >> simp[]
  >- (IF_CASES_TAC >> gvs[]) >>
  once_rewrite_tac[EQ_SYM_EQ] >> irule inv_alias_resolve_opaque >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem inv_alias_prefix_normal:
  !xs a b. inv_alias_prefix xs ==>
  (same_after_assigns xs a b <=>
    resolve_block_assigns xs a = resolve_block_assigns xs b)
Proof
  Induct >- simp[inv_alias_prefix_def, same_after_assigns_def,
                   resolve_block_assigns_def] >>
  simp[inv_alias_prefix_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `a = b` >- gvs[] >>
  simp[same_after_assigns_def] >>
  Cases_on `step_back_assign h a`
  >- (simp[] >> metis_tac[inv_alias_clobber_opaque]) >>
  Cases_on `step_back_assign h b`
  >- (simp[] >> metis_tac[inv_alias_clobber_opaque]) >>
  gvs[] >> metis_tac[inv_alias_resolve_step]
QED

Theorem inv_alias_prefix_ordered:
  !xs.
  (!i j v. i < j /\ j < LENGTH xs /\
    MEM v (EL j xs).inst_outputs ==>
    ~MEM v (EL i xs).inst_outputs /\
    ((EL i xs).inst_opcode = ASSIGN ==>
      ~MEM (Var v) (EL i xs).inst_operands)) ==>
  inv_alias_prefix (REVERSE xs)
Proof
  Induct using SNOC_INDUCT >- simp[inv_alias_prefix_def] >>
  simp[REVERSE_SNOC, inv_alias_prefix_def] >> rpt strip_tac
  >- (first_x_assum irule >> rpt strip_tac >>
      qpat_x_assum `!i j v. _` (qspecl_then [`i`, `j`, `v`] mp_tac) >>
      simp[SNOC_APPEND, EL_APPEND_EQN]) >>
  gvs[EVERY_REVERSE, EVERY_MEM] >> gen_tac >> disch_tac >>
  rename1 `MEM inst xs` >>
  `?idx. idx < LENGTH xs /\ inst = EL idx xs` by metis_tac[MEM_EL] >>
  qpat_x_assum `!i j v. _`
    (qspecl_then [`idx`, `LENGTH xs`, `v`] mp_tac) >>
  simp[SNOC_APPEND, EL_APPEND_EQN]
QED

Theorem inv_alias_output_index_unique:
  !xs i j v.
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) xs)) /\
  i < LENGTH xs /\ j < LENGTH xs /\
  MEM v (EL i xs).inst_outputs /\ MEM v (EL j xs).inst_outputs ==>
  i = j
Proof
  Induct >- simp[] >> rpt gen_tac >>
  Cases_on `i` >> Cases_on `j` >>
  simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]
QED

Theorem inv_alias_chronological_prefix:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
  (!j v prod. j < LENGTH xs /\ (EL j xs).inst_opcode = ASSIGN /\
    MEM (Var v) (EL j xs).inst_operands /\
    producing_inst xs v = SOME prod ==>
    ?k. k < j /\ EL k xs = prod) ==>
  inv_alias_prefix (REVERSE xs)
Proof
  strip_tac >>
  irule inv_alias_prefix_ordered >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (strip_tac >> `i < LENGTH xs` by decide_tac >>
      `i = j` by metis_tac[inv_alias_output_index_unique] >> decide_tac) >>
  rpt strip_tac >>
  `producing_inst xs v = SOME (EL j xs)` by
    (irule producing_inst_distinct_outputs >> simp[EL_MEM]) >>
  `?k. k < i /\ EL k xs = EL j xs` by
    (qpat_x_assum `!j v prod. _`
       (qspecl_then [`i`, `v`, `EL j xs`] mp_tac) >> simp[]) >>
  `k < LENGTH xs` by decide_tac >>
  `k = j` by metis_tac[inv_alias_output_index_unique] >>
  gvs[]
QED

Theorem inv_alias_chronological_normal:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
  (!j v prod. j < LENGTH xs /\ (EL j xs).inst_opcode = ASSIGN /\
    MEM (Var v) (EL j xs).inst_operands /\
    producing_inst xs v = SOME prod ==>
    ?k. k < j /\ EL k xs = prod) ==>
  (same_after_assigns (REVERSE xs) a b <=>
    resolve_block_assigns (REVERSE xs) a =
    resolve_block_assigns (REVERSE xs) b)
Proof
  strip_tac >> irule inv_alias_prefix_normal >>
  irule inv_alias_chronological_prefix >> metis_tac[]
QED

Theorem inv_alias_prefix_suffix:
  !xs ys. inv_alias_prefix (xs ++ ys) ==> inv_alias_prefix ys
Proof
  Induct >> simp[inv_alias_prefix_def] >> metis_tac[]
QED

Theorem inv_alias_prefix_take:
  inv_alias_prefix (REVERSE xs) ==>
  inv_alias_prefix (REVERSE (TAKE n xs))
Proof
  strip_tac >>
  `inv_alias_prefix (REVERSE (DROP n xs) ++ REVERSE (TAKE n xs))` by
    simp[GSYM REVERSE_APPEND] >>
  metis_tac[inv_alias_prefix_suffix]
QED

Theorem inv_alias_source_prefix_normal:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  (same_after_assigns (REVERSE (TAKE n bb.bb_instructions)) a b <=>
    resolve_block_assigns (REVERSE (TAKE n bb.bb_instructions)) a =
    resolve_block_assigns (REVERSE (TAKE n bb.bb_instructions)) b)
Proof
  strip_tac >> irule inv_alias_prefix_normal >>
  irule inv_alias_prefix_take >> irule inv_alias_chronological_prefix >>
  `wf_ssa fn /\ wf_function fn` by gvs[dft_fn_rel_def] >>
  `np_defs_before_uses bb.bb_instructions` by
    metis_tac[wf_ssa_defs_before_uses] >>
  conj_tac
  >- (gvs[np_defs_before_uses_def] >> rpt strip_tac >>
      first_x_assum irule >> simp[is_pseudo_def] >> metis_tac[]) >>
  qpat_x_assum `wf_ssa fn` mp_tac >>
  simp[wf_ssa_def, ssa_form_def, fn_insts_def] >> strip_tac >>
  qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND,
                ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* Premise audit for future scheduler consumers:
   - Source TAKE prefixes: inv_alias_source_prefix_normal obtains SSA and
     wf_function from dft_fn_rel; wf_ssa_defs_before_uses requires no extra
     block reachability premise. Only ASSIGN users are queried, not PARAM.
   - Scheduled output: dft_block_suffix_structure gives ID permutation and
     from_block provenance; together with flip_operands_order_fields and
     source SSA these are candidates for distinct scheduled outputs.
     dft_block_suffix_producers supplies output_producer_before for the
     non-pseudo suffix. dft_block_suffix_decomposition exposes the unchanged
     pseudo prefix. These still need composition and restriction to the
     actual emitted prefix; they are not a cross-prefix alias theorem.
   - Equality of source and emitted canonical origins is NOT established
     here. In particular provenance and producer ordering alone do not
     say which source instructions have been emitted above a pending REVERT.
*)
