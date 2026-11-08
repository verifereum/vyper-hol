(* Logical stack effects used to align deep duplication with prefix execution.
   These identities do not assume that spilled values are distinct. *)
Theory doDupModel
Ancestors
  doSwapSim mixedPrefixSim strongPrefixSim stackModel stackPlanOps
  stackPlanTypes list rich_list arithmetic

Theorem map_el_genlist_identity:
  !xs. MAP (\i. EL i xs) (GENLIST I (LENGTH xs)) = xs
Proof
  simp[LIST_EQ_REWRITE, EL_MAP, EL_GENLIST]
QED

Theorem dup_restore_schedule_map:
  !xs. MAP (\i. EL i xs) (dup_restore_indices (LENGTH xs)) =
    if LENGTH xs <= 16 then TL (REVERSE xs) ++ TAKE 1 (REVERSE xs)
    else REVERSE xs
Proof
  rw[dup_restore_indices_def] >>
  simp[MAP_TL, MAP_TAKE, MAP_REVERSE, map_el_genlist_identity]
QED

Theorem swap_front_after_prefix:
  !top value mid rest.
    LUPDATE top (SUC (LENGTH mid))
      (LUPDATE value 0 (top::(mid ++ value::rest))) =
    value::(mid ++ top::rest)
Proof
  rpt gen_tac >> simp_tac std_ss [LUPDATE_def] >>
  mp_tac (Q.SPECL [`mid`,`value::rest`,`LENGTH mid`,`top`]
    LUPDATE_APPEND2) >> simp[LUPDATE_def]
QED

Theorem dup_restore_front_stack:
  !xs top rest.
    xs <> [] /\ LENGTH xs <= 16 ==>
    let restored =
      REVERSE (MAP (\i. EL i xs) (dup_restore_indices (LENGTH xs))) ++
        top::rest
    in LUPDATE (HD restored) (LENGTH xs)
         (LUPDATE (EL (LENGTH xs) restored) 0 restored) =
       top::(xs ++ rest)
Proof
  rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) [dup_restore_schedule_map] >>
  Cases_on `REVERSE xs` >> gvs[] >>
  rename1 `REVERSE xs = last::mid` >>
  `xs = REVERSE mid ++ [last]` by
    (qpat_x_assum `REVERSE xs = _` (mp_tac o AP_TERM ``REVERSE``) >>
     pure_rewrite_tac [REVERSE_REVERSE, REVERSE_DEF, SNOC_APPEND] >>
     simp[]) >> gvs[] >>
  mp_tac (Q.SPECL [`last`,`top`,`REVERSE mid`,`rest`]
    swap_front_after_prefix) >>
  simp[EL_APPEND_EQN, GSYM ADD1]
QED

Theorem stack_swap_one_snoc_pair:
  !xs top value.
    stack_swap 1 (SNOC value (SNOC top xs)) =
    SNOC top (SNOC value xs)
Proof
  rpt gen_tac >>
  simp[stack_swap_def, LIST_EQ_REWRITE, EL_LUPDATE, EL_SNOC] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[EL_SNOC] >>
  simp[SNOC_APPEND, EL_APPEND_EQN, ADD1]
QED

Theorem restore_below_top_model:
  !offsets initial_fmp lo ps top.
    apply_prefix_ops initial_fmp lo
      (FLAT (MAP (\off. [SORestore off; SOSwap 1]) offsets))
      (ps with ps_stack := SNOC top ps.ps_stack) =
    let restored = apply_prefix_ops initial_fmp lo (MAP SORestore offsets) ps
    in restored with ps_stack := SNOC top restored.ps_stack
Proof
  Induct >> rpt gen_tac
  >- simp[apply_prefix_ops_def] >>
  simp[apply_prefix_ops_def, apply_prefix_op_def, apply_simple_op_def,
       stack_push_def, stack_swap_one_snoc_pair] >>
  first_x_assum (qspecl_then [`initial_fmp`,`lo`,
    `ps with <|
       ps_stack := SNOC (spill_lookup h ps.ps_spilled) ps.ps_stack;
       ps_spilled := ps.ps_spilled \\ spill_lookup h ps.ps_spilled|>`,
    `top`] mp_tac) >> simp[]
QED

Theorem do_dup_spilled:
  !dist ps. (SND (do_dup dist ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[do_dup_def, LET_THM] >>
  IF_CASES_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[])
QED

Theorem restore_below_top_effect:
  !items offsets initial_fmp lo ps top.
    LENGTH items = LENGTH offsets /\ ALL_DISTINCT items /\
    (!k. k < LENGTH items ==>
       FLOOKUP ps.ps_spilled (EL k items) = SOME (EL k offsets)) /\
    (!op1 off1 op2 off2.
       FLOOKUP ps.ps_spilled op1 = SOME off1 /\
       FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1) ==>
    let restored = apply_prefix_ops initial_fmp lo
      (FLAT (MAP (\off. [SORestore off; SOSwap 1]) offsets))
      (ps with ps_stack := SNOC top ps.ps_stack)
    in restored.ps_stack = SNOC top (ps.ps_stack ++ items) /\
       restored.ps_spilled = FOLDL (\sp item. sp \\ item) ps.ps_spilled items /\
       restored.ps_alloc = ps.ps_alloc
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`items`,`offsets`,`initial_fmp`,`lo`,`ps`]
    apply_restore_ops_effect) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  simp[restore_below_top_model]
QED

Theorem do_dup_preserves_absent_operand:
  !dist ps operand.
    dist < LENGTH ps.ps_stack /\ ~MEM operand ps.ps_stack /\
    operand NOTIN FDOM ps.ps_spilled ==>
    ~MEM operand (SND (do_dup dist ps)).ps_stack /\
    operand NOTIN FDOM (SND (do_dup dist ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  simp[do_dup_stack, do_dup_spilled, stack_dup_def] >>
  `MEM (stack_peek dist ps.ps_stack) ps.ps_stack` by
    simp[stack_peek_def, EL_MEM] >> metis_tac[]
QED
