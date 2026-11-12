Theory dftGasInvForwardOrigins
Ancestors
  dftGasInvAliasNormal contextCodegenRel contextCodegenRelProps list rich_list
  dftRunRel venomWf venomInst venomExecSemantics

Theorem inv_alias_resolve_append:
  !xs ys a. inv_alias_prefix (xs ++ ys) ==>
  resolve_block_assigns (xs ++ ys) a =
  resolve_block_assigns ys (resolve_block_assigns xs a)
Proof
  Induct >- simp[resolve_block_assigns_def] >>
  simp[inv_alias_prefix_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `a` >> simp[resolve_block_assigns_def] >>
  rename1 `Var v` >>
  Cases_on `MEM v h.inst_outputs` >> simp[]
  >- (Cases_on `h.inst_opcode = ASSIGN /\ h.inst_outputs = [v] /\
                LENGTH h.inst_operands = 1` >> simp[] >>
      sym_tac >> irule resolve_block_assigns_no_write >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[EVERY_APPEND] >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem inv_forward_take_split[local]:
  i < j /\ i < LENGTH xs ==>
  TAKE j xs = TAKE i xs ++ [EL i xs] ++
    TAKE (j - SUC i) (DROP (SUC i) xs)
Proof
  map_every qid_spec_tac [`j`, `i`] >> Induct_on `xs` >>
  Cases_on `i` >> Cases_on `j` >> simp[]
QED

Theorem inv_forward_interval_copies[local]:
  revert_forward_pair bb i j /\ EVERY inst_wf bb.bb_instructions ==>
  EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1 /\
              LENGTH a.inst_operands = 1)
    (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)))
Proof
  strip_tac >>
  `i < j /\ j < LENGTH bb.bb_instructions` by
    gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
  simp[EVERY_REVERSE, EVERY_EL, LENGTH_TAKE, LENGTH_DROP] >>
  qx_gen_tac `k` >> strip_tac >> gvs[LENGTH_TAKE, LENGTH_DROP] >>
  `k + SUC i < LENGTH bb.bb_instructions` by gvs[LENGTH_DROP] >>
  `inst_wf (EL (k + SUC i) bb.bb_instructions)` by
    metis_tac[EVERY_EL] >>
  `i < k + SUC i /\ k + SUC i < j` by decide_tac >>
  `get_instruction bb (k + SUC i) =
    SOME (EL (k + SUC i) bb.bb_instructions)` by simp[get_instruction_def] >>
  ` (EL (k + SUC i) bb.bb_instructions).inst_opcode = ASSIGN` by
    metis_tac[revert_forward_pair_def] >>
  simp[EL_TAKE, EL_DROP] >> gvs[inst_wf_def]
QED

Theorem inv_forward_source_origins:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [p;src;n] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [q;m] ==>
  resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) src = Lit 0w /\
  resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) p =
  resolve_block_assigns (REVERSE (TAKE j bb.bb_instructions)) q /\
  resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) n =
  resolve_block_assigns (REVERSE (TAKE j bb.bb_instructions)) m
Proof
  strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `i < j /\ i < LENGTH bb.bb_instructions /\
    copy = EL i bb.bb_instructions /\ copy.inst_opcode = RETURNDATACOPY` by
    gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
  `inst_wf copy` by metis_tac[EVERY_EL] >>
  `copy.inst_outputs = []` by gvs[inst_wf_def] >>
  `TAKE j bb.bb_instructions = TAKE i bb.bb_instructions ++ [copy] ++
    TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)` by
    metis_tac[inv_forward_take_split] >>
  drule_all inv_forward_interval_copies >> strip_tac >>
  `!a. resolve_block_assigns (REVERSE (TAKE j bb.bb_instructions)) a =
     resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions))
       (resolve_block_assigns
          (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions))) a)` by
    (gen_tac >> asm_rewrite_tac[REVERSE_APPEND] >>
     drule resolve_block_assigns_copy_append >>
     disch_then (fn th => rewrite_tac[th]) >>
     simp[resolve_block_assigns_def] >>
     Cases_on `resolve_block_assigns
       (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions))) a` >>
     gvs[resolve_block_assigns_def]) >>
  drule_all inv_alias_source_prefix_normal >>
  disch_then (fn th => gvs[revert_forward_pair_def, th])
QED
