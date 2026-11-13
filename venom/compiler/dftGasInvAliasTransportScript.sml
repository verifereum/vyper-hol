Theory dftGasInvAliasTransport
Ancestors
  dftGasInvScheduledAliases dftGasInvAliasPaths dftGasInvForwardOrigins
  dftRunRel dftWf venomWf venomInst contextCodegenRel list rich_list relation

Theorem inv_scheduled_alias_terminal:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  (inv_alias_terminal (dft_block order bb).bb_instructions a b <=>
   inv_alias_terminal bb.bb_instructions a b)
Proof
  strip_tac >>
  `inv_assign_edge (dft_block order bb).bb_instructions =
   inv_assign_edge bb.bb_instructions` by
    (simp[FUN_EQ_THM] >> metis_tac[inv_scheduled_assign_edge]) >>
  simp[inv_alias_terminal_def]
QED

Theorem inv_scheduled_use_resolution:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  get_instruction bb i = SOME inst /\
  get_instruction (dft_block order bb) k = SOME inst /\
  ~is_pseudo inst.inst_opcode /\ MEM a inst.inst_operands ==>
  resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) a =
  resolve_block_assigns
    (REVERSE (TAKE k (dft_block order bb).bb_instructions)) a
Proof
  strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `np_defs_before_uses bb.bb_instructions` by
    metis_tac[wf_ssa_defs_before_uses, dft_fn_rel_def] >>
  `ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) bb.bb_instructions))` by
    metis_tac[inv_block_distinct_outputs, dft_fn_rel_def] >>
  `EVERY inst_wf (dft_block order bb).bb_instructions /\
   ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs)
      (dft_block order bb).bb_instructions)) /\
   np_defs_before_uses (dft_block order bb).bb_instructions` by
    metis_tac[inv_scheduled_inst_wf, inv_scheduled_distinct_outputs,
              inv_scheduled_defs_before_uses] >>
  `i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst /\
   k < LENGTH (dft_block order bb).bb_instructions /\
   EL k (dft_block order bb).bb_instructions = inst` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `inv_alias_terminal bb.bb_instructions a
    (resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) a)` by
    (irule inv_alias_use_endpoint >> simp[] >> metis_tac[]) >>
  `inv_alias_terminal (dft_block order bb).bb_instructions a
    (resolve_block_assigns
      (REVERSE (TAKE k (dft_block order bb).bb_instructions)) a)` by
    (irule inv_alias_use_endpoint >> simp[] >> metis_tac[]) >>
  metis_tac[inv_scheduled_alias_terminal, inv_alias_terminal_unique]
QED

Theorem inv_scheduled_split_use_resolution:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  get_instruction bb i = SOME inst /\
  (dft_block order bb).bb_instructions = pre ++ inst::post /\
  ~is_pseudo inst.inst_opcode /\ MEM a inst.inst_operands ==>
  resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) a =
  resolve_block_assigns (REVERSE pre) a
Proof
  strip_tac >>
  `get_instruction (dft_block order bb) (LENGTH pre) = SOME inst` by
    simp[get_instruction_def, EL_APPEND2] >>
  drule_all inv_scheduled_use_resolution >>
  simp[TAKE_APPEND]
QED

Theorem inv_forward_scheduled_origins:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [p;src;n] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [q;m] /\
  (dft_block [] bb).bb_instructions = pre ++ [copy] ++ mid ++ [rev] ++ post ==>
  resolve_block_assigns (REVERSE pre) src = Lit 0w /\
  resolve_block_assigns (REVERSE pre) p =
    resolve_block_assigns (REVERSE (pre ++ [copy] ++ mid)) q /\
  resolve_block_assigns (REVERSE pre) n =
    resolve_block_assigns (REVERSE (pre ++ [copy] ++ mid)) m
Proof
  strip_tac >>
  `copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT` by
    gvs[revert_forward_pair_def] >>
  `!a. MEM a copy.inst_operands ==>
    resolve_block_assigns (REVERSE (TAKE i bb.bb_instructions)) a =
    resolve_block_assigns (REVERSE pre) a` by
    (rpt strip_tac >> irule inv_scheduled_split_use_resolution >>
     conj_tac
     >- (qexistsl [`copy`, `[]`, `mid ++ [rev] ++ post`] >>
         simp[is_pseudo_def]) >> metis_tac[]) >>
  `!a. MEM a rev.inst_operands ==>
    resolve_block_assigns (REVERSE (TAKE j bb.bb_instructions)) a =
    resolve_block_assigns (REVERSE (pre ++ [copy] ++ mid)) a` by
    (rpt strip_tac >> irule inv_scheduled_split_use_resolution >>
     conj_tac
     >- (qexistsl [`rev`, `[]`, `post`] >>
         simp[is_pseudo_def, APPEND_ASSOC]) >> metis_tac[]) >>
  drule_all inv_forward_source_origins >> strip_tac >>
  metis_tac[MEM]
QED
