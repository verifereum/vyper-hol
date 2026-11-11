Theory dftGasInvInitializedTerminals
Ancestors
  dftGasInvForwardTerminals dftGasInvAliasPaths dftGasInvStackLineage
  dftGasInvSchedulerProvenance dftStructural dftTopoSort dftDefs
  dftIdempotent passSharedDefs dftWf dftRunRel dftCorrectness venomWf contextCodegenRel list rich_list relation venomInst arithmetic

Theorem inv_output_source_recover:
  dfs_good_state bi st /\ ALL_DISTINCT (MAP (\z. z.inst_id) bi) /\
  MEM inst bi /\ flip_operands inst = inst /\
  MEM inst.inst_id (MAP (\z. z.inst_id) st.ds_output) ==>
  MEM inst st.ds_output
Proof
  strip_tac >>
  `?emitted. MEM emitted st.ds_output /\ emitted.inst_id = inst.inst_id` by
    (gvs[MEM_MAP] >> metis_tac[]) >>
  `from_block bi emitted` by
    (gvs[dfs_good_state_def, EVERY_MEM] >> metis_tac[]) >>
  gvs[from_block_def] >>
  `!x y. MEM x bi /\ MEM y bi /\ x.inst_id = y.inst_id ==> x = y` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
     qid_spec_tac `bi` >> Induct >> simp[MEM_MAP] >> rpt strip_tac >>
     gvs[] >> metis_tac[]) >>
  metis_tac[flip_operands_inst_id]
QED

Theorem inv_single_operand_unflipped:
  LENGTH inst.inst_operands = 1 ==> flip_operands inst = inst
Proof
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >> simp[flip_operands_def]
QED

Theorem inv_emitted_assign_path_producer[local]:
  (!use a prod. MEM use st.ds_output /\ MEM a use.inst_operands /\
    operand_producer bi a = SOME prod /\ MEM prod bi /\
    ~is_pseudo prod.inst_opcode ==>
    MEM prod.inst_id (MAP (\z. z.inst_id) st.ds_output) /\
    MEM prod.inst_id st.ds_visited /\
    ~MEM prod.inst_id (stack_emit_ids st.ds_stack)) /\
  dfs_good_state bi st /\ ALL_DISTINCT (MAP (\z. z.inst_id) bi) ==>
  !a b. RTC (inv_assign_edge bi) a b ==>
  !use prod. MEM use st.ds_output /\ MEM a use.inst_operands /\
    operand_producer bi b = SOME prod /\ MEM prod bi /\
    ~is_pseudo prod.inst_opcode ==>
  MEM prod.inst_id (MAP (\z. z.inst_id) st.ds_output) /\
  MEM prod.inst_id st.ds_visited /\
  ~MEM prod.inst_id (stack_emit_ids st.ds_stack)
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT >> conj_tac
  >- metis_tac[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `inv_assign_edge _ _ _` mp_tac >>
  simp[inv_assign_edge_def] >> strip_tac >> gvs[] >>
  rename1 `producing_inst bi v = SOME assign` >>
  `MEM assign bi` by metis_tac[producing_inst_unique] >>
  `MEM assign.inst_id (MAP (\z. z.inst_id) st.ds_output)` by
    (qpat_assum `!use a prod. _` (irule o cj 1) >>
     simp[is_pseudo_def] >> qexists `Var v` >>
     simp[operand_producer_def] >> metis_tac[]) >>
  `MEM assign st.ds_output` by
    (irule inv_output_source_recover >>
     simp[inv_single_operand_unflipped] >> metis_tac[]) >>
  first_x_assum irule >> qexists `assign` >> simp[]
QED

Theorem inv_initialized_use_terminal:
  eda_wf eda bi /\ eda_topo_compatible bi eda order /\
  np_defs_before_uses bi /\ ALL_DISTINCT (MAP (\z. z.inst_id) bi) /\
  bi <> [] /\
  (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)) /\ EVERY (\z. MEM z bi) entries /\
  st = inv_line_state bi order eda om do_flip entries ticks /\
  MEM use st.ds_output /\ MEM a use.inst_operands /\
  inv_terminal_producer bi a prod /\ ~is_pseudo prod.inst_opcode ==>
  MEM prod.inst_id (MAP (\z. z.inst_id) st.ds_output) /\
  MEM prod.inst_id st.ds_visited /\
  ~MEM prod.inst_id (stack_emit_ids st.ds_stack)
Proof
  strip_tac >>
  `dfs_good_state bi st` by
    (gvs[inv_line_state_def] >> irule dfs_funpow_preserves_good >>
     simp[init_dfs_state_good]) >>
  `!use a prod. MEM use st.ds_output /\ MEM a use.inst_operands /\
    operand_producer bi a = SOME prod /\ MEM prod bi /\
    ~is_pseudo prod.inst_opcode ==>
    MEM prod.inst_id (MAP (\z. z.inst_id) st.ds_output) /\
    MEM prod.inst_id st.ds_visited /\
    ~MEM prod.inst_id (stack_emit_ids st.ds_stack)` by
    (rpt gen_tac >> strip_tac >> Cases_on `a'` >>
     gvs[operand_producer_def] >>
     irule inv_scheduler_producer_provenance >>
     gvs[inv_line_state_def] >> metis_tac[]) >>
  gvs[inv_terminal_producer_def, inv_alias_terminal_def] >>
  `MEM prod bi` by
    (Cases_on `b` >> gvs[operand_producer_def] >>
     metis_tac[producing_inst_unique]) >>
  irule inv_emitted_assign_path_producer >>
  simp[] >> qexistsl [`a`, `b`, `bi`, `use`] >> simp[] >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem inv_dft_initialized_use_terminal:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) ticks /\
  MEM use st.ds_output /\ MEM a use.inst_operands /\
  inv_terminal_producer bb.bb_instructions a prod /\
  ~is_pseudo prod.inst_opcode ==>
  MEM prod.inst_id (MAP (\z. z.inst_id) st.ds_output) /\
  MEM prod.inst_id st.ds_visited /\
  ~MEM prod.inst_id (stack_emit_ids st.ds_stack)
Proof
  strip_tac >>
  `wf_ssa fn /\ wf_function fn` by gvs[dft_fn_rel_def] >>
  `bb_well_formed bb /\
   ALL_DISTINCT (MAP (\z. z.inst_id) bb.bb_instructions)` by
    metis_tac[wf_function_def, EVERY_MEM, bb_inst_ids_distinct] >>
  `np_defs_before_uses bb.bb_instructions` by
    metis_tac[wf_ssa_defs_before_uses] >>
  `eda_topo_compatible bb.bb_instructions (dft_eda bb.bb_instructions) []` by
    (irule eda_topo_compatible_dft_eda >> gvs[bb_well_formed_def]) >>
  `eda_wf (dft_eda bb.bb_instructions) bb.bb_instructions` by
    simp[dft_eda_wf] >>
  `EVERY (\z. MEM z bb.bb_instructions)
     (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions))` by
    simp[EVERY_MEM, entry_instructions_mem] >>
  fs[bb_well_formed_def] >> drule_all inv_initialized_use_terminal >> simp[]
QED

Theorem inv_forward_initialized_terminals:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [p;src;n] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [q;m] /\
  st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) ticks /\
  MEM copy st.ds_output /\
  (inv_terminal_producer bb.bb_instructions q prod \/
   inv_terminal_producer bb.bb_instructions m prod) /\
  ~is_pseudo prod.inst_opcode ==>
  MEM prod.inst_id (MAP (\z. z.inst_id) st.ds_output) /\
  MEM prod.inst_id st.ds_visited /\
  ~MEM prod.inst_id (stack_emit_ids st.ds_stack)
Proof
  strip_tac >>
  `inv_terminal_producer bb.bb_instructions p prod \/
   inv_terminal_producer bb.bb_instructions n prod` by
    (drule_all inv_forward_terminal_producers >> metis_tac[]) >>
  irule inv_dft_initialized_use_terminal >>
  metis_tac[MEM]
QED

(* Boundary checks: no local producer is invented for external/literal
   origins, and the pseudo origin is not required to appear in output. *)
Definition inv_terminal_check_block_def:
  inv_terminal_check_block root =
    [mk_inst 0 ASSIGN [root] ["alias"];
     mk_inst 1 REVERT [Var "alias"; Lit 0w] []]
End

Definition inv_terminal_check_state_def:
  inv_terminal_check_state bi =
    inv_line_state bi [] (dft_eda bi) (build_offspring_map bi []) T
      (entry_instructions bi [] (dft_eda bi)) 30
End

Theorem inv_external_terminal_boundary:
  resolve_block_assigns
    (REVERSE (TAKE 1 (inv_terminal_check_block (Var "external"))))
    (Var "alias") = Var "external" /\
  operand_producer (inv_terminal_check_block (Var "external"))
    (Var "external") = NONE /\
  MAP (\z. z.inst_id)
    (inv_terminal_check_state (inv_terminal_check_block (Var "external"))).ds_output =
      [0;1]
Proof
  EVAL_TAC
QED

Theorem inv_literal_terminal_boundary:
  resolve_block_assigns
    (REVERSE (TAKE 1 (inv_terminal_check_block (Lit 0w))))
    (Var "alias") = Lit 0w /\
  operand_producer (inv_terminal_check_block (Lit 0w)) (Lit 0w) = NONE /\
  MAP (\z. z.inst_id)
    (inv_terminal_check_state (inv_terminal_check_block (Lit 0w))).ds_output = [0;1]
Proof
  EVAL_TAC
QED

Definition inv_pseudo_terminal_block_def:
  inv_pseudo_terminal_block =
    mk_inst 2 PARAM [Lit 0w] ["external"] ::
    inv_terminal_check_block (Var "external")
End

Theorem inv_pseudo_terminal_boundary:
  EVERY inst_wf inv_pseudo_terminal_block /\
  resolve_block_assigns (REVERSE (TAKE 2 inv_pseudo_terminal_block))
    (Var "alias") = Var "external" /\
  operand_producer inv_pseudo_terminal_block (Var "external") =
    SOME (mk_inst 2 PARAM [Lit 0w] ["external"]) /\
  is_pseudo PARAM /\
  MAP (\z. z.inst_id)
    (inv_terminal_check_state inv_pseudo_terminal_block).ds_output = [0;1]
Proof
  EVAL_TAC
QED
