(* Exact memory-check boundaries of the sealed sparse-store observer. *)
Theory storeSlotsObserverMemory
Ancestors
  exprSimAbiGasBridge fragGasPathMem fragExec memSafeRun contextCodegenRel
  o1ContractSimplifyCfgSrcFrame venomInst venomExecSemantics venomState
  compileEnv list rich_list arithmetic

Theorem observer_revert_pair_before_stop[local]:
  revert_forward_pair
    <|bb_label := lbl; bb_instructions := xs ++ [mk_inst id STOP [] []]|> i j ==>
  j < LENGTH xs
Proof
  simp[revert_forward_pair_def, get_instruction_def] >> strip_tac >>
  Cases_on `j < LENGTH xs` >> simp[] >>
  gvs[EL_APPEND_EQN, mk_inst_def] >>
  `j - LENGTH xs = 0` by decide_tac >> gvs[]
QED

Theorem observer_revert_pair_prefix[local]:
  isPREFIX xs bb.bb_instructions /\
  revert_forward_pair
    <|bb_label := lbl; bb_instructions := xs ++ [mk_inst id STOP [] []]|> i j ==>
  revert_forward_pair bb i j
Proof
  strip_tac >> drule observer_revert_pair_before_stop >> strip_tac >>
  drule scfg_revert_forward_pair_take >>
  disch_then (qspec_then `LENGTH xs` mp_tac) >>
  simp[TAKE_APPEND] >> strip_tac >>
  fs[IS_PREFIX_APPEND] >>
  drule scfg_revert_forward_pair_suffix >>
  disch_then (qspec_then `l` mp_tac) >>
  simp[revert_forward_pair_def, get_instruction_def] >> metis_tac[]
QED

Theorem observer_memory_check_transfer:
  fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  (revert_forward_at bb idx \/ mem_safe_step fuel ctx inst s) ==>
  ?original. lookup_block lbl fn.fn_blocks = SOME original /\
    (revert_forward_at original idx \/ mem_safe_step fuel ctx inst s)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[] >> fs[fn_has_code_def] >>
      fs[revert_forward_at_def] >>
      metis_tac[observer_revert_pair_prefix]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED
