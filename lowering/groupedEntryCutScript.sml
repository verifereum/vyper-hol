(* The observer records the first exit from the installed entry code. *)
Theory groupedEntryCut
Ancestors
  fragFuelConfinement fragObserverCodeProps exprSimAbiGasBridge groupedRegistrationCounters
  fragFuel fragExec fragGasPath venomInst venomExecSemantics venomState
  venomExecProofs list rich_list relation

Theorem entry_observer_preserves_execution_hyps[local]:
  fn_has_code sa sb fn /\ no_phi_fn fn /\ callees_stable G ctx fn ==>
  no_phi_fn (frag_observer sa sb fn id) /\
  callees_stable G ctx (frag_observer sa sb fn id)
Proof
  strip_tac >> conj_tac >- metis_tac[abi_dyn_observer_no_phi] >>
  simp[callees_stable_def] >> rpt strip_tac >>
  rename1 `i.inst_opcode = INVOKE` >>
  `i.inst_opcode <> STOP` by simp[] >>
  `MEM i (fn_insts fn)` by metis_tac[frag_observer_nonstop_inclusion] >>
  fs[callees_stable_def] >> metis_tac[]
QED

val before_cut = ``\sa sb fn id (s:venom_state).
  IS_SOME (lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks) /\
  (s.vs_current_bb = sb.cs_current_bb ==> s.vs_inst_idx < LENGTH sb.cs_current_insts)``;

Theorem entry_observer_matches_before_cut[local]:
  fn_has_code sa sb fn /\ ^before_cut sa sb fn id s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i ==>
  ?b. lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME b /\
      get_instruction b s.vs_inst_idx = SOME i
Proof
  simp[] >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks` >>
  gvs[] >> drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[fn_has_code_def, IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  qpat_assum `fn_has_code sa sb fn`
    (mp_tac o REWRITE_RULE [fn_has_code_def]) >>
  disch_then (qspec_then `x` mp_tac o cj 1) >> simp[] >> metis_tac[]
QED

Theorem entry_observer_first_exit[local]:
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  ^before_cut sa sb fn id s /\ gas_path_edge ctx fn s n (OK t) /\
  ~(^before_cut sa sb fn id t) /\ ~at_point sb t ==>
  t.vs_inst_idx = 0 /\
  lookup_block t.vs_current_bb (frag_observer sa sb fn id).fn_blocks = NONE
Proof
  simp[] >> strip_tac >>
  drule_all grouped_registration_edge_pc >> strip_tac >>
  Cases_on `is_terminator i.inst_opcode` >> gvs[] >>
  `~t.vs_halted` by metis_tac[gas_path_edge_normal] >>
  fs[at_point_def] >>
  Cases_on `t.vs_current_bb = sb.cs_current_bb` >>
  gvs[frag_observer_cut_lookup] >> decide_tac
QED

Theorem grouped_entry_first_cut:
  frag_fuel Wv {} {} sa sb Kb /\ at_point sa s /\
  sa.cs_current_insts = [] /\
  fn_has_code sa sb fn /\ cs_extends sa sb /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  gas_path ctx fn s n (OK t) ==>
  (?m. at_point sb s /\ gas_path ctx fn s m (OK t)) \/
  (^before_cut sa sb fn id t /\
   RTC (\a b. ^before_cut sa sb fn id a /\
     ?j. gas_path_edge ctx fn a j (OK b)) s t) \/
  ?u v k m.
    RTC (\a b. ^before_cut sa sb fn id a /\
      ?j. gas_path_edge ctx fn a j (OK b)) s u /\
    ^before_cut sa sb fn id u /\ at_point sb v /\
    gas_path_edge ctx fn u k (OK v) /\ gas_path ctx fn v m (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `at_point sb s` >- (disj1_tac >> qexists_tac `n` >> simp[]) >>
  disj2_tac >>
  `!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  `fn_has_code sa sb (frag_observer sa sb fn id)` by metis_tac[frag_observer_has_code_from_labels] >>
  `no_phi_fn (frag_observer sa sb fn id) /\
    callees_stable G ctx (frag_observer sa sb fn id)` by
    metis_tac[entry_observer_preserves_execution_hyps] >>
  qpat_assum `at_point sa s` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  `^before_cut sa sb fn id s` by
    (Cases_on `sa.cs_current_bb = sb.cs_current_bb`
     >- (Cases_on `sb.cs_current_insts`
         >- (fs[] >> metis_tac[at_point_def]) >>
         fs[frag_observer_cut_lookup]) >>
     drule frag_extends_emitted_shape >>
     Cases_on `emitted_blocks sa sb` >> gvs[at_point_def, fn_has_code_def] >>
     `MEM (LAST (h::t')) (h::t')` by simp[MEM_LAST_NOT_NIL] >>
     strip_tac >>
     qpat_assum `!b. _ ==> lookup_block _ (frag_observer sa sb fn id).fn_blocks = _`
       (qspec_then `LAST (h::t')` mp_tac) >>
     fs[] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  mp_tac (BETA_RULE (Q.INST
    [`P` |-> `^before_cut sa sb fn id`,
     `observer` |-> `frag_observer sa sb fn id`,
     `cut` |-> `<|bb_label := sb.cs_current_bb;
                   bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`]
    (SPEC_ALL frag_fuel_path_reaches_cut))) >>
  impl_tac
  >- (asm_rewrite_tac[frag_observer_cut_lookup, frag_observer_cut_instruction] >>
      metis_tac[entry_observer_matches_before_cut, entry_observer_first_exit]) >>
  simp[]
QED
