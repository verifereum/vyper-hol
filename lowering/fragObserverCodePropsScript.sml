(* The STOP-cut observer retains the installed fragment code. *)
Theory fragObserverCodeProps
Ancestors exprSimAbiGasBridge fragExec fragFuel venomInst venomExecSemantics
  venomExecProofs exprLoweringProps loweringShapeDefs list rich_list

Theorem frag_code_in_state_insts:
  MEM i (frag_code sa sb) ==> MEM i (state_insts sb)
Proof
  `!b. MEM b (emitted_blocks sa sb) ==> MEM b sb.cs_blocks` by
    (simp[emitted_blocks_def] >> metis_tac[MEM_TAKE]) >>
  Cases_on `emitted_blocks sa sb` >>
  simp[frag_code_def, state_insts_def, emitted_insts_def, all_blocks_def,
       MEM_FLAT, MEM_MAP, MEM_REVERSE] >>
  strip_tac
  >- metis_tac[MEM_DROP_IMP] >>
  `MEM (LAST (h::t)) sb.cs_blocks` by metis_tac[MEM_LAST_NOT_NIL, NOT_CONS_NIL] >>
  `!b. MEM b (FRONT (h::t)) ==> MEM b sb.cs_blocks` by
    metis_tac[MEM_FRONT] >>
  metis_tac[MEM_DROP_IMP]
QED

Theorem reject_observer_has_code:
  fn_has_code sa sb fn /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) ==>
  fn_has_code sa sb (frag_observer sa sb fn id)
Proof
  rw[fn_has_code_def]
  >- (rename1 `MEM emitted (emitted_blocks sa sb)` >>
      `emitted.bb_label <> sb.cs_current_bb` by (fs[MEM_MAP] >> metis_tac[]) >>
      simp[frag_observer_def, lookup_block_def, FIND_thm] >>
      rewrite_tac[GSYM lookup_block_def] >>
      irule exprSimAbiGasBridgeTheory.frag_observer_lookup_filter >> simp[]) >>
  qexists_tac `<|bb_label := sb.cs_current_bb;
    bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` >>
  simp[frag_observer_cut_lookup, IS_PREFIX_APPEND3]
QED

Theorem abi_dyn_observer_no_phi:
  !sa sb fn id. fn_has_code sa sb fn /\ no_phi_fn fn ==>
    no_phi_fn (frag_observer sa sb fn id)
Proof
  rpt gen_tac >> strip_tac >>
  `?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    IS_PREFIX bb.bb_instructions sb.cs_current_insts` by gvs[fn_has_code_def] >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (drule venomExecProofsTheory.lookup_block_MEM >>
     gvs[no_phi_fn_def, EVERY_MEM] >> metis_tac[]) >>
  simp[frag_observer_def, no_phi_fn_def] >> conj_tac
  >- (gvs[rich_listTheory.IS_PREFIX_APPEND] >>
      Cases_on `sb.cs_current_insts` >>
      gvs[phi_prefix_length_def, mk_inst_def, AllCaseEqs()]) >>
  gvs[no_phi_fn_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED
