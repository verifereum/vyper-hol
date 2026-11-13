Theory lowerDloadReachableDiscipline
Ancestors
  lowerDloadOwnership ptrDiscipline o1LowerDloadGhost o1LowerDloadOccurrence
  venomExecSemantics venomState venomInst finite_map list pred_set words

Theorem ld_annotated_taint_ok:
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s ==>
  taint_ok fn tn i s
Proof
  strip_tac >> drule ld_annotated_erasure >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

(* Pointer arithmetic that steps has its fixed arity. *)
Theorem ld_step_arith_operands[local]:
  step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode <> INVOKE ==>
  ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) ==>
   ?a b. inst.inst_operands = [a; b]) /\
  (inst.inst_opcode = ASSIGN ==> ?a. inst.inst_operands = [a])
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

(* A DALLOCA output's frame site starts at the free memory pointer, which
   is at or above the dynamic floor. *)
Theorem ld_dalloca_dyn_site[local]:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  ptr_discipline lo ctx vs0 /\ active_inst fn inst s /\
  inst.inst_opcode = DALLOCA /\ step_inst fuel ctx inst s = OK s' ==>
  ?b z. out_prov PG G inst s' = SOME (b,z) /\ dyn_floor ctx vs0 <= b /\
        b + z < dimword (:256)
Proof
  strip_tac >> fs[ptr_discipline_def] >>
  `EVERY (fn_ptr_ok P) ctx.ctx_functions` by fs[EVERY_MEM] >>
  drule frame_reachable_prov_support >> disch_then drule >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (qpat_x_assum `active_inst _ _ _` mp_tac >>
     rw[contextCodegenRelTheory.active_inst_def, fn_insts_def,
        o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `ctx_has_dalloca ctx` by
    (simp[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  `allocas_below_fmp s` by metis_tac[] >>
  `s.vs_initial_fmp = vs0.vs_initial_fmp` by
    metis_tac[frame_reachable_initial_fmp] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> simp[AllCaseEqs()] >> strip_tac >>
  gvs[out_prov_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      dyn_floor_def, allocas_below_fmp_def] >>
  qmatch_goalsub_abbrev_tac `w2n a + (w2n c - w2n a)` >>
  `w2n a < dimword (:256) /\ w2n c < dimword (:256)` by simp[w2n_lt] >>
  decide_tac
QED

(* One annotated step against the frame step: the frame provenance keeps
   the selected sites, and its extra sites stay dynamic. *)
Theorem ld_annotated_step_ghosts[local]:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  ptr_discipline lo ctx vs0 /\ active_inst fn inst s /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' /\
  ld_erase L' = s'.vs_allocas /\
  (!v x. FLOOKUP (ld_erase AG) v = SOME x ==> FLOOKUP G v = SOME x) /\
  (!v. FLOOKUP (ld_erase AG) v = NONE ==>
     FLOOKUP G v = NONE \/
     ?b z. FLOOKUP G v = SOME (b,z) /\ dyn_floor ctx vs0 <= b /\
           b + z < dimword (:256)) /\
  LIST_REL (\p q. (!x. p = SOME x ==> q = SOME x) /\
    (p = NONE ==>
       q = NONE \/ ?b z. q = SOME (b,z) /\ dyn_floor ctx vs0 <= b /\
                         b + z < dimword (:256)))
    (MAP (OPTION_MAP SND) AP) PG ==>
  (!v x. FLOOKUP (ld_erase (ld_step_prov AP AG L' inst)) v = SOME x ==>
         FLOOKUP (step_prov PG G inst s') v = SOME x) /\
  (!v. FLOOKUP (ld_erase (ld_step_prov AP AG L' inst)) v = NONE ==>
     FLOOKUP (step_prov PG G inst s') v = NONE \/
     ?b z. FLOOKUP (step_prov PG G inst s') v = SOME (b,z) /\
           dyn_floor ctx vs0 <= b /\ b + z < dimword (:256))
Proof
  strip_tac >> rewrite_tac[ld_step_prov_def, step_prov_def, ld_erase_set_prov] >>
  irule ld_ghost_set_prov >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (`ld_out_prov AP AG L' inst = NONE` by simp[ld_out_prov_def] >>
      drule_all ld_dalloca_dyn_site >> strip_tac >> simp[]) >>
  `OPTION_MAP SND (ld_out_prov AP AG L' inst) =
   out_prov (MAP (OPTION_MAP SND) AP) (ld_erase AG) inst s'` by
    (irule ld_erase_out_prov >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule ld_ghost_out_prov >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all ld_step_arith_operands >> strip_tac >>
  Cases_on `inst.inst_opcode = ASSIGN` >> gvs[] >>
  fs[ptr_discipline_def] >>
  `EVERY (fn_ptr_ok P) ctx.ctx_functions` by fs[EVERY_MEM] >>
  drule frame_reachable_prov_support >> disch_then drule >> strip_tac >>
  `fn_ptr_ok P fn` by fs[EVERY_MEM] >>
  `MEM inst (fn_insts fn)` by
    (qpat_x_assum `active_inst _ _ _` mp_tac >>
     rw[contextCodegenRelTheory.active_inst_def, fn_insts_def,
        o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    fs[fn_insts_def, venomFnInstsProofsTheory.mem_fn_insts_blocks_rev] >>
  `affine_pointer_ops fn (ptr_roots P fn)` by fs[fn_ptr_ok_def] >>
  `v IN fn_pv P fn /\ w IN fn_pv P fn` by fs[SUBSET_DEF] >>
  fs[fn_pv_def, pointerConfinedDefsTheory.affine_pointer_ops_def] >>
  first_x_assum (qspecl_then [`bb`,`inst`] mp_tac) >> gvs[] >>
  metis_tac[]
QED

(* The frame provenance of an annotated state: it has every selected site,
   and its other sites are DALLOCA sites at or above the dynamic floor.
   The parameters and saved frames are related the same way. *)
Theorem ld_annotated_ghosts:
  !vs0 ctx astk k L AP AG tn fn inst s.
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  ptr_discipline lo ctx vs0 ==>
  ?stk PG G. frame_reachable vs0 ctx stk PG G tn fn inst s /\
    (!v x. FLOOKUP (ld_erase AG) v = SOME x ==> FLOOKUP G v = SOME x) /\
    (!v. FLOOKUP (ld_erase AG) v = NONE ==>
       FLOOKUP G v = NONE \/
       ?b z. FLOOKUP G v = SOME (b,z) /\ dyn_floor ctx vs0 <= b /\
             b + z < dimword (:256)) /\
    LIST_REL (\p q. (!x. p = SOME x ==> q = SOME x) /\
      (p = NONE ==>
         q = NONE \/ ?b z. q = SOME (b,z) /\ dyn_floor ctx vs0 <= b /\
                           b + z < dimword (:256)))
      (MAP (OPTION_MAP SND) AP) PG /\
    LIST_REL (\af f. f.cf_fn = af.lf_fn /\ f.cf_inst = af.lf_inst /\
      f.cf_state = af.lf_state /\ f.cf_tvar = af.lf_tvar /\
      (!v x. FLOOKUP (ld_erase af.lf_prov) v = SOME x ==>
             FLOOKUP f.cf_prov v = SOME x) /\
      (!v. FLOOKUP (ld_erase af.lf_prov) v = NONE ==>
         FLOOKUP f.cf_prov v = NONE \/
         ?b z. FLOOKUP f.cf_prov v = SOME (b,z) /\ dyn_floor ctx vs0 <= b /\
               b + z < dimword (:256)) /\
      LIST_REL (\p q. (!x. p = SOME x ==> q = SOME x) /\
        (p = NONE ==>
           q = NONE \/ ?b z. q = SOME (b,z) /\ dyn_floor ctx vs0 <= b /\
                             b + z < dimword (:256)))
        (MAP (OPTION_MAP SND) af.lf_params) f.cf_params)
      astk stk
Proof
  ho_match_mp_tac ld_annotated_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> TRY (disch_then strip_assume_tac) >> TRY strip_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call" >>
  suspend "ret"
QED

Resume ld_annotated_ghosts[entry]:
  qexistsl_tac [`[]`, `[]`, `FEMPTY`] >> simp[ld_erase_def] >>
  irule frame_reachable_entry >> metis_tac[]
QED

Resume ld_annotated_ghosts[next]:
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`stk`, `PG`, `step_prov PG G inst s'`] >>
  conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
  once_rewrite_tac[CONJ_ASSOC] >>
  conj_tac >- (irule ld_annotated_step_ghosts >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Resume ld_annotated_ghosts[block]:
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`stk`, `PG`, `entry_prov fn s' G`] >>
  conj_tac >- (irule frame_reachable_block >> metis_tac[]) >>
  rewrite_tac[ld_erase_entry_prov] >> once_rewrite_tac[CONJ_ASSOC] >>
  conj_tac >- (irule ld_ghost_entry_prov >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Resume ld_annotated_ghosts[call]:
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`<| cf_fn := fn; cf_inst := inst; cf_state := s;
                   cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>
                 :: stk`, `MAP (op_prov G) ops`, `FEMPTY`] >>
  conj_tac >- (irule frame_reachable_call >> metis_tac[]) >>
  rpt conj_tac
  >- simp[ld_erase_def]
  >- simp[ld_erase_def]
  >- (`MAP (OPTION_MAP SND) (MAP (ld_op_prov AG) ops) =
       MAP (op_prov (ld_erase AG)) ops` by
        simp[MAP_MAP_o, MAP_EQ_f, ld_erase_op_prov] >>
      pop_assum SUBST1_TAC >>
      simp[LIST_REL_EL_EQN, EL_MAP] >> rpt gen_tac >> strip_tac >>
      irule ld_ghost_op_prov >> metis_tac[]) >>
  fs[]
QED

Resume ld_annotated_ghosts[ret]:
  first_x_assum drule >> strip_tac >>
  rename1 `LIST_REL _ (f::astk) stk0` >>
  Cases_on `stk0` >> fs[] >> rename1 `LIST_REL _ astk stk` >>
  qexistsl_tac [`stk`, `h.cf_params`,
                `DRESTRICT h.cf_prov (COMPL (set h.cf_inst.inst_outputs))`] >>
  rewrite_tac[ld_erase_restrict] >>
  conj_tac
  >- (qpat_x_assum `h.cf_fn = _` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `h.cf_inst = _` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `h.cf_state = _` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `h.cf_tvar = _` (SUBST_ALL_TAC o SYM) >>
      irule frame_reachable_ret >> metis_tac[]) >>
  once_rewrite_tac[CONJ_ASSOC] >>
  conj_tac >- (simp[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Finalise ld_annotated_ghosts

(* Every access an annotated state makes goes through a frame provenance
   that has the selected sites; a pointer with no selected site is a
   DALLOCA pointer into the dynamic region. *)
Theorem ld_annotated_access_ok:
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s ==>
  ?G. access_ok lo G fn i s /\
      (!v x. FLOOKUP (ld_erase AG) v = SOME x ==> FLOOKUP G v = SOME x) /\
      (!v b z. FLOOKUP AG v = NONE /\ FLOOKUP G v = SOME (b,z) ==>
         dyn_floor ctx s <= b /\ b + z < dimword (:256))
Proof
  strip_tac >> drule ld_annotated_ghosts >>
  disch_then drule >> strip_tac >>
  qexists_tac `G` >>
  `s.vs_initial_fmp = vs0.vs_initial_fmp` by
    metis_tac[frame_reachable_initial_fmp] >>
  `dyn_floor ctx s = dyn_floor ctx vs0` by simp[dyn_floor_def] >>
  pop_assum SUBST1_TAC >>
  conj_tac >- (fs[ptr_discipline_def] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP (ld_erase AG) v = NONE` by simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem ld_taint_operand_clean:
  taint_ok fn tn i s /\ MEM op i.inst_operands /\
  i.inst_opcode <> ASSIGN /\
  ~MEM i.inst_opcode [MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE] ==>
  op_taint tn op = {}
Proof
  simp[taint_ok_def, MEM] >> metis_tac[]
QED

Theorem ld_taint_store_address_clean:
  taint_ok fn tn i s /\
  MEM i.inst_opcode [MSTORE;SSTORE;TSTORE;ISTORE] /\
  i.inst_operands = [a;v] ==>
  op_taint tn a = {}
Proof
  simp[taint_ok_def, MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `a` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ld_taint_shift_amount_clean:
  taint_ok fn tn i s /\ MEM i.inst_opcode [SHL;SHR;SAR] /\
  i.inst_operands = [n;v] ==>
  op_taint tn n = {}
Proof
  simp[taint_ok_def, MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> metis_tac[]
QED
