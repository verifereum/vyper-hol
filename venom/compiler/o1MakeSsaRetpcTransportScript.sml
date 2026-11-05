Theory o1MakeSsaRetpcTransport
Ancestors o1ContractMakeSsaPtrOk o1MakeSsaRequiredUses unitShapeDefs list
  venomWf cfgWf

Theorem mssa_retpc_definition_cases:
  retpc_shape_ok fn /\ mssa_inst_origin orig fn i /\
  MEM i (fn_insts g) /\ MEM v i.inst_outputs /\ retpc_var fn (orig v) ==>
  i.inst_opcode = RETPC_PARAM \/
  (i.inst_opcode = ASSIGN /\ ?u. i.inst_operands = [Var u] /\ retpc_var fn (orig u)) \/
  (i.inst_opcode = PHI /\ !u. MEM (Var u) i.inst_operands ==> retpc_var fn (orig u))
Proof
  strip_tac >> qpat_x_assum `mssa_inst_origin _ _ _` mp_tac >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac
  >- (`MEM (orig v) inst.inst_outputs` by metis_tac[listTheory.MEM_MAP] >>
      gvs[retpc_shape_ok_def] >>
      qpat_x_assum `!inst x. MEM inst (fn_insts fn) /\ _ ==> _` drule_all >>
      strip_tac >> gvs[] >>
      Cases_on `i.inst_operands` >> gvs[] >>
      Cases_on `h` >> gvs[]) >>
  gvs[retpc_shape_ok_def] >>
  qpat_x_assum `!inst x. MEM inst (fn_insts fn) /\ _ ==> _` drule_all >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem mssa_retpc_origin_forward:
  !g v. retpc_var g v ==> !orig fn.
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) ==>
  retpc_var fn (orig v)
Proof
  simp[retpc_var_def] >> Induct_on `copy_phi_var` >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `!i. MEM i _ ==> mssa_inst_origin _ _ _` drule >>
      pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[] >>
      metis_tac[copy_phi_var_rules, MEM_MAP]) >>
  rename1 `copy_phi_var RETPC_PARAM g u` >>
  `copy_phi_var RETPC_PARAM fn (orig u)` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!i. MEM i _ ==> mssa_inst_origin _ _ _` drule >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >>
  gvs[]
  >- (`MEM (orig v) inst'.inst_outputs` by metis_tac[MEM_MAP] >>
      irule (cj 2 copy_phi_var_rules) >> metis_tac[]) >>
  metis_tac[cj 3 copy_phi_var_rules]
QED

Theorem mssa_retpc_output_on_path:
  retpc_shape_ok fn /\
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) /\
  fn_defs_reach_uses g /\ ssa_form g /\ fn_phis_cover_preds g /\
  (!bb inst. MEM bb g.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_entry_label g = SOME bb.bb_label ==> inst.inst_opcode <> PHI) ==>
  !n j path bb v.
    LENGTH path = n /\ is_fn_path g path /\ path <> [] /\
    fn_entry_label g = SOME (HD path) /\ LAST path = bb.bb_label /\
    MEM bb g.fn_blocks /\ j < LENGTH bb.bb_instructions /\
    MEM v (EL j bb.bb_instructions).inst_outputs /\ retpc_var fn (orig v) ==>
    retpc_var g v
Proof
  strip_tac >> completeInduct_on `n` >> gen_tac >>
  completeInduct_on `j` >> rpt strip_tac >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  `MEM (EL j bb.bb_instructions) (fn_insts g)` by
    (simp[venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `mssa_inst_origin orig fn (EL j bb.bb_instructions)` by metis_tac[] >>
  drule_all mssa_retpc_definition_cases >> strip_tac
  >- (simp[retpc_var_def] >> metis_tac[cj 1 copy_phi_var_rules])
  >- suspend "assign"
  >> suspend "phi"
QED

Resume mssa_retpc_output_on_path[assign]:
  `MEM (Var u) (EL j bb.bb_instructions).inst_operands /\
   (EL j bb.bb_instructions).inst_opcode <> PHI` by simp[] >>
  drule_all mssa_nonphi_earlier_def >> strip_tac
  >- (`retpc_var g u` by
        (qpat_x_assum `!m. m < n ==> _` (qspec_then `LENGTH pre` mp_tac) >>
         (impl_tac >- decide_tac) >>
         disch_then (qspecl_then [`di`, `pre`, `db`, `u`] mp_tac) >> simp[]) >>
      simp[retpc_var_def] >> metis_tac[cj 2 copy_phi_var_rules, retpc_var_def]) >>
  `retpc_var g u` by
    (qpat_x_assum `!m. m < j ==> _` (qspec_then `i` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`path`, `bb`, `u`] mp_tac) >> simp[]) >>
  simp[retpc_var_def] >> metis_tac[cj 2 copy_phi_var_rules, retpc_var_def]
QED

Resume mssa_retpc_output_on_path[phi]:
  qpat_x_assum `!m. m < n ==> _` (mk_asm "outer") >>
  qpat_x_assum `!m. m < j ==> _` kall_tac >>
  Cases_on `path` using SNOC_CASES >- gvs[] >>
  rename1 `SNOC last prefix` >>
  Cases_on `prefix = []` >- (gvs[] >> metis_tac[]) >>
  `!xs. HD (prefix ++ xs) = HD prefix` by (Cases_on `prefix` >> gvs[]) >>
  gvs[SNOC_APPEND] >>
  drule_all mssa_phi_earlier_def >> strip_tac >>
  `MEM (Var u) (EL j bb.bb_instructions).inst_operands` by
    metis_tac[cfgNormBaseTheory.phi_pairs_mem_var] >>
  `retpc_var fn (orig u)` by metis_tac[] >>
  `retpc_var g u` by
    (asm "outer" (qspec_then `LENGTH pre` mp_tac) >>
     (impl_tac >- gvs[]) >>
     disch_then (qspecl_then [`di`, `pre`, `db`, `u`] mp_tac) >> simp[]) >>
  simp[retpc_var_def] >> metis_tac[cj 3 copy_phi_var_rules, retpc_var_def]
QED

Finalise mssa_retpc_output_on_path

Theorem mssa_retpc_output_backward:
  retpc_shape_ok fn /\
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) /\
  fn_defs_reach_uses g /\ ssa_form g /\ fn_phis_cover_preds g /\
  all_reachable g /\
  (!bb inst. MEM bb g.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_entry_label g = SOME bb.bb_label ==> inst.inst_opcode <> PHI) /\
  MEM inst (fn_insts g) /\ MEM v inst.inst_outputs /\ retpc_var fn (orig v) ==>
  retpc_var g v
Proof
  strip_tac >>
  `?bb. MEM bb g.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `fn_reachable g bb.bb_label` by gvs[all_reachable_def] >>
  gvs[fn_reachable_def] >> drule venomExecProofsTheory.rtc_to_fn_path >> strip_tac >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  irule mssa_retpc_output_on_path >> simp[] >> conj_tac
  >- metis_tac[] >> conj_tac
  >- (qexistsl_tac [`bb`, `j`, `path`] >> simp[]) >>
  qexistsl_tac [`fn`, `orig`] >> simp[]
QED

Theorem mssa_retpc_operand_backward:
  retpc_shape_ok fn /\
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) /\
  fn_defs_reach_uses g /\ wf_ssa g /\ fn_phis_cover_preds g /\
  all_reachable g /\
  (!bb inst. MEM bb g.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_entry_label g = SOME bb.bb_label ==> inst.inst_opcode <> PHI) /\
  MEM inst (fn_insts g) /\ MEM (Var v) inst.inst_operands /\ retpc_var fn (orig v) ==>
  retpc_var g v
Proof
  strip_tac >> drule_all mssa_operand_has_definition >> strip_tac >>
  irule mssa_retpc_output_backward >> gvs[venomWfTheory.wf_ssa_def] >> metis_tac[]
QED
