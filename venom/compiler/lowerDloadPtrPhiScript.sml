Theory lowerDloadPtrPhi
Ancestors
  venomExecSemantics venomState venomInst execEquivParamBase
  list pred_set finite_map lowerDloadDefs o1ContractLowerDload

Theorem eval_operand_definedness:
  s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  (eval_operand op s = NONE <=> eval_operand op t = NONE)
Proof
  Cases_on `op` >> simp[eval_operand_def]
QED

Theorem update_var_definedness:
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  !v. v IN V ==>
    (lookup_var v (update_var out a s) = NONE <=>
     lookup_var v (update_var out b t) = NONE)
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = out` >> simp[]
QED

Theorem eval_one_phi_definedness:
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==>
       (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  eval_one_phi t i = SOME (out,b) ==>
  ?a. eval_one_phi s i = SOME (out,a)
Proof
  strip_tac >> gvs[eval_one_phi_def, AllCaseEqs()] >>
  rename1 `eval_operand op t = SOME b` >>
  `MEM op i.inst_operands` by metis_tac[resolve_phi_MEM] >>
  `eval_operand op s <> NONE` by
    (drule eval_operand_definedness >>
     disch_then (qspec_then `op` mp_tac) >>
     (impl_tac >- (rpt strip_tac >> gvs[])) >> simp[]) >>
  Cases_on `eval_operand op s` >> gvs[]
QED

Theorem eval_phis_definedness:
  !xs V s t t'.
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!i v. MEM i xs /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  eval_phis t xs = OK t' ==>
  ?s'. eval_phis s xs = OK s' /\
       (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  Induct_on `xs` >- simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (qpat_x_assum `eval_phis t (h::xs) = OK t'` mp_tac >>
      simp[Once eval_phis_def] >>
      Cases_on `eval_one_phi t h` >> simp[] >>
      rename1 `eval_one_phi t h = SOME pair` >> PairCases_on `pair` >>
      Cases_on `eval_phis t xs` >> simp[] >> strip_tac >>
      rename1 `eval_phis t xs = OK tailt` >>
      `?a. eval_one_phi s h = SOME (pair0,a)` by
        (irule eval_one_phi_definedness >>
         qexistsl [`pair1`, `t`] >> simp[] >> metis_tac[MEM]) >>
      `?s'. eval_phis s xs = OK s' /\
        (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v tailt = NONE))` by
        (first_x_assum irule >> conj_tac
         >- metis_tac[MEM] >> qexists `t` >> simp[]) >>
      qexists `update_var pair0 a s'` >>
      simp[Once eval_phis_def] >> gvs[] >>
      rpt strip_tac >> irule update_var_definedness >> qexists `V` >> simp[]) >>
  gvs[Once eval_phis_def] >> qexists `s` >> simp[Once eval_phis_def]
QED

Theorem lower_dload_insts_supply_phi_exact:
  !xs q ys q'. lower_dload_insts_supply q xs = (ys,q') ==>
    phi_prefix_length ys = phi_prefix_length xs /\
    TAKE (phi_prefix_length ys) ys = TAKE (phi_prefix_length xs) xs /\
    (!s. eval_phis s ys = eval_phis s xs)
Proof
  Induct_on `xs` >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply q h = ([h],q)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[] >> first_x_assum drule >> strip_tac >> gvs[] >>
      simp[phi_prefix_length_def, eval_phis_def]) >>
  `out <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  Cases_on `out` >- gvs[] >>
  `h'.inst_opcode <> PHI` by
    (strip_tac >> drule lower_dload_inst_supply_control >>
     simp[] >> metis_tac[]) >>
  gvs[phi_prefix_length_def, eval_phis_def]
QED

Theorem lower_dload_block_supply_phi_exact:
  lower_dload_block_supply q bb = (bb',q') ==>
    phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
    TAKE (phi_prefix_length bb'.bb_instructions) bb'.bb_instructions =
      TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
    (!s. eval_phis s bb'.bb_instructions = eval_phis s bb.bb_instructions)
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule lower_dload_insts_supply_phi_exact >> simp[]
QED

Theorem lower_dload_block_supply_phi_definedness:
  lower_dload_block_supply q bb = (bb',q') /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  eval_phis t bb'.bb_instructions = OK t' ==>
  ?s'. eval_phis s bb.bb_instructions = OK s' /\
       (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  strip_tac >> drule lower_dload_block_supply_phi_exact >> strip_tac >>
  gvs[] >> irule eval_phis_definedness >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> qexists `i` >> simp[]) >>
  qexists `t` >> simp[]
QED
