Theory lowerDloadPtrPhi
Ancestors
  venomExecSemantics venomState venomInst execEquivParamBase
  unitShapeDefs list pred_set finite_map lowerDloadDefs o1ContractLowerDload contextCodegenRel lowerDloadPtrRel ptrDiscipline

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

Theorem lower_dload_blocks_supply_lookup:
  !bs q cs q' lbl b'.
    lower_dload_blocks_supply q bs = (cs,q') /\
    lookup_block lbl cs = SOME b' ==>
    ?b u u'. lookup_block lbl bs = SOME b /\
              lower_dload_block_supply u b = (b',u')
Proof
  Induct_on `bs` >- simp[lower_dload_blocks_supply_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >> strip_tac >>
  `bb'.bb_label = h.bb_label` by
    (gvs[lower_dload_block_supply_def, AllCaseEqs()] >> simp[]) >>
  gvs[lookup_block_def, FIND_thm] >> Cases_on `h.bb_label = lbl` >> gvs[]
  >- (qexistsl [`q`,`s1`] >> simp[]) >>
  first_x_assum drule >> simp[lookup_block_def] >> metis_tac[]
QED

Theorem lower_dload_function_supply_enters_block:
  lower_dload_function_supply q f = (g,q') /\
  s.vs_current_bb = t.vs_current_bb /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!bb i v. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
            MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  enters_block g t t' ==>
  ?s'. enters_block f s s' /\ s'.vs_inst_idx = t'.vs_inst_idx /\
       (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  simp[lower_dload_function_supply_def, enters_block_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule_all lower_dload_blocks_supply_lookup >> strip_tac >>
  `MEM b f.fn_blocks` by metis_tac[lookup_block_def, FIND_MEM] >>
  `?sp. eval_phis s b.bb_instructions = OK sp /\
    (!v. v IN V ==> (lookup_var v sp = NONE <=> lookup_var v s_phi = NONE))` by
    (irule lower_dload_block_supply_phi_definedness >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> qexistsl [`b`,`i`] >> simp[]) >>
     qexistsl [`bb`, `u`, `u'`, `t`] >> simp[]) >>
  drule lower_dload_block_supply_phi_exact >> strip_tac >>
  qexists `sp with vs_inst_idx := phi_prefix_length b.bb_instructions` >>
  gvs[lookup_var_def] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem dload_vars_match_write:
  dload_vars_match fs V G H
    (tn with t_var := tv) (un with t_var := uv) s t /\
  (out IN V ==> m = n /\ dload_value_word fs m p q a b) ==>
  dload_vars_match fs V (set_prov G [out] p) (set_prov H [out] q)
    (tn with t_var := set_var_taint tv [out] m)
    (un with t_var := set_var_taint uv [out] n)
    (update_var out a s) (update_var out b t)
Proof
  strip_tac >> simp[dload_vars_match_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `v = out`
  >- (gvs[] >> Cases_on `p` >> Cases_on `q` >>
      gvs[lookup_var_def, update_var_def, set_prov_def, set_var_taint_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]) >>
  qpat_x_assum `dload_vars_match _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_vars_match_def] >>
  disch_then (qspec_then `v` mp_tac) >>
  simp[lookup_var_def, update_var_def, set_var_taint_def,
       FLOOKUP_UPDATE, op_taint_def] >> strip_tac >>
  Cases_on `p` >> Cases_on `q` >>
  gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem dload_matched_phi:
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  dload_vars_match fs V G H tn un s t /\
  (!lbl op w. s.vs_prev_bb = SOME lbl /\
    resolve_phi lbl i.inst_operands = SOME op /\ op = Var w ==> w IN V) /\
  eval_one_phi s i = SOME (out,a) /\ eval_one_phi t i = SOME (out,b) ==>
  phi_taint s.vs_prev_bb tn i = phi_taint t.vs_prev_bb un i /\
  dload_value_word fs (phi_taint s.vs_prev_bb tn i)
    (phi_prov s.vs_prev_bb G i) (phi_prov t.vs_prev_bb H i) a b
Proof
  strip_tac >> gvs[eval_one_phi_def, AllCaseEqs()] >>
  rename1 `eval_operand op s = SOME a` >>
  `!w. op = Var w ==> w IN V` by metis_tac[] >>
  `op_taint tn op = op_taint un op` by
    (Cases_on `op` >> gvs[op_taint_def, dload_vars_match_def]) >>
  `dload_value_word fs (op_taint tn op) (op_prov G op) (op_prov H op) a b` by
    (irule dload_matched_operand >> qexistsl [`V`,`s`,`t`,`un`] >> simp[]) >>
  gvs[phi_taint_def, phi_prov_def]
QED

Theorem dload_vars_match_phis:
  !xs s t s' t' fs V G H tn un.
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  dload_vars_match fs V G H tn un s t /\
  (!i v lbl op w. MEM i xs /\ i.inst_outputs = [v] /\ v IN V /\
    s.vs_prev_bb = SOME lbl /\ resolve_phi lbl i.inst_operands = SOME op /\
    op = Var w ==> w IN V) /\
  eval_phis s xs = OK s' /\ eval_phis t xs = OK t' ==>
  dload_vars_match fs V
    (phis_prov s.vs_prev_bb G xs) (phis_prov t.vs_prev_bb H xs)
    (tn with t_var := phis_taint s.vs_prev_bb tn xs)
    (un with t_var := phis_taint t.vs_prev_bb un xs) s' t'
Proof
  Induct_on `xs`
  >- (simp[eval_phis_def, phis_prov_def, phis_taint_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (Cases_on `eval_one_phi s h` >- gvs[Once eval_phis_def] >>
      rename1 `eval_one_phi s h = SOME pair` >> PairCases_on `pair` >>
      Cases_on `eval_one_phi t h` >- gvs[eval_phis_def] >>
      rename1 `eval_one_phi t h = SOME other` >> PairCases_on `other` >>
      Cases_on `eval_phis s xs` >> gvs[eval_phis_def] >>
      Cases_on `eval_phis t xs` >> gvs[eval_phis_def] >>
      `pair0 = other0 /\ h.inst_outputs = [pair0]` by
        (gvs[eval_one_phi_def, AllCaseEqs()]) >> gvs[] >>
      rename1 `eval_phis s xs = OK ss` >>
      rename1 `eval_phis t xs = OK tt` >>
      `dload_vars_match fs V
        (phis_prov t.vs_prev_bb G xs) (phis_prov t.vs_prev_bb H xs)
        (tn with t_var := phis_taint t.vs_prev_bb tn xs)
        (un with t_var := phis_taint t.vs_prev_bb un xs) ss tt` by
        (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
      `other0 IN V ==>
        phi_taint s.vs_prev_bb tn h = phi_taint t.vs_prev_bb un h /\
        dload_value_word fs (phi_taint s.vs_prev_bb tn h)
          (phi_prov s.vs_prev_bb G h) (phi_prov t.vs_prev_bb H h) pair1 other1` by
        (strip_tac >>
         `!lbl op w. s.vs_prev_bb = SOME lbl /\
           resolve_phi lbl h.inst_operands = SOME op /\ op = Var w ==> w IN V` by
           metis_tac[MEM] >>
         drule_all dload_matched_phi >> simp[]) >>
      simp[phis_prov_def, phis_taint_def] >>
      irule dload_vars_match_write >> gvs[]) >>
  gvs[eval_phis_def, phis_prov_def, phis_taint_def]
QED

Theorem retpc_phi_input_tracked:
  MEM i (fn_insts f) /\ i.inst_opcode = PHI /\
  MEM v i.inst_outputs /\ ~retpc_var f v /\
  MEM (Var w) i.inst_operands ==> ~retpc_var f w
Proof
  simp[retpc_var_def] >> metis_tac[copy_phi_var_phi]
QED

Theorem phi_prefix_member:
  !xs i. MEM i (TAKE (phi_prefix_length xs) xs) ==>
    MEM i xs /\ i.inst_opcode = PHI
Proof
  Induct_on `xs` >- simp[phi_prefix_length_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def] >> metis_tac[MEM]
QED

Theorem phi_prefix_computations:
  !xs. (!s. eval_phis s (TAKE (phi_prefix_length xs) xs) = eval_phis s xs) /\
    (!prev G. phis_prov prev G (TAKE (phi_prefix_length xs) xs) = phis_prov prev G xs) /\
    (!prev tn. phis_taint prev tn (TAKE (phi_prefix_length xs) xs) = phis_taint prev tn xs)
Proof
  Induct_on `xs`
  >- simp[phi_prefix_length_def, eval_phis_def, phis_prov_def, phis_taint_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def, eval_phis_def, phis_prov_def, phis_taint_def]
QED

Theorem dload_vars_match_phis_retpc:
  (!i. MEM i xs ==> MEM i (fn_insts f)) /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  dload_vars_match fs {v | ~retpc_var f v} G H tn un s t /\
  eval_phis s xs = OK s' /\ eval_phis t xs = OK t' ==>
  dload_vars_match fs {v | ~retpc_var f v}
    (phis_prov s.vs_prev_bb G xs) (phis_prov t.vs_prev_bb H xs)
    (tn with t_var := phis_taint s.vs_prev_bb tn xs)
    (un with t_var := phis_taint t.vs_prev_bb un xs) s' t'
Proof
  strip_tac >>
  `!i v lbl op w. MEM i (TAKE (phi_prefix_length xs) xs) /\
    i.inst_outputs = [v] /\ v IN {v | ~retpc_var f v} /\
    s.vs_prev_bb = SOME lbl /\ resolve_phi lbl i.inst_operands = SOME op /\
    op = Var w ==> w IN {v | ~retpc_var f v}` by
    (rpt strip_tac >> gvs[] >> irule retpc_phi_input_tracked >>
     drule phi_prefix_member >> strip_tac >>
     qexistsl [`i`,`v`] >> simp[] >> metis_tac[resolve_phi_MEM]) >>
  `eval_phis s (TAKE (phi_prefix_length xs) xs) = OK s' /\
   eval_phis t (TAKE (phi_prefix_length xs) xs) = OK t'` by
    simp[phi_prefix_computations] >>
  drule_all dload_vars_match_phis >> simp[phi_prefix_computations]
QED
