(* Successful path inversion without assuming first-arrival uniqueness. *)
Theory bodyPtrBopInSuffix
Ancestors bodyPtrBopInArrival fragGasPath fragGasMode

Theorem successful_gas_path_last_edge:
  !ctx fn s n r. gas_path ctx fn s n r ==>
  !t. r = OK t ==>
    (s = t /\ n = 0) \/ ?u a b. gas_path ctx fn s a (OK u) /\
                      gas_path_edge ctx fn u b (OK t) /\ n = a + b
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum (qspec_then `t` mp_tac) >> simp[] >>
      strip_tac
      >- (gvs[] >> disj2_tac >> qexistsl_tac [`s`,`0`,`n`] >>
          simp[] >> irule (cj 1 gas_path_rules) >>
          gvs[gas_path_edge_def]) >>
      disj2_tac >> qexistsl_tac [`u`,`n + a`,`b`] >>
      pure_asm_rewrite_tac[arithmeticTheory.ADD_ASSOC, boolTheory.AND_CLAUSES] >>
      simp_tac bool_ss [] >>
      irule (cj 2 gas_path_rules) >> metis_tac[]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem successful_path_arrival_predecessor:
  lookup_block L fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ seg ++ post /\ seg <> [] /\
  EVERY (\i. i.inst_opcode <> PHI) seg /\ LENGTH pre < k /\
  s.vs_current_bb = L /\ s.vs_inst_idx = LENGTH pre /\
  gas_path ctx fn s n (OK t) /\
  t.vs_current_bb = L /\ t.vs_inst_idx = k ==>
  ?u a b. gas_path ctx fn s a (OK u) /\
          gas_path_edge ctx fn u b (OK t) /\ n = a + b /\
          u.vs_current_bb = L /\ u.vs_inst_idx = k - 1
Proof
  strip_tac >> drule successful_gas_path_last_edge >>
  disch_then (qspec_then `t` mp_tac) >>
  simp_tac (srw_ss()) [] >> strip_tac
  >- (qpat_x_assum `s = t` SUBST_ALL_TAC >>
      qpat_x_assum `t.vs_inst_idx = LENGTH pre` mp_tac >>
      qpat_x_assum `t.vs_inst_idx = k` mp_tac >>
      qpat_x_assum `LENGTH pre < k` mp_tac >>
      simp_tac arith_ss []) >>
  drule_all edge_arrival_inside_nonphi_segment >> strip_tac >>
  qexistsl_tac [`u`,`a`,`b`] >> simp_tac bool_ss [] >> metis_tac[]
QED

Theorem successful_path_segment_suffix:
  !j ctx fn L bb pre seg post s n t.
  lookup_block L fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ seg ++ post /\ seg <> [] /\
  EVERY (\i. i.inst_opcode <> PHI) seg /\ j <= LENGTH seg /\
  s.vs_current_bb = L /\ s.vs_inst_idx = LENGTH pre /\
  gas_path ctx fn s n (OK t) /\
  t.vs_current_bb = L /\ t.vs_inst_idx = LENGTH pre + j ==>
  ?u a. gas_path ctx fn s a (OK u) /\
        u.vs_current_bb = L /\ u.vs_inst_idx = LENGTH pre /\
        NRC (\x y. x.vs_current_bb = L /\ y.vs_current_bb = L /\
                   y.vs_inst_idx = SUC x.vs_inst_idx /\
                   ?b. gas_path_edge ctx fn x b (OK y)) j u t
Proof
  Induct >- (rpt strip_tac >> qexistsl_tac [`t`,`n`] >>
             asm_simp_tac bool_ss [arithmeticTheory.NRC, arithmeticTheory.ADD_0]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH pre < LENGTH pre + SUC j` by decide_tac >>
  drule_all successful_path_arrival_predecessor >> strip_tac >>
  `u.vs_inst_idx = LENGTH pre + j` by decide_tac >>
  `j <= LENGTH seg` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`u'`,`a'`] >>
  asm_simp_tac bool_ss [] >>
  rewrite_tac[arithmeticTheory.NRC_SUC_RECURSE_LEFT] >>
  qexists_tac `u` >> asm_simp_tac bool_ss [] >>
  conj_tac >- decide_tac >>
  qexists_tac `b` >> asm_rewrite_tac[]
QED

Theorem nonterminating_edge_instruction:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\
  gas_path_edge ctx fn s n (OK t) ==>
  ?fuel v. step_inst fuel ctx i s = OK v /\
           ~s.vs_halted /\ ~v.vs_halted /\
           t = v with vs_inst_idx := SUC s.vs_inst_idx
Proof
  strip_tac >> gvs[gas_path_edge_def, fragExecTheory.exit_result_def]
  >- (qexistsl_tac [`fuel`,`t'`] >> simp[]) >>
  qpat_x_assum `OK t = _` (assume_tac o SYM) >>
  gvs[fragExecTheory.exit_result_def]
QED

Theorem marked_path_segment_suffix:
  lookup_block L fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ seg ++ post /\ seg <> [] /\
  EVERY (\i. i.inst_opcode <> PHI) seg /\ j <= LENGTH seg /\
  s.vs_current_bb = L /\ s.vs_inst_idx = LENGTH pre /\
  gas_marked_path memory ctx fn s n (OK t) /\
  t.vs_current_bb = L /\ t.vs_inst_idx = LENGTH pre + j ==>
  ?u a. gas_path ctx fn s a (OK u) /\
        u.vs_current_bb = L /\ u.vs_inst_idx = LENGTH pre /\
        NRC (\x y. x.vs_current_bb = L /\ y.vs_current_bb = L /\
                   y.vs_inst_idx = SUC x.vs_inst_idx /\
                   ?b. gas_path_edge ctx fn x b (OK y)) j u t
Proof
  strip_tac >> drule gas_marked_path_exec >> strip_tac >>
  drule_all successful_path_segment_suffix >> simp_tac bool_ss []
QED
