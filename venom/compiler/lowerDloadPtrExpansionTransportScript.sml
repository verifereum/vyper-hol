Theory lowerDloadPtrExpansionTransport
Ancestors
  lowerDloadPtrScratchTransport lowerDloadPtrPhase lowerDloadPtrBlockEntry lowerDloadPtrCall
  lowerDloadPtrAggregate lowerDloadPtrRel lowerDloadPtrPhi lowerDloadPtrTaint ptrDiscipline
  lowerDloadDefs venomExecSemantics venomState
  venomMemProps instIdxIndep codegenRel list rich_list words finite_map arithmetic pred_set

Theorem dload_code_data_padded_slice:
  code_layout_valid s /\ eval_operand (Label "code_end") s = SOME e /\
  w2n (off:bytes32) + w2n e < dimword (:256) ==>
  TAKE n (DROP (w2n (off+e)) s.vs_code ++ REPLICATE n 0w) =
  TAKE n (DROP (w2n off) s.vs_data_section ++ REPLICATE n 0w)
Proof
  simp[code_layout_valid_def, eval_operand_def] >> strip_tac >> gvs[] >>
  `LENGTH prefix < dimword (:256)` by
    (fs[dimword_def] >> decide_tac) >>
  gvs[LESS_MOD] >>
  `LENGTH prefix + w2n off < dimword (:256)` by decide_tac >>
  simp[word_add_def, w2n_n2w, LESS_MOD, DROP_APPEND, ADD_COMM, DROP_LENGTH_TOO_LONG]
QED

Theorem dload_mload_written_bytes:
  LENGTH bs = 32 ==>
  mload b (write_memory_with_expansion b bs s) = word_of_bytes T (0w:bytes32) bs
Proof
  strip_tac >>
  qspecl_then [`b`,`bs`,`s`] mp_tac write_memory_with_expansion_read_self >>
  simp[mload_def, TAKE_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  strip_tac >>
  simp[LENGTH_write_memory_with_expansion, MAX_DEF] >>
  IF_CASES_TAC >> simp[] >>
  `b+32 - LENGTH s.vs_memory = 0` by decide_tac >> simp[]
QED

Theorem dload_codecopy_payload:
  code_layout_valid s /\ eval_operand (Label "code_end") s = SOME e /\
  w2n (off:bytes32) + w2n e < dimword (:256) /\
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME (off+e) /\
  eval_operand sz s = SOME 32w /\ step_inst_base i s = OK s1 ==>
  mload (w2n b) s1 = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))
Proof
  strip_tac >> drule_all dload_code_data_padded_slice >>
  disch_then (qspec_then `32` assume_tac) >>
  gvs[step_inst_base_def, dimword_def] >> irule dload_mload_written_bytes >>
  simp[LENGTH_TAKE_EQ]
QED

Theorem dload_codecopy_mload_payload:
  code_layout_valid s /\ eval_operand (Label "code_end") s = SOME e /\
  w2n (off:bytes32) + w2n e < dimword (:256) /\
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME (off+e) /\
  eval_operand sz s = SOME 32w /\ step_inst_base i s = OK s1 /\
  j.inst_opcode = MLOAD /\ j.inst_operands = [addr] /\ j.inst_outputs = [out] /\
  eval_operand addr s1 = SOME b ==>
  step_inst_base j s1 = OK (update_var out
    (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))) s1)
Proof
  strip_tac >> drule_all dload_codecopy_payload >> strip_tac >>
  simp[step_inst_base_def, exec_read1_def]
QED

Theorem dload_supply_expansion:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\
  i.inst_outputs = [out] /\ lower_dload_inst_supply supply i = (xs,next) ==>
  ?av cv ai ci bi mi.
    xs = [<|inst_id := ai; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := [av]|>;
          <|inst_id := ci; inst_opcode := ADD;
            inst_operands := [off;Label "code_end"]; inst_outputs := [cv]|>;
          <|inst_id := bi; inst_opcode := CODECOPY;
            inst_operands := [Var av;Var cv;Lit 32w]; inst_outputs := []|>;
          <|inst_id := mi; inst_opcode := MLOAD;
            inst_operands := [Var av]; inst_outputs := [out]|>]
Proof
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem dload_four_step_replay:
  dload_prefix_match fuel C PH [a;b;c;d] 4 t H un t4 H4 un4 ==>
  ?v1 v2 v3 v4 t1 t2 t3 H1 H2 H3 un1 un2 un3.
    step_inst fuel C a t = OK v1 /\
    t1 = v1 with vs_inst_idx := SUC t.vs_inst_idx /\
    H1 = step_prov PH H a v1 /\ un1 = step_taint a t v1 un /\
    step_inst fuel C b t1 = OK v2 /\
    t2 = v2 with vs_inst_idx := SUC t1.vs_inst_idx /\
    H2 = step_prov PH H1 b v2 /\ un2 = step_taint b t1 v2 un1 /\
    step_inst fuel C c t2 = OK v3 /\
    t3 = v3 with vs_inst_idx := SUC t2.vs_inst_idx /\
    H3 = step_prov PH H2 c v3 /\ un3 = step_taint c t2 v3 un2 /\
    step_inst fuel C d t3 = OK v4 /\
    t4 = v4 with vs_inst_idx := SUC t3.vs_inst_idx /\
    H4 = step_prov PH H3 d v4 /\ un4 = step_taint d t3 v4 un3
Proof
  `4 = SUC (SUC (SUC (SUC 0)))` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem dload_expansion_replay_value:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var cv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  av <> cv /\ off <> Var av /\
  code_layout_valid t /\ eval_operand off t = SOME x /\
  eval_operand (Label "code_end") t = SOME e /\
  w2n x + w2n e < dimword (:256) /\
  dload_prefix_match fuel C PH [a;b;c;d] 4 t H un t4 H4 un4 ==>
  lookup_var out t4 = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n x) t.vs_data_section ++ REPLICATE 32 0w)))
Proof
  strip_tac >> drule dload_four_step_replay >> strip_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `H4 = _` kall_tac >> qpat_x_assum `un4 = _` kall_tac >>
  qpat_x_assum `H3 = _` kall_tac >> qpat_x_assum `un3 = _` kall_tac >>
  qpat_x_assum `H2 = _` kall_tac >> qpat_x_assum `un2 = _` kall_tac >>
  qpat_x_assum `H1 = _` kall_tac >> qpat_x_assum `un1 = _` kall_tac >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base a _ = _` mp_tac >>
  simp[step_inst_base_def, eval_operand_def] >> strip_tac >>
  `?p. lookup_var av v1 = SOME p /\
       eval_operand off v1 = SOME x /\
       eval_operand (Label "code_end") v1 = SOME e /\
       code_layout_valid v1 /\ v1.vs_data_section = t.vs_data_section` by
    (Cases_on `off` >>
     gvs[exec_alloca_def, AllCaseEqs(), update_var_def, lookup_var_def,
         eval_operand_def, FLOOKUP_UPDATE, code_layout_valid_def]) >>
  `v2 = update_var cv (x+e) (v1 with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_x_assum `step_inst_base b _ = _` mp_tac >>
     simp[step_inst_base_def, exec_pure2_def, eval_op_inst_idx, eval_operand_def, lookup_var_def] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base c t2` >>
  `code_layout_valid t2 /\ eval_operand (Label "code_end") t2 = SOME e /\
   eval_operand (Var av) t2 = SOME p /\
   eval_operand (Var cv) t2 = SOME (x+e) /\ eval_operand (Lit 32w) t2 = SOME 32w` by
    gvs[Abbr `t2`, update_var_def, lookup_var_def, eval_operand_def,
         FLOOKUP_UPDATE, code_layout_valid_def] >>
  `mload (w2n p) v3 = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n x) t2.vs_data_section ++ REPLICATE 32 0w))` by
    (irule dload_codecopy_payload >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl [`Var av`,`c`,`Var cv`,`Lit 32w`] >> simp[]) >>
  `eval_operand (Var av) v3 = SOME p` by
    (qpat_x_assum `step_inst_base c _ = _` mp_tac >>
     simp[step_inst_base_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `step_inst_base d _ = _` mp_tac >>
  simp[step_inst_base_def, exec_read1_def, eval_op_inst_idx] >>
  strip_tac >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    Abbr `t2`, mload_def]
QED

Theorem dload_boundary_core_target_temporary:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\ tmp NOTIN V ==>
  dload_boundary_core lo fs V Ws PG PH G (set_prov H [tmp] p)
    tn (un with t_var := set_var_taint un.t_var [tmp] mask)
    s (update_var tmp value t) cs ds
Proof
  strip_tac >>
  `dload_vars_match fs V G (set_prov H [tmp] p)
    tn (un with t_var := set_var_taint un.t_var [tmp] mask)
    s (update_var tmp value t)` by
    (drule dload_boundary_vars >>
     simp[dload_vars_match_def, set_prov_def, set_var_taint_def,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     Cases_on `p` >> simp[FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >>
     rpt strip_tac >> `v <> tmp` by metis_tac[] >>
     gvs[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  `lowerDloadPtrCall$dload_equal_environment s (update_var tmp value t)` by
    (drule dload_boundary_environment >>
     simp[lowerDloadPtrCallTheory.dload_equal_environment_def,
          update_var_def, venom_state_component_equality]) >>
  `dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
     (update_var tmp value t::MAP (\d. d.cf_state) ds)` by
    (drule dload_boundary_tables >>
     simp[dload_table_stack_def, update_var_def] >> strip_tac >>
     gen_tac >> Cases_on `k`
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]) >>
  gvs[dload_boundary_core_def, dload_memory_match_def,
      lowerDloadPtrCallTheory.dload_shared_store_def, update_var_def] >>
  metis_tac[]
QED

Theorem dload_source_read_step:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  eval_operand off s = SOME x ==>
  step_inst fuel C i s = OK (update_var out
    (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n x) s.vs_data_section ++ REPLICATE 32 0w))) s)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def]
QED

Theorem dload_supply_replay_read:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ off <> Var av /\
  code_layout_valid s /\ dload_offset_ok C fn i s /\
  lowerDloadPtrCall$dload_equal_environment s t /\
  eval_operand off s = SOME x /\ eval_operand off t = SOME x /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 ==>
  ?s1. step_inst fuel C i s = OK s1 /\ lookup_var out s1 = lookup_var out t4
Proof
  strip_tac >> drule_all dload_supply_expansion >> strip_tac >> gvs[] >>
  `code_layout_valid t /\ s.vs_data_section = t.vs_data_section /\
   s.vs_code = t.vs_code /\ s.vs_labels = t.vs_labels` by
    (gvs[lowerDloadPtrCallTheory.dload_equal_environment_def,
         venom_state_component_equality, code_layout_valid_def] >>
     metis_tac[]) >>
  `?e. eval_operand (Label "code_end") t = SOME e /\
       w2n x + w2n e < dimword (:256)` by
    (gvs[code_layout_valid_def, dload_offset_ok_def, eval_operand_def] >>
     `LENGTH t.vs_code - LENGTH t.vs_data_section < dimword (:256)` by
       (fs[dimword_def] >> decide_tac) >>
     simp[w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  `lookup_var out t4 = SOME (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n x) s.vs_data_section ++ REPLICATE 32 0w)))` by
    (drule_at (Pat `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`)
       dload_expansion_replay_value >> simp[]) >>
  qmatch_asmsub_abbrev_tac `lookup_var out t4 = SOME value` >>
  qexists_tac `update_var out value s` >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  pure_rewrite_tac[GSYM update_var_def] >>
  simp[Abbr `value`] >>
  qpat_x_assum `s.vs_data_section = t.vs_data_section`
    (fn th => rewrite_tac[GSYM th]) >>
  irule dload_source_read_step >> simp[]
QED


Theorem disjoint_fdom_lookup_none:
  DISJOINT (FDOM m) ids /\ aid IN ids ==> FLOOKUP m aid = NONE
Proof
  strip_tac >>
  `aid NOTIN FDOM m` by (fs[DISJOINT_ALT] >> metis_tac[]) >>
  simp[FLOOKUP_DEF]
QED

Theorem dload_scratch_copy_separation:
  dload_live_layout lo sf tf fs /\ j < LENGTH fs /\
  aid IN (EL j fs).dr_scratch /\
  FLOOKUP (EL j fs).dr_target aid = SOME (b,32) ==>
  (!x. x < lo ==> ~(b <= x /\ x < b+32)) /\
  (!owner id a c n k. dload_live_site fs owner id a c n /\ k < n ==>
    ~(b <= c+k /\ c+k < b+32))
Proof
  strip_tac >>
  `dload_frame_sites (EL j fs)` by
    (fs[dload_live_layout_def, EVERY_EL] >> metis_tac[]) >>
  `lo <= b` by (fs[dload_live_layout_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `owner <> j \/ id <> aid` by
    (spose_not_then strip_assume_tac >>
     `FLOOKUP (EL j fs).dr_source aid = NONE` by
       (irule disjoint_fdom_lookup_none >>
        qexists_tac `(EL j fs).dr_scratch` >> fs[dload_frame_sites_def]) >>
     fs[dload_live_site_def]) >>
  `0 < n` by decide_tac >>
  `b+32 <= c \/ c+n <= b` by
    (fs[dload_live_layout_def, dload_live_site_def] >>
     qpat_x_assum `!k' j' id' jd b' n' c' m.
       _ /\ _ /\ FLOOKUP (EL k' fs).dr_target id' = _ /\ _ ==> _`
       irule >> simp[] >> metis_tac[]) >>
  decide_tac
QED

Theorem dload_codecopy_state_ghost:
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst;src;sz] /\
  i.inst_outputs = [] /\ eval_operand dst s = SOME b /\
  eval_operand src s = SOME a /\ eval_operand sz s = SOME n /\
  step_inst_base i s = OK t ==>
  t = write_memory_with_expansion (w2n b)
    (TAKE (w2n n) (DROP (w2n a) s.vs_code ++ REPLICATE (w2n n) 0w)) s /\
  step_prov PG G i t = G /\
  step_taint i s t tn = tn with t_mem :=
    tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b + w2n n}
Proof
  strip_tac >>
  drule_all codecopy_no_new_site_bytes >> strip_tac >>
  drule_all codecopy_mem_taint >> strip_tac >>
  conj_asm1_tac >- (gvs[step_inst_base_def]) >>
  conj_tac >- simp[step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  simp[step_taint_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, write_memory_with_expansion_def] >>
  simp[DRESTRICT_UNIV, taint_component_equality]
QED

Theorem dload_scratch_codecopy_memory:
  dload_memory_match lo fs tn un s t /\
  (!x. x < lo ==> ~(w2n b <= x /\ x < w2n b+w2n n)) /\
  (!owner id a c m k. dload_live_site fs owner id a c m /\ k < m ==>
    ~(w2n b <= c+k /\ c+k < w2n b+w2n n)) /\
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst t = SOME b /\ eval_operand src t = SOME off /\
  eval_operand sz t = SOME n /\ step_inst_base i t = OK u ==>
  dload_memory_match lo fs tn
    (un with t_mem := un.t_mem DIFF {j | w2n b <= j /\ j < w2n b+w2n n}) s u
Proof
  strip_tac >>
  `!x. ~(w2n b <= x /\ x < w2n b+w2n n) ==>
    read_byte x u.vs_memory = read_byte x t.vs_memory` by
    (rpt strip_tac >> irule codecopy_byte_outside >>
     qexistsl [`off`,`b`,`dst`,`i`,`n`,`sz`,`src`] >> simp[]) >>
  fs[dload_memory_match_def] >> conj_tac >> rpt strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem dload_boundary_core_scratch_codecopy:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  (!x. x < lo ==> ~(w2n b <= x /\ x < w2n b+w2n n)) /\
  (!owner id a c m k. dload_live_site fs owner id a c m /\ k < m ==>
    ~(w2n b <= c+k /\ c+k < w2n b+w2n n)) /\
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst;src;sz] /\
  i.inst_outputs = [] /\ eval_operand dst t = SOME b /\
  eval_operand src t = SOME off /\ eval_operand sz t = SOME n /\
  step_inst_base i t = OK u ==>
  dload_boundary_core lo fs V Ws PG PH G (step_prov PH H i u)
    tn (step_taint i t u un) s u cs ds
Proof
  strip_tac >> drule_all dload_codecopy_state_ghost >> strip_tac >>
  `dload_memory_match lo fs tn
    (un with t_mem := un.t_mem DIFF {j | w2n b <= j /\ j < w2n b+w2n n}) s u` by
    (irule dload_scratch_codecopy_memory >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qexistsl [`dst`,`i`,`off`,`src`,`sz`,`t`] >>
     fs[dload_boundary_core_def]) >>
  `dload_table_stack fs (s::MAP (\c. c.cf_state) cs)
     (u::MAP (\d. d.cf_state) ds)` by
    (drule dload_boundary_tables >> strip_tac >>
     simp[dload_table_stack_def] >>
     gvs[dload_table_stack_def] >> gen_tac >>
     Cases_on `k`
     >- (first_x_assum (qspec_then `0` mp_tac) >>
         simp[write_memory_with_expansion_def]) >>
     first_x_assum (qspec_then `SUC n'` mp_tac) >>
     simp[write_memory_with_expansion_def]) >>
  `dload_equal_environment s u` by
    (drule dload_boundary_environment >>
     simp[write_memory_with_expansion_def, dload_equal_environment_def,
          venom_state_component_equality]) >>
  gvs[dload_boundary_core_def] >>
  fs[write_memory_with_expansion_def, dload_vars_match_def,
     lookup_var_def, dload_shared_store_def] >>
  gen_tac >> first_x_assum (qspec_then `a` mp_tac) >> simp[]
QED

Theorem dload_read_ghost_updates:
  (i.inst_opcode = DLOAD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = ILOAD) /\
  i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out value s) = set_prov G [out] NONE /\
  step_taint i s (update_var out value s) tn =
    tn with t_var := set_var_taint tn.t_var [out] (out_taint tn i s)
Proof
  strip_tac >> gvs[] >>
  simp[step_prov_def, out_prov_def, step_taint_def, mem_taint_def,
       adopt_reset_def, store_taint_def, imm_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, written_taint_def,
       FLOOKUP_DEF, taint_component_equality, EXTENSION] >>
  simp[SF CONJ_ss] >>
  namedCases_on `i.inst_operands` ["", "a ops"] >> simp[] >>
  namedCases_on `ops` ["", "b ops1"] >> simp[] >>
  namedCases_on `ops1` ["", "c ops2"] >> simp[] >>
  Cases_on `ops2` >> simp[]
QED

Theorem dload_boundary_core_read_pair:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = DLOAD /\ j.inst_opcode = MLOAD /\
  i.inst_outputs = [out] /\ j.inst_outputs = [out] /\
  out_taint tn i s = {} /\ out_taint un j t = {} ==>
  dload_boundary_core lo fs V Ws PG PH
    (step_prov PG G i (update_var out value s))
    (step_prov PH H j (update_var out value t))
    (step_taint i s (update_var out value s) tn)
    (step_taint j t (update_var out value t) un)
    (update_var out value s) (update_var out value t) cs ds
Proof
  strip_tac >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
     (tn with t_var := set_var_taint tn.t_var [out] {})
     (un with t_var := set_var_taint un.t_var [out] {})
     (update_var out value s) (update_var out value t)` by
    (irule dload_vars_match_write >>
     simp[dload_value_word_def, word_agree_except_def] >>
     drule dload_boundary_vars >>
     simp[dload_vars_match_def]) >>
  simp[dload_read_ghost_updates] >>
  simp[update_var_def] >>
  irule (GEN_ALL (SRULE [] (Q.INST
    [`si` |-> `s.vs_inst_idx`, `ti` |-> `t.vs_inst_idx`]
    (SPEC_ALL dload_boundary_core_var_index_update)))) >>
  conj_tac >- fs[update_var_def] >>
  qexistsl [`G`,`H`] >> simp[]
QED

Theorem dload_boundary_core_add_temporary:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = ADD /\ i.inst_outputs = [tmp] /\ tmp NOTIN V /\
  step_inst_base i t = OK u ==>
  dload_boundary_core lo fs V Ws PG PH G (step_prov PH H i u)
    tn (step_taint i t u un) s u cs ds
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base i t = OK u` mp_tac >>
  simp[step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `step_taint i t (update_var tmp (v1+v2) t) un =
    un with t_var := set_var_taint un.t_var [tmp] (out_taint un i t)` by
    (simp[step_taint_def, mem_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def, update_var_def, new_site_bytes_def,
      step_writes_def, range_bytes_def, source_memory_write_ranges_def,
      written_taint_def, FLOOKUP_DEF, taint_component_equality, EXTENSION] >>
     simp[SF CONJ_ss]) >>
  simp[step_prov_def] >> irule dload_boundary_core_target_temporary >> simp[]
QED

Theorem dload_scratch_alloca_result:
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [av] /\
  off <> Var av /\ eval_operand off t = SOME x /\
  exec_alloca a t (32w:bytes32) = OK u ==>
  ?b n. lookup_var av u = SOME (n2w b) /\
    FLOOKUP u.vs_allocas a.inst_id = SOME (b,n) /\
    eval_operand off u = SOME x /\
    u.vs_alloca_next <= t.vs_alloca_next + 32 /\
    u.vs_code = t.vs_code /\ u.vs_data_section = t.vs_data_section /\
    u.vs_labels = t.vs_labels
Proof
  strip_tac >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, dimword_def] >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `off` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem dload_scratch_site_bounds:
  dload_live_layout lo sf tf fs /\ j < LENGTH fs /\
  aid IN (EL j fs).dr_scratch /\
  FLOOKUP (EL j fs).dr_target aid = SOME (b,n) ==>
  n = 32 /\ lo <= b /\ b+32 <= tf /\ b < dimword (:256)
Proof
  strip_tac >>
  `dload_frame_sites (EL j fs)` by
    (fs[dload_live_layout_def, EVERY_EL] >> metis_tac[]) >>
  `n = 32` by (fs[dload_frame_sites_def] >> metis_tac[]) >>
  `lo <= b /\ b+n <= tf` by (fs[dload_live_layout_def] >> metis_tac[]) >>
  fs[dload_live_layout_def] >> decide_tac
QED

Theorem dload_alloca_conditional_frontier:
  t.vs_alloca_next < dimword(:256) /\
  (FLOOKUP t.vs_allocas aid = NONE ==> t.vs_alloca_next + w2n amount < dimword(:256)) /\
  a.inst_id = aid /\ exec_alloca a t (amount:bytes32) = OK t1 ==>
  t1.vs_alloca_next < dimword(:256)
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def] >> metis_tac[]
QED

Theorem dload_four_step_boundary_fresh:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ a.inst_id NOTIN orig /\
  (FLOOKUP t.vs_allocas a.inst_id = NONE ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\ b.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var cv;Lit 32w] /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  av <> cv /\ av NOTIN V /\ cv NOTIN V /\ off <> Var av /\
  code_layout_valid t /\ eval_operand off s = SOME x /\ eval_operand off t = SOME x /\
  eval_operand (Label "code_end") t = SOME e /\ w2n x + w2n e < dimword (:256) /\
  dload_prefix_match fuel Ct PH [a;b;c;d] 4 t H un t4 H4 un4 ==>
  ?s1 r1.
    step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\ r1.dr_scratch = a.inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds
Proof
  strip_tac >> drule dload_four_step_replay >> strip_tac >>
  `exec_alloca a t (32w:bytes32) = OK v1` by
    (qpat_x_assum `step_inst fuel Ct a t = OK v1` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, eval_operand_def]) >>
  `t.vs_alloca_next < dimword (:256)` by
    (drule dload_boundary_layout >> simp[dload_live_layout_def]) >>
  `v1.vs_alloca_next < dimword (:256)` by
    (irule dload_alloca_conditional_frontier >>
     qexistsl [`a`,`a.inst_id`,`(32w:bytes32)`,`t`] >> fs[dimword_def]) >>
  drule_all dload_boundary_core_scratch_alloca >> strip_tac >>
  suspend "after_alloca"
QED

Resume dload_four_step_boundary_fresh[after_alloca]:
  `dload_boundary_core lo (r1::rs) V Ws PG PH G H1 tn un1 s t1 cs ds` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s v1 _ _`
       (mp_then Any mp_tac dload_boundary_core_index_update) >>
     disch_then (qspecl_then [`SUC t.vs_inst_idx`,`s.vs_inst_idx`] mp_tac) >>
     simp[]) >>
  `step_inst_base b t1 = OK v2` by
    (qpat_x_assum `step_inst fuel Ct b t1 = OK v2` mp_tac >>
     simp[step_inst_non_invoke]) >>
  `dload_boundary_core lo (r1::rs) V Ws PG PH G H2 tn un2 s v2 cs ds` by
    (qpat_assum `H2 = _` SUBST1_TAC >>
     qpat_assum `un2 = _` SUBST1_TAC >>
     irule dload_boundary_core_add_temporary >> metis_tac[]) >>
  `dload_boundary_core lo (r1::rs) V Ws PG PH G H2 tn un2 s t2 cs ds` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s v2 _ _`
       (mp_then Any mp_tac dload_boundary_core_index_update) >>
     disch_then (qspecl_then [`SUC t1.vs_inst_idx`,`s.vs_inst_idx`] mp_tac) >>
     simp[]) >>
  suspend "before_copy"
QED
Resume dload_four_step_boundary_fresh[before_copy]:
  drule_all dload_scratch_alloca_result >>
  disch_then (qx_choose_then `bb` (qx_choose_then `nn` strip_assume_tac)) >>
  `eval_operand off t1 = SOME x /\
   eval_operand (Label "code_end") t1 = SOME e` by
    fs[eval_op_inst_idx, eval_operand_def] >>
  `v2 = update_var cv (x+e) t1` by
    (qpat_x_assum `step_inst_base b t1 = OK v2` mp_tac >>
     simp[step_inst_base_def, exec_pure2_def] >>
     gvs[eval_op_inst_idx, eval_operand_def]) >>
  `eval_operand (Var av) t2 = SOME (n2w bb) /\
   eval_operand (Var cv) t2 = SOME (x+e) /\
   eval_operand (Lit 32w) t2 = SOME 32w /\
   t2.vs_allocas = v1.vs_allocas /\
   t2.vs_alloca_next = v1.vs_alloca_next` by
    fs[eval_operand_def, eval_op_inst_idx, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  suspend "copy_fields"
QED
Resume dload_four_step_boundary_fresh[copy_fields]:
  drule dload_boundary_layout >> strip_tac >>
  `nn = 32 /\ lo <= bb /\ bb+32 <= t2.vs_alloca_next /\ bb < dimword (:256)` by
    (irule dload_scratch_site_bounds >>
     qexistsl [`a.inst_id`,`r1::rs`,`0`,`s.vs_alloca_next`] >>
     simp[] >> fs[FLOOKUP_DEF]) >>
  `(!z. z < lo ==> ~(bb <= z /\ z < bb+32)) /\
   (!owner id aa cc m k. dload_live_site (r1::rs) owner id aa cc m /\ k < m ==>
     ~(bb <= cc+k /\ cc+k < bb+32))` by
    (irule dload_scratch_copy_separation >>
     conj_tac
     >- (qexistsl [`a.inst_id`,`0`] >> simp[] >> fs[FLOOKUP_DEF]) >>
     metis_tac[]) >>
  `step_inst_base c t2 = OK v3` by
    (qpat_x_assum `step_inst fuel Ct c t2 = OK v3` mp_tac >>
     simp[step_inst_non_invoke]) >>
  `dload_boundary_core lo (r1::rs) V Ws PG PH G H3 tn un3 s v3 cs ds` by
    (qpat_assum `H3 = _` SUBST1_TAC >> qpat_assum `un3 = _` SUBST1_TAC >>
     irule dload_boundary_core_scratch_codecopy >>
     simp[IgnAsm `t2 = _`, IgnAsm `H2 = _`, IgnAsm `un2 = _`,
          w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  `dload_boundary_core lo (r1::rs) V Ws PG PH G H3 tn un3 s t3 cs ds` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s v3 _ _`
       (mp_then Any mp_tac dload_boundary_core_index_update) >>
     disch_then (qspecl_then [`SUC t2.vs_inst_idx`,`s.vs_inst_idx`] mp_tac) >>
     simp[]) >>
  suspend "after_copy"
QED
Resume dload_four_step_boundary_fresh[after_copy]:
  `s.vs_data_section = t.vs_data_section` by
    (last_assum (mp_then Any mp_tac dload_boundary_environment) >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `lookup_var out t4 = SOME (word_of_bytes T (0w:bytes32)
     (TAKE 32 (DROP (w2n x) s.vs_data_section ++ REPLICATE 32 0w)))` by
    (drule_at (Pat `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`)
       dload_expansion_replay_value >> simp[]) >>
  qmatch_asmsub_abbrev_tac `lookup_var out t4 = SOME value` >>
  `eval_operand (Var av) t3 = SOME (n2w bb)` by
    (drule_all dload_codecopy_state_ghost >> strip_tac >>
     gvs[eval_operand_def, lookup_var_def, write_memory_with_expansion_def,
         update_var_def]) >>
  `v4 = update_var out value t3` by
    (qpat_x_assum `step_inst fuel Ct d t3 = OK v4` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def] >>
     strip_tac >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `out_taint tn i s = {} /\ out_taint un3 d t3 = {}` by
    (`mem_word_taint (mem_taint un2 c t2 v3) (w2n (n2w bb:bytes32)) = {}` by
       (irule codecopy_scratch_step_untainted >>
        simp[IgnAsm `t2 = _`] >> metis_tac[]) >>
     `un3.t_mem = mem_taint un2 c t2 v3` by
       (qpat_assum `un3 = _` SUBST1_TAC >>
        simp_tac (srw_ss()) [step_taint_def, LET_THM]) >>
     qpat_x_assum `un3 = _` kall_tac >>
     qpat_x_assum `un2 = _` kall_tac >>
     qpat_x_assum `t3 = _` kall_tac >>
     qpat_x_assum `t2 = _` kall_tac >>
     simp[out_taint_def]) >>
  suspend "paired_read"
QED
Resume dload_four_step_boundary_fresh[paired_read]:
  `step_inst fuel C i s = OK (update_var out value s)` by
    (qpat_x_assum `s.vs_data_section = t.vs_data_section` kall_tac >>
     simp[Abbr `value`] >> irule dload_source_read_step >> metis_tac[]) >>
  `dload_boundary_core lo (r1::rs) V Ws PG PH
     (step_prov PG G i (update_var out value s))
     (step_prov PH H3 d (update_var out value t3))
     (step_taint i s (update_var out value s) tn)
     (step_taint d t3 (update_var out value t3) un3)
     (update_var out value s) (update_var out value t3) cs ds` by
    (irule dload_boundary_core_read_pair >> metis_tac[]) >>
  qexistsl [`update_var out value s`,`r1`] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qpat_assum `t4 = _` SUBST1_TAC >>
  qpat_assum `H4 = _` SUBST1_TAC >>
  qpat_assum `un4 = _` SUBST1_TAC >>
  qpat_assum `v4 = _` SUBST1_TAC >>
  first_assum (mp_then Any mp_tac dload_boundary_core_index_update) >>
  disch_then (qspecl_then [`SUC t3.vs_inst_idx`,`SUC s.vs_inst_idx`] mp_tac) >>
  simp_tac (srw_ss()) []
QED
Finalise dload_four_step_boundary_fresh

Theorem dload_four_step_boundary:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ a.inst_id NOTIN orig /\
  t.vs_alloca_next + 32 < dimword (:256) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\ b.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var cv;Lit 32w] /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  av <> cv /\ av NOTIN V /\ cv NOTIN V /\ off <> Var av /\
  code_layout_valid t /\ eval_operand off s = SOME x /\ eval_operand off t = SOME x /\
  eval_operand (Label "code_end") t = SOME e /\ w2n x + w2n e < dimword (:256) /\
  dload_prefix_match fuel Ct PH [a;b;c;d] 4 t H un t4 H4 un4 ==>
  ?s1 r1.
    step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\ r1.dr_scratch = a.inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds
Proof
  strip_tac >> irule dload_four_step_boundary_fresh >> metis_tac[]
QED

Theorem dload_supply_replay_boundary_fresh:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ (EL 0 xs).inst_id NOTIN orig /\
  (FLOOKUP t.vs_allocas (EL 0 xs).inst_id = NONE ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN V /\ cv NOTIN V /\ off <> Var av /\
  code_layout_valid s /\ dload_offset_ok C fn i s /\
  eval_operand off s = SOME x /\ eval_operand off t = SOME x /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 ==>
  ?s1 r1. step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\
    r1.dr_scratch = (EL 0 xs).inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds
Proof
  strip_tac >>
  `dload_equal_environment s t` by (drule dload_boundary_environment >> simp[]) >>
  `code_layout_valid t /\ s.vs_data_section = t.vs_data_section /\
   s.vs_code = t.vs_code /\ s.vs_labels = t.vs_labels` by
    (gvs[dload_equal_environment_def, venom_state_component_equality,
         code_layout_valid_def] >> metis_tac[]) >>
  `?e. eval_operand (Label "code_end") t = SOME e /\
       w2n x + w2n e < dimword (:256)` by
    (gvs[code_layout_valid_def, dload_offset_ok_def, eval_operand_def] >>
     `LENGTH t.vs_code - LENGTH t.vs_data_section < dimword (:256)` by
       (fs[dimword_def] >> decide_tac) >>
     simp[w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  drule_all dload_supply_expansion >> strip_tac >> gvs[] >>
  drule_at (Pat `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`)
    dload_four_step_boundary_fresh >> simp[] >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem dload_supply_replay_boundary:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ (EL 0 xs).inst_id NOTIN orig /\
  t.vs_alloca_next + 32 < dimword (:256) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN V /\ cv NOTIN V /\ off <> Var av /\
  code_layout_valid s /\ dload_offset_ok C fn i s /\
  eval_operand off s = SOME x /\ eval_operand off t = SOME x /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 ==>
  ?s1 r1. step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\
    r1.dr_scratch = (EL 0 xs).inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds
Proof
  strip_tac >> irule dload_supply_replay_boundary_fresh >> metis_tac[]
QED
