Theory bodyAbiDecodeGuardedLoopCutReplayMods
Ancestors
  bodyFullAbiDecodeCutLayout bodyFullAbiDecodeCutFirstJump
  bodyFullAbiDecodeCutAfterPath bodyFullAbiDecodeCutPath
  exprSimAbiDecodeSiteCoverage exprSimAbiGasBridge fragExec fragGasPath
  compileEnv venomInst venomState venomExecSemantics list rich_list relation
Libs
  bodyFullAbiDecodeCutArraySyntaxLib

(* The entry JMP is the first newly emitted instruction in the shadow block. *)
Theorem cut_loop_jump_layout[local]:
  cs_extends cut_start a /\ cs_extends a h /\ cs_extends h cut_finish /\
  h.cs_blocks = <|bb_label := a.cs_current_bb;
    bb_instructions := a.cs_current_insts ++
      [mk_inst a.cs_next_id JMP [Label h.cs_current_bb] []]|> :: a.cs_blocks /\
  a.cs_blocks = cut_start.cs_blocks /\
  LENGTH ids = LENGTH cut_start.cs_current_insts /\
  fn_has_code cut_start cut_finish fn /\
  fn_has_code (start_relabel L ids cut_start) (start_swap cut_start L ids cut_finish)
    (frag_relabel_observer cut_start cut_finish L ids fn id) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code cut_start cut_finish) ==>
  h.cs_blocks <> cut_start.cs_blocks /\ h.cs_current_bb <> L /\
  ?shadow. lookup_block L (frag_relabel_observer cut_start cut_finish L ids fn id).fn_blocks =
             SOME shadow /\
    get_instruction shadow (LENGTH a.cs_current_insts) =
      SOME (mk_inst a.cs_next_id JMP [Label h.cs_current_bb] [])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `v = <|bb_label := a.cs_current_bb;
    bb_instructions := a.cs_current_insts ++
      [mk_inst a.cs_next_id JMP [Label h.cs_current_bb] []]|>` >>
  `emitted_blocks a h = [v]` by (irule emitted_blocks_append >> simp[]) >>
  `h.cs_blocks <> cut_start.cs_blocks /\ cut_start.cs_blocks <> cut_finish.cs_blocks` by
    (qpat_assum `cs_extends h cut_finish` (strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
     gvs[] >> simp[]) >>
  `MEM (mk_inst a.cs_next_id JMP [Label h.cs_current_bb] []) (frag_code a h)` by
    simp[frag_code_def, Abbr `v`, DROP_APPEND1] >>
  `h.cs_current_bb <> L` by
    (`MEM (mk_inst a.cs_next_id JMP [Label h.cs_current_bb] []) (frag_code cut_start cut_finish)` by
       metis_tac[abi_decode_frag_code_left_inclusion, abi_decode_frag_code_right_inclusion,
                 cs_extends_trans] >>
     fs[EVERY_MEM] >>
     qpat_assum `!i. MEM i (frag_code cut_start cut_finish) ==> _`
       (qspec_then `mk_inst a.cs_next_id JMP [Label h.cs_current_bb] []`
          (fn th => first_assum (assume_tac o MATCH_MP th))) >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `fn_has_code a h fn` by metis_tac[fn_has_code_mid] >>
  `lookup_block a.cs_current_bb fn.fn_blocks = SOME v` by
    (qpat_assum `fn_has_code a h fn` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
     `v.bb_label = a.cs_current_bb` by simp[Abbr `v`] >>
     `MEM v (emitted_blocks a h)` by simp[MEM] >> metis_tac[]) >>
  simp[] >>
  mp_tac (Q.INST [`start` |-> `cut_start`, `final` |-> `cut_finish`, `b` |-> `a`]
    abi_decode_cut_entry_slice) >>
  (impl_tac >- (simp[cs_extends_refl] >> metis_tac[cs_extends_trans])) >>
  disch_then (qx_choose_then `orig` (qx_choose_then `shadow` strip_assume_tac)) >>
  qexists `shadow` >> simp[] >>
  qpat_assum `!idx. LENGTH a.cs_current_insts <= idx ==> _`
    (qspec_then `LENGTH a.cs_current_insts` mp_tac) >>
  gvs[get_instruction_def, Abbr `v`, EL_LENGTH_APPEND]
QED

val cut_loop_layout = ``^array_cut_layout /\
  cut = frag_observer_cut cut_finish /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code cut_start cut_finish)``;

(* Replay the entry JMP and transport the supplied tail without choosing a result. *)
Theorem abi_decode_guarded_loop_cut_replay_mods:
  ^cut_loop_layout /\ (^array_crossing) a b /\
  cs_extends a h /\ cs_extends h b /\
  h.cs_blocks = <|bb_label := a.cs_current_bb;
    bb_instructions := a.cs_current_insts ++
      [mk_inst a.cs_next_id JMP [Label h.cs_current_bb] []]|> :: a.cs_blocks /\
  (!obs. fn_has_code h b obs ==> gas_path ctx obs (jump_to h.cs_current_bb s) 0 r) /\
  ((?t. r = OK t /\ t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts) \/
   (?t. r = Abort Revert_abort t)) ==>
  (^array_shadow) a b s r
Proof
  simp_tac pure_ss [BETA_THM] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `cs_extends cut_start a /\ cs_extends h cut_finish /\ cs_extends cut_start h /\
   cs_extends cut_start cut_finish` by metis_tac[cs_extends_trans] >>
  qpat_x_assum `cut_observer = _` SUBST_ALL_TAC >>
  qpat_x_assum `cut = frag_observer_cut _` SUBST_ALL_TAC >>
  drule_all cut_loop_jump_layout >> strip_tac >>
  qabbrev_tac `v = frag_relabel_observer cut_start cut_finish L ids fn id` >>
  `fn_has_code h b v` by
    (simp[Abbr `v`] >> metis_tac[abi_decode_cut_after_has_code]) >>
  `?target. lookup_block h.cs_current_bb v.fn_blocks = SOME target` by
    metis_tac[fn_has_code_start] >>
  drule_all abi_decode_cut_shadow_controls >> simp_tac bool_ss [LET_THM] >>
  disch_then (qspecl_then [`id`,`fn`] strip_assume_tac) >>
  `phi_prefix_length target.bb_instructions = 0` by metis_tac[Abbr `v`] >>
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.vs_current_bb = L /\ u.vs_inst_idx = LENGTH a.cs_current_insts` by fs[] >>
  `(L,u.vs_inst_idx) <> frag_observer_cut cut_finish` by metis_tac[pairTheory.FST] >>
  `get_instruction shadow u.vs_inst_idx =
    SOME (mk_inst a.cs_next_id JMP [Label h.cs_current_bb] [])` by fs[] >>
  drule_all abi_decode_cut_first_jump >> strip_tac >>
  irule (BETA_RULE abi_decode_cut_prefix_bind) >>
  qexists `jump_to h.cs_current_bb u` >>
  (reverse conj_tac >-
    (irule RTC_SINGLE >> first_assum (qspec_then `ctx` (ACCEPT_TAC o CONJUNCT1)))) >>
  `lookup_block b.cs_current_bb v.fn_blocks <> NONE` by fs[fn_has_code_def] >>
  `(jump_to h.cs_current_bb u).vs_current_bb <> L` by simp[jump_to_def] >>
  qpat_assum `b.cs_blocks <> cut_start.cs_blocks` (fn th => simp_tac bool_ss [th]) >>
  match_mp_tac (BETA_RULE (Q.INST [`v` |-> `jump_to h.cs_current_bb s`, `n` |-> `0`]
    abi_decode_cut_after_path)) >>
  qpat_assum `!ctx. abi_observer_step ctx _ _ _ _ /\ _`
    (qspec_then `ctx` (assume_tac o (CONJUNCT1 o CONJUNCT2))) >>
  unabbrev_all_tac >> gvs[] >> rpt conj_tac
  >>~- ([`?bb id. lookup_block _ _ = SOME bb /\ _`],
        qexistsl [`bb`,`id`] >> simp[]) >>
  metis_tac[]
QED
