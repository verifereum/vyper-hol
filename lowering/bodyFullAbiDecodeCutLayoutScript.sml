Theory bodyFullAbiDecodeCutLayout
Ancestors
  exprSimAbiGasBridge fragExec compileEnv venomExecSemantics venomInst
  venomState venomExecProofs list rich_list arithmetic exprLoweringProps

(* Before the first close, the current prefix of b still belongs to the
   oldest emitted block. The replacement at L changes only its old prefix. *)
Theorem abi_decode_cut_entry_slice:
  cs_extends start a /\ cs_extends a b /\ cs_extends b final /\
  a.cs_blocks = start.cs_blocks /\ b.cs_blocks = start.cs_blocks /\
  start.cs_blocks <> final.cs_blocks /\ LENGTH ids = LENGTH start.cs_current_insts /\
  fn_has_code start final fn /\
  fn_has_code (start_relabel L ids start) (start_swap start L ids final)
    (frag_relabel_observer start final L ids fn id) ==>
  ?orig shadow.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME orig /\
    lookup_block L (frag_relabel_observer start final L ids fn id).fn_blocks = SOME shadow /\
    isPREFIX (emitted_insts a b)
      (DROP (LENGTH a.cs_current_insts) shadow.bb_instructions) /\
    !idx. LENGTH a.cs_current_insts <= idx ==>
      get_instruction shadow idx = get_instruction orig idx
Proof
  strip_tac >>
  `emitted_blocks b final = emitted_blocks start final` by
    simp[emitted_blocks_def] >>
  `emitted_blocks start final <> []` by
    (drule frag_extends_emitted_shape >> simp[]) >>
  `emitted_blocks start a = [] /\ emitted_blocks a b = []` by
    simp[emitted_blocks_def] >>
  `a.cs_current_bb = b.cs_current_bb /\
   isPREFIX start.cs_current_insts a.cs_current_insts /\
   isPREFIX a.cs_current_insts b.cs_current_insts` by
    metis_tac[frag_extends_emitted_shape] >>
  `b.cs_blocks <> final.cs_blocks /\ cs_extends start final` by
    metis_tac[cs_extends_trans] >>
  qabbrev_tac `new = emitted_blocks start final` >>
  `isPREFIX b.cs_current_insts (LAST new).bb_instructions /\
   (LAST new).bb_label = b.cs_current_bb` by
    (qpat_assum `cs_extends b final` (mp_then Any mp_tac frag_extends_emitted_shape) >>
     simp[Abbr `new`]) >>
  `isPREFIX start.cs_current_insts (LAST new).bb_instructions` by
    metis_tac[isPREFIX_TRANS] >>
  drule_all start_swap_emitted_shape >>
  disch_then (qspecl_then [`ids`, `L`] strip_assume_tac) >>
  qabbrev_tac `shadow = LAST new with <|bb_label := L;
    bb_instructions := MAP (\j. mk_inst j NOP [] []) ids ++
      DROP (LENGTH start.cs_current_insts) (LAST new).bb_instructions|>` >>
  `shadow.bb_label = L` by simp[Abbr `shadow`] >>
  qexistsl_tac [`LAST new`, `shadow`] >> rpt conj_tac
  >- (fs[fn_has_code_def] >> metis_tac[MEM_LAST_NOT_NIL])
  >- (fs[fn_has_code_def] >> metis_tac[MEM_LAST_NOT_NIL])
  >- (`LENGTH start.cs_current_insts <= LENGTH a.cs_current_insts` by
        metis_tac[IS_PREFIX_LENGTH] >>
      `DROP (LENGTH a.cs_current_insts) shadow.bb_instructions =
       DROP (LENGTH a.cs_current_insts) (LAST new).bb_instructions` by
        simp[Abbr `shadow`, DROP_APPEND2, DROP_DROP_T, SUB_ADD] >>
      qpat_assum `isPREFIX b.cs_current_insts (LAST new).bb_instructions`
        (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
      `LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts` by
        metis_tac[IS_PREFIX_LENGTH] >>
      simp[emitted_insts_def, DROP_APPEND1, IS_PREFIX_APPEND]) >>
  rpt strip_tac >>
  `LENGTH start.cs_current_insts <= idx` by
    metis_tac[IS_PREFIX_LENGTH, LESS_EQ_TRANS] >>
  drule_all frag_relabel_entry_instruction >> simp[Abbr `shadow`]
QED

(* Once the first block was emitted, swapping it modifies only the
   shared suffix of the two compiler histories. *)
Theorem cut_swap_after[local]:
  cs_extends start a /\ cs_extends a b /\ start.cs_blocks <> a.cs_blocks ==>
  cs_extends (start_swap start L ids a) (start_swap start L ids b) /\
  emitted_blocks (start_swap start L ids a) (start_swap start L ids b) =
    emitted_blocks a b
Proof
  strip_tac >>
  qpat_assum `cs_extends start a`
    (qx_choose_then `xs` strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
  qpat_assum `cs_extends a b`
    (qx_choose_then `ys` strip_assume_tac o REWRITE_RULE [cs_extends_def]) >>
  `xs <> []` by (strip_tac >> gvs[]) >>
  `emitted_blocks start a = xs /\ emitted_blocks a b = ys /\
   emitted_blocks start b = ys ++ xs` by
    (rpt conj_tac >> irule emitted_blocks_append >> fs[APPEND_ASSOC]) >>
  `(start_swap start L ids b).cs_blocks = ys ++ (start_swap start L ids a).cs_blocks` by
    simp[start_swap_def, NULL_EQ, FRONT_APPEND_NOT_NIL, LAST_APPEND_NOT_NIL,
         APPEND_ASSOC, DROP_APPEND2, DROP_LENGTH_APPEND] >>
  reverse conj_tac >- metis_tac[emitted_blocks_append] >>
  simp[cs_extends_def, start_swap_def, NULL_EQ, FRONT_APPEND_NOT_NIL,
       LAST_APPEND_NOT_NIL, APPEND_ASSOC, DROP_APPEND2, DROP_LENGTH_APPEND]
QED

Theorem abi_decode_cut_after_has_code:
  cs_extends start a /\ cs_extends a b /\ cs_extends b final /\
  start.cs_blocks <> a.cs_blocks /\
  fn_has_code (start_relabel L ids start) (start_swap start L ids final)
    (frag_relabel_observer start final L ids fn id) ==>
  fn_has_code a b (frag_relabel_observer start final L ids fn id)
Proof
  strip_tac >>
  `cs_extends start b /\ start.cs_blocks <> b.cs_blocks` by
    (conj_tac >- metis_tac[cs_extends_trans] >>
     fs[cs_extends_def] >> strip_tac >> gvs[] >> fs[GSYM APPEND_ASSOC]) >>
  `fn_has_code (start_swap start L ids a) (start_swap start L ids b)
     (frag_relabel_observer start final L ids fn id)` by
    (irule fn_has_code_mid >> conj_tac >- metis_tac[cut_swap_after] >>
     qexistsl_tac [`start_swap start L ids final`, `start_relabel L ids start`] >>
     simp[] >> metis_tac[start_relabel_extends, cut_swap_after]) >>
  `emitted_blocks (start_swap start L ids a) (start_swap start L ids b) =
   emitted_blocks a b` by metis_tac[cut_swap_after] >>
  `(start_swap start L ids b).cs_current_bb = b.cs_current_bb /\
   (start_swap start L ids b).cs_current_insts = b.cs_current_insts` by
    metis_tac[start_swap_fields] >>
  fs[fn_has_code_def]
QED

(* The artificial STOP is separate from genuine decoder instructions.
   A jump on the genuine suffix cannot return to L. Jump targets off L
   need no PHI processing, including the synthetic exit block. *)
Theorem abi_decode_cut_shadow_controls:
  cs_extends start final /\ start.cs_blocks <> final.cs_blocks /\
  LENGTH ids = LENGTH start.cs_current_insts /\ frag_ops_free start final /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code start final) ==>
  (!lbl idx bb inst.
    (lbl = L ==> LENGTH start.cs_current_insts <= idx) /\
    (lbl,idx) <> frag_observer_cut final /\
    lookup_block lbl (frag_relabel_observer start final L ids fn id).fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==>
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN /\
    (!s t. MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base inst s = OK t ==>
      t.vs_current_bb <> L)) /\
  (!lbl bb. lbl <> L /\ lookup_block lbl (frag_relabel_observer start final L ids fn id).fn_blocks = SOME
    bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (?bb. lookup_block (FST (frag_observer_cut final)) (frag_relabel_observer start final L ids fn
    id).fn_blocks = SOME bb /\
    get_instruction bb (SND (frag_observer_cut final)) = SOME (mk_inst id STOP [] []))
Proof
  strip_tac >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all frag_relabel_code_provenance >> strip_tac >>
      `inst.inst_opcode <> GAS /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
       inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN` by
        (fs[frag_ops_free_def, EVERY_MEM] >> metis_tac[]) >>
      simp[] >> rpt gen_tac >> disch_tac >>
      irule frag_relabel_jump_no_reentry >> fs[EVERY_MEM] >> metis_tac[]) >>
  reverse conj_tac
  >- simp[frag_observer_cut_def, frag_relabel_observer_cut, frag_observer_cut_instruction] >>
  rpt gen_tac >> strip_tac >> drule frag_relabel_observer_lookup_cases >> strip_tac
  >- metis_tac[frag_relabel_observer_phi_zero] >>
  drule_all start_swap_emitted_blocks >> strip_tac >>
  fs[MEM_APPEND] >> gvs[] >>
  irule no_phis_phi_prefix_length_zero >> metis_tac[frag_relabel_front_nonphi]
QED
