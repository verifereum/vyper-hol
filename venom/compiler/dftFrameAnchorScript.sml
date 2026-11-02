(* Successful current-block prefixes anchored at a reachable block entry. *)
Theory dftFrameAnchor
Ancestors
  dftFramePrefix o1PassLift venomWf venomInst venomExecSemantics
  dftCorrectnessFinal contextCodegenRel venomInstProofs
  list rich_list arithmetic

Definition dft_block_anchor_def:
  dft_block_anchor C f g s0 j t <=>
    ?v e bb pre xs post i.
      enters_block g v e /\ frame_reach C f s0 i e /\
      MEM bb g.fn_blocks /\ bb.bb_label = e.vs_current_bb /\
      bb.bb_instructions = pre ++ xs ++ j::post /\
      LENGTH pre = e.vs_inst_idx /\ dft_prefix C xs e t
End

Theorem dft_block_anchor_entry:
  enters_block g v e /\ active_inst g j e /\
  frame_reach C f s0 i e ==> dft_block_anchor C f g s0 j e
Proof
  simp[active_inst_def, dft_block_anchor_def] >> strip_tac >>
  qexistsl [`v`, `e`, `bb`, `TAKE e.vs_inst_idx bb.bb_instructions`,
            `[]`, `DROP (SUC e.vs_inst_idx) bb.bb_instructions`, `i`] >>
  gvs[] >> simp[TAKE_DROP_SUC]
QED

Theorem dft_block_anchor_next:
  wf_function g /\ dft_block_anchor C f g s0 j t /\
  ~is_terminator j.inst_opcode /\ step_inst fuel C j t = OK u /\
  active_inst g k (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  dft_block_anchor C f g s0 k (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[dft_block_anchor_def, active_inst_def] >> strip_tac >>
  `t.vs_current_bb = e.vs_current_bb /\
   t.vs_inst_idx = e.vs_inst_idx + LENGTH xs` by
    metis_tac[dft_prefix_control] >>
  `u.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `bb' = bb` by metis_tac[wf_fn_blocks_same_label_eq] >> gvs[] >>
  `0 < LENGTH post` by decide_tac >>
  Cases_on `post` >- gvs[] >>
  qexistsl [`v`, `e`, `bb`, `pre`, `xs ++ [j]`, `t'`, `i`] >>
  simp[APPEND_ASSOC, dft_prefix_append] >>
  conj_tac
  >- (simp[EL_APPEND_EQN] >> `SUC (LENGTH xs + e.vs_inst_idx) -
        (LENGTH xs + e.vs_inst_idx) = 1` by decide_tac >> simp[]) >>
  qexists_tac `t` >> simp[dft_prefix_cons] >>
  qexistsl [`fuel`, `u`] >> simp[]
QED

Theorem frame_reach_block_anchor:
  !C f s0 j t. frame_reach C f s0 j t ==>
    wf_function f ==> dft_block_anchor C f f s0 j t
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac >> rpt strip_tac
  >- metis_tac[dft_block_anchor_entry, frame_reach_rules]
  >- metis_tac[dft_block_anchor_next]
  >> metis_tac[dft_block_anchor_entry, frame_reach_rules]
QED
