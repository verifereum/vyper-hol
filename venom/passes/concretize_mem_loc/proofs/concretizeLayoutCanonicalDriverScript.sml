Theory concretizeLayoutCanonicalDriver
Ancestors concretizeLayoutCanonicalIndex concretizeLayoutScopedRun
  concretizeLayoutScopedPhase concretizeLayoutAlignedControl
  concretizeLayoutPairedEntry concretizeLayoutStagePairing
  concretizeLayoutCallResult concretizeLayoutCompletedJump
  frameSelectedSimulation frameControlAgreement concretizeLayoutPhaseOrigin
  concretizeLayoutRunState concretizeLayoutBlockEntry concretizeLayoutPhaseCompose
  venomExecSemantics list arithmetic

(* All ordinary witnesses, including ending RET witnesses, are indexed in the
   ONE ambient decoration.  No canonical fact is attached to the ignored g of
   layout_scoped_run. *)
Definition layout_driver_indexed_def:
  layout_driver_indexed es ass a <=> layout_phase_canonical es a /\
    a.lop_anns = EL a.lop_cursor ass
End

Definition layout_canonical_ready_def:
  layout_canonical_ready vs0 C q0 es qs ass qend q n a p <=>
    ~a.lop_pending /\ a.lop_config = q /\ a.lop_cursor = n /\
    layout_driver_indexed es ass a /\
    layout_ordinary_trace vs0 C q0 es qs qend a p
End

(* A row is retained at the structural boundary.  It is NOT a hypothesis of
   target execution; stage_row_produce supplies it from the actual pass. *)
Definition layout_driver_row_def:
  layout_driver_row C' fn fn' positions <=>
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ?ctx reserved layout. layout_stage_row ctx reserved fn fn' layout /\
      positions = layout.cl_positions
End

Definition layout_canonical_run_def:
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t <=>
    MEM fn C.ctx_functions /\ (?positions. layout_driver_row C' fn fn' positions) /\
    ?a p p'. enters_block fn s p /\ enters_block fn' t p' /\
      layout_canonical_ready vs0 C q0 es qs ass qend q n a p /\
      layout_ordinary_state D lo C' q0 es qs a p p' /\ control_agree p p'
End

Definition layout_canonical_entry_def:
  (layout_canonical_entry D lo vs0 C C' q0 es qs ass qend q n (INL a) s t <=>
    layout_canonical_ready vs0 C q0 es qs ass qend q n a s /\
    layout_aligned_entry D lo vs0 C C' q0 es qs qend a s t) /\
  (layout_canonical_entry D lo vs0 C C' q0 es qs ass qend q n (INR a) s t <=>
    ~a.ltp_pending /\ layout_corridor_entry C a s t)
End

Definition layout_canonical_ret_def:
  layout_canonical_ret D lo vs0 C C' q0 es qs ass qend qe m ret s ret' t <=>
    ?b. b.lop_config = qe /\ b.lop_cursor = m /\
      layout_driver_indexed es ass b /\
      layout_ret_endpoint D lo vs0 C C' q0 es qs qend b s t ret ret'
End

(* This common non-OK relation is shared by step, block, and run outcomes.
   IntRet retains the exact ending cursor, BEFORE OriginResume is consumed. *)
Definition layout_canonical_result_def:
  layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe m r r' <=>
    case (r,r') of
      (Halt s,Halt t) => dead_result_rel D (Halt s) (Halt t)
    | (Abort a s,Abort b t) => dead_result_rel D (Abort a s) (Abort b t)
    | (IntRet ret s,IntRet ret' t) =>
        layout_canonical_ret D lo vs0 C C' q0 es qs ass qend qe m ret s ret' t
    | _ => F
End

Definition layout_canonical_block_witness_def:
  (layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend q n bb s bb' t (INL a) <=>
    layout_driver_indexed es ass a /\
    ?fn fn' positions. decoration_entry fn s q /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      MEM fn C.ctx_functions /\
      layout_driver_row C' fn fn' positions /\
      layout_paired_ordinary D lo vs0 C C' q0 es qs qend
        positions q n bb s bb' t a) /\
  (layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend q n bb s bb' t (INR a) <=>
    ~a.ltp_pending /\ a.ltp_origin.lbo_source = bb /\
    a.ltp_origin.lbo_target = bb' /\ layout_corridor_entry C a s t)
End

Definition layout_canonical_EB_def:
  layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb s bb' t <=>
    ?a. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      q n bb s bb' t a
End

(* Virtual NOP is deliberately not a target lookup. *)
Definition layout_canonical_step_witness_def:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend q n i s j t a <=>
    ?bb bb'. layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend
      q n bb s bb' t a /\ get_instruction bb s.vs_inst_idx = SOME i /\
      (case a of
        INL g => ?fn fn' positions. decoration_entry fn s q /\
          layout_driver_row C' fn fn' positions /\
          layout_block_pair positions bb bb' s.vs_inst_idx t.vs_inst_idx /\
          ((i.inst_opcode = NOP /\ j = i) \/
           ((concretize_inst_with_positions positions i).inst_opcode <> NOP /\
            j = concretize_inst_with_positions positions i))
      | INR g => get_instruction bb' t.vs_inst_idx = SOME j)
End

Definition layout_canonical_ES_def:
  layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t <=>
    layout_base_lookahead C q0 path q n i s /\
    ?a. layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend q n i s j t a
End

(* Base OK awaits OriginOrdinary at m; INVOKE OK has already consumed the
   resume in its semantic payload (ready at SUC m), never a pending ordinary
   edge. Corridors have no ordinary identifiers or sampled configuration. *)
Definition layout_canonical_success_def:
  layout_canonical_success D lo vs0 C C' q0 es qs ass qend m invoke a s t <=>
    ?b. layout_phase_origin b = layout_phase_origin a /\
      s.vs_halted = t.vs_halted /\
      (case b of
        INL k => layout_driver_indexed es ass k /\ k.lop_cursor = SUC m /\
          k.lop_pending = ~invoke /\
          layout_aligned_entry D lo vs0 C C' q0 es qs qend k
            (if invoke then s with vs_inst_idx := SUC s.vs_inst_idx else s)
            (if invoke then t with vs_inst_idx := SUC t.vs_inst_idx else t)
      | INR k => ~invoke /\ k.ltp_pending /\ layout_corridor_entry C k s t)
End

Definition layout_canonical_OS_def:
  layout_canonical_OS D lo vs0 C C' q0 es qs ass qend q n qe m i s j t r r' <=>
    (i.inst_opcode <> INVOKE ==> qe = q /\ m = n) /\
    (case (r,r') of
      (OK p,OK p') =>
        !a. layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend q n i s j t a ==>
          if is_terminator i.inst_opcode then
            (?g. a = INL g /\
              layout_completed_jump D lo vs0 C C' q0 es qs qend g i j s t p p' /\
              control_agree p p')
          else layout_canonical_success D lo vs0 C C' q0 es qs ass qend m
            (i.inst_opcode = INVOKE) a p p'
    | _ => layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe m r r')
End

(* Block OK is completed, not pending. The exact input origin is preserved
   for every compatible witness, as in OS. *)
Definition layout_canonical_OB_def:
  layout_canonical_OB D lo vs0 C C' q0 es qs ass qend q n qe m bb s bb' t r r' <=>
    case (r,r') of
      (OK p,OK p') => !a.
        layout_canonical_block_witness D lo vs0 C C' q0 es qs ass qend q n bb s bb' t a ==>
        ?g b i j u v. a = INL g /\ layout_driver_indexed es ass b /\
          b.lop_config = qe /\ b.lop_cursor = m /\
          b.lop_origin = g.lop_origin /\
          layout_completed_jump D lo vs0 C C' q0 es qs qend b i j u v p p' /\
          control_agree p p'
    | _ => layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe m r r'
End

Definition layout_canonical_OutR_def:
  layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend q n qe m fn s fn' t r r' <=>
    layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe m r r'
End

Theorem layout_canonical_run_forget:
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t ==>
  layout_scoped_run D lo vs0 C C' q0 es qs qend g fn fn' s t
Proof
  simp[layout_canonical_run_def, layout_canonical_ready_def,
    layout_scoped_run_def] >> metis_tac[]
QED

Theorem layout_canonical_entry_forget:
  layout_canonical_entry D lo vs0 C C' q0 es qs ass qend q n a s t ==>
  layout_scoped_entry D lo vs0 C C' q0 es qs qend a s t
Proof
  Cases_on `a` >> simp[layout_canonical_entry_def, layout_scoped_entry_def,
    layout_aligned_entry_def]
QED

Theorem layout_canonical_run_intro:
  enters_block fn s p /\ enters_block fn' t p' /\
  ~a.lop_pending /\ a.lop_config = q /\ a.lop_cursor = n /\
  layout_driver_indexed es ass a /\
  layout_ordinary_trace vs0 C q0 es qs qend a p /\
  layout_ordinary_state D lo C' q0 es qs a p p' /\ control_agree p p' ==>
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t
Proof
  simp[layout_canonical_run_def, layout_canonical_ready_def] >> metis_tac[]
QED

Theorem layout_canonical_run_initial:
  enters_block fn s p /\ EVERY bb_well_formed fn.fn_blocks /\
  joint_trace vs0 C q0 es qs qend /\
  q0 = JointConfig [] [] FEMPTY entry_taint fn inst p [] FEMPTY hs h /\
  p.vs_allocas = FEMPTY /\ EL 0 ass = [([],FEMPTY)] ==>
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q0 0 fn s
    (concretize_function_with_positions positions fn) s
Proof
  strip_tac >> drule_all layout_canonical_initial_enters_entry >>
  disch_then (qspecl_then [`positions`, `lo`] mp_tac) >>
  disch_then (qspecl_then [`ARB`, `D`, `C'`] strip_assume_tac) >>
  simp[layout_canonical_run_def, layout_canonical_ready_def] >>
  qexistsl [`b`, `p`, `p`] >>
  gvs[layout_ordinary_entry_def, layout_scoped_phi_link_def,
      layout_phase_pending_def, control_agree_def, layout_driver_indexed_def]
QED

Theorem layout_canonical_run_phi:
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t ==>
  ?bb bb' phi phi' b.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis s bb.bb_instructions = OK phi /\
    eval_phis t bb'.bb_instructions = OK phi' /\
    layout_canonical_entry D lo vs0 C C' q0 es qs ass qend q n (INL b)
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    layout_scoped_phi_link g (INL b) fn fn' s t bb bb' phi phi'
Proof
  simp[layout_canonical_run_def, layout_canonical_ready_def,
    layout_driver_indexed_def] >> strip_tac >>
  drule_all layout_canonical_enters_entry >>
  disch_then (qspec_then `g` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  gvs[layout_canonical_entry_def, layout_canonical_ready_def,
      layout_aligned_entry_def, layout_ordinary_entry_def,
      layout_phase_canonical_def, layout_ordinary_trace_def, layout_driver_indexed_def]
QED

Theorem layout_canonical_ret_intro:
  b.lop_config = qe /\ b.lop_cursor = m /\ layout_driver_indexed es ass b /\
  layout_ret_endpoint D lo vs0 C C' q0 es qs qend b s t ret ret' ==>
  layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe m
    (IntRet ret s) (IntRet ret' t)
Proof
  simp[layout_canonical_result_def, layout_canonical_ret_def] >> metis_tac[]
QED

val _ = export_theory();
