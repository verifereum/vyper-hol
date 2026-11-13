(* Live-successor integration for the grouped memory-write effects. *)
Theory lowerDloadSafetyWriteAdvance
Ancestors
  lowerDloadSafetyWriteAssembly lowerDloadSafetyLocations lowerDloadSafetyAdvance
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline venomInst finite_map list

Theorem ld_sync_memory_write_advance:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn /\
  ptr_discipline lo C vs0 /\ fn_shape_ok fn /\ fn_inst_wf fn /\
  s.vs_labels = t.vs_labels /\ ~in_revert_forward fn s /\
  t.vs_alloca_next < dimword(:256) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] /\
  step_inst fuel C' inst t = OK ts /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\
  active_inst (FST (lower_dload_function_supply f.lf_supply fn)) ti
    (ts with vs_inst_idx := SUC p) ==>
  ?ss next. step_inst fuel C inst s = OK ss /\
    ld_sync lo P C vs0 stk PG G (step_taint inst s ss tn) fn next
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (ts with vs_inst_idx := SUC p) A
      ((f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                 lf_tgt := ts with vs_inst_idx := SUC p;
                 lf_tv := (step_taint inst s ss tn).t_var|>)::fs) N /\
    ld_global lo A
      ((f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                 lf_tgt := ts with vs_inst_idx := SUC p;
                 lf_tv := (step_taint inst s ss tn).t_var|>)::fs)
Proof
  strip_tac >>
  drule_all ld_sync_memory_write_effect >> strip_tac >>
  `ld_envelope f.lf_supply fn ss s.vs_inst_idx [inst] p` by
    (fs[ld_envelope_def] >> qexists_tac `bi` >> simp[]) >>
  `ts.vs_current_bb = ss.vs_current_bb` by
    (`s.vs_current_bb = t.vs_current_bb` by
       (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        pure_rewrite_tac[ld_sync_def] >> simp[] >> strip_tac >> simp[]) >> simp[]) >>
  drule_all (SRULE [GSYM arithmeticTheory.ADD1] (Q.INST [`X` |-> `[inst]`] ld_envelope_expansion_next)) >>
  strip_tac >>
  `G = ld_erase A o_f f.lf_H` by
    (drule ld_sync_ghosts >> simp[]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
     simp[is_terminator_def] >> strip_tac >> gvs[is_terminator_def]) >>
  `ld_vars P A (f with
      <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
        lf_tgt := ts with vs_inst_idx := SUC p;
        lf_tv := (step_taint inst s ss tn).t_var|>)` by
    (mp_tac (ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := ts;
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC p`]) >> simp[]) >>
  qexistsl_tac [`ss`,`next`] >> conj_tac >- first_assum ACCEPT_TAC >>
  mp_tac (ld_sync_ordinary_advance |> Q.INST
    [`H'` |-> `f.lf_H`, `G'` |-> `G`,
     `tn'` |-> `step_taint inst s ss tn`,
     `f'` |-> `f with
       <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
         lf_tgt := ts with vs_inst_idx := SUC p;
         lf_tv := (step_taint inst s ss tn).t_var|>`]) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- simp[ld_frame_component_equality] >>
     conj_tac >- (qexists_tac `Y` >> first_assum ACCEPT_TAC) >>
     metis_tac[])) >> simp[]
QED
