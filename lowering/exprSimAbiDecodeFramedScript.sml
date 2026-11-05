Theory exprSimAbiDecodeFramed
Ancestors
  exprSimAbiDecodeResourcePrims exprSimAbiDecodeResource compileEnv pred_set

Definition decode_framed_def:
  decode_framed ex m post <=>
    !s P. P SUBSET decode_label_range 0 s.cs_next_label ==>
      ?x t Q. decode_resource_run ex P m s x t Q /\ P SUBSET Q /\ post x
End

Theorem decode_straight_framed:
  decode_straight ex m post ==> decode_framed ex m post
Proof
  rw[decode_straight_def, decode_framed_def] >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`x`, `t`, `P`] >> simp[]
QED

Theorem decode_framed_return:
  post x ==> decode_framed ex (comp_return x) post
Proof
  strip_tac >> irule decode_straight_framed >>
  irule decode_straight_return >> simp[]
QED

Theorem decode_framed_bind:
  decode_framed ex m mid /\
  (!x. mid x ==> decode_framed ex (f x) post) ==>
  decode_framed ex (comp_bind m f) post
Proof
  rw[decode_framed_def] >>
  first_x_assum drule >> strip_tac >>
  `Q SUBSET decode_label_range 0 t.cs_next_label` by
    (drule decode_resource_run_pool >> simp[]) >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qexistsl_tac [`x'`, `t'`, `Q'`] >> simp[] >>
  conj_tac
  >- (irule decode_resource_run_bind >> metis_tac[]) >>
  metis_tac[SUBSET_TRANS]
QED

Theorem decode_framed_ignore_bind:
  decode_framed ex m mid /\ decode_framed ex n post ==>
  decode_framed ex (comp_ignore_bind m n) post
Proof
  rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  match_mp_tac (GEN_ALL decode_framed_bind) >> qexists_tac `mid` >> simp[]
QED

Theorem decode_framed_run:
  decode_framed ex m post /\ m s = (x,t) /\
  P SUBSET decode_label_range 0 s.cs_next_label ==>
  ?Q. decode_resource_run ex P m s x t Q /\ P SUBSET Q /\ post x
Proof
  rw[decode_framed_def] >> first_x_assum drule >> strip_tac >>
  `x' = x /\ t' = t` by fs[decode_resource_run_def] >> gvs[] >>
  qexists_tac `Q` >> simp[]
QED

Theorem decode_ignore_unit:
  comp_ignore_bind (comp_ignore_bind m (comp_return ())) n = comp_ignore_bind m n
Proof
  simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def,
       pairTheory.UNCURRY, pairTheory.PAIR]
QED

Theorem decode_resource_switch_exists:
  P SUBSET decode_label_range 0 s.cs_next_label /\ l IN P ==>
  ?t. decode_resource_run ex P
    (comp_ignore_bind (new_block l) (comp_return ())) s () t (P DELETE l)
Proof
  strip_tac >> irule_at Any decode_resource_switch >> simp[]
QED

Theorem decode_resource_terminator_exists:
  P SUBSET decode_label_range 0 s.cs_next_label /\ l IN P /\
  (opc = JMP \/ opc = JNZ) ==>
  ?t. decode_resource_run ex P
    (comp_ignore_bind (emit_inst opc ops [])
      (comp_ignore_bind (new_block l) (comp_return ()))) s () t (P DELETE l)
Proof
  strip_tac >> irule_at Any decode_resource_terminator_switch >> simp[]
QED

Theorem decode_resource_then_exists:
  (?u. decode_resource_run ex P m s () u R) /\
  (!u. decode_resource_run ex P m s () u R ==>
    ?x t Q. decode_resource_run ex R n u x t Q /\ post x t Q) ==>
  ?x t Q. decode_resource_run ex P (comp_ignore_bind m n) s x t Q /\ post x t Q
Proof
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [`x`, `t`, `Q`] >> simp[] >>
  irule decode_resource_run_ignore_bind >> metis_tac[]
QED

Theorem decode_resource_switch_then:
  P SUBSET decode_label_range 0 s.cs_next_label /\ l IN P /\
  (!u. decode_resource_run ex P
      (comp_ignore_bind (new_block l) (comp_return ())) s () u (P DELETE l) ==>
    ?x t Q. decode_resource_run ex (P DELETE l) n u x t Q /\ post x t Q) ==>
  ?x t Q. decode_resource_run ex P
    (comp_ignore_bind (new_block l) n) s x t Q /\ post x t Q
Proof
  strip_tac >> once_rewrite_tac[GSYM decode_ignore_unit] >>
  match_mp_tac (GEN_ALL decode_resource_then_exists) >>
  qexists_tac `P DELETE l` >> simp[] >>
  irule decode_resource_switch_exists >> simp[]
QED

Theorem decode_resource_terminator_then:
  P SUBSET decode_label_range 0 s.cs_next_label /\ l IN P /\
  (opc = JMP \/ opc = JNZ) /\
  (!u. decode_resource_run ex P
      (comp_ignore_bind (emit_inst opc ops [])
        (comp_ignore_bind (new_block l) (comp_return ()))) s () u (P DELETE l) ==>
    ?x t Q. decode_resource_run ex (P DELETE l) n u x t Q /\ post x t Q) ==>
  ?x t Q. decode_resource_run ex P
    (comp_ignore_bind (emit_inst opc ops []) (comp_ignore_bind (new_block l) n))
    s x t Q /\ post x t Q
Proof
  strip_tac >>
  `comp_ignore_bind (emit_inst opc ops []) (comp_ignore_bind (new_block l) n) =
   comp_ignore_bind (comp_ignore_bind (emit_inst opc ops [])
     (comp_ignore_bind (new_block l) (comp_return ()))) n` by
    simp[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def,
         pairTheory.UNCURRY, pairTheory.PAIR] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  match_mp_tac (GEN_ALL decode_resource_then_exists) >>
  qexists_tac `P DELETE l` >> simp[] >>
  irule decode_resource_terminator_exists >> simp[]
QED
