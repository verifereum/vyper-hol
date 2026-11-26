(* A borrowed nonword operand retains its entire footprint, including any
   dynamic-array length word, when the source scopes do not change. *)
Theory bodyExtBorrowedFootprintMods
Ancestors
  bodyPtrDefs loweringPosts valueEncodingProps

Theorem ext_borrowed_footprint_frame:
  ee.scopes = es.scopes /\ wb_frame ce es ee st s t /\
  ghost_kept_at lo ce es st G tn s G' tn' /\
  sb.cs_next_id <= st.cs_next_id /\
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
       i IN tn'.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (conj_tac
      >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
            (fs[wb_frame_def] >> first_x_assum irule >>
             conj_tac >- metis_tac[] >> qexists `aid` >> simp[] >> decide_tac) >>
          `w2n w = b + (w2n w - b)` by decide_tac >>
          `w2n w - b + val_footprint tv v <= sz` by decide_tac >>
          drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
          disch_then (qspecl_then [`w2n w - b`, `val_footprint tv v`] mp_tac) >>
          simp[]) >>
      rpt strip_tac >> fs[ghost_kept_at_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      conj_tac >- (qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
        gvs[] >> decide_tac) >>
      simp[])
  >- (conj_tac
      >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
            (fs[wb_frame_def, locals_kept_def] >>
             qpat_assum `!n b sz. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
             qexists `n` >> simp[]) >>
          `w2n w = b + (w2n w - b)` by decide_tac >>
          `w2n w - b + val_footprint tv v <= sz` by decide_tac >>
          drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
          disch_then (qspecl_then [`w2n w - b`, `val_footprint tv v`] mp_tac) >>
          simp[]) >>
      rpt strip_tac >> fs[ghost_kept_at_def] >>
      qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
      conj_tac >- simp[] >>
      qexistsl_tac [`b`, `n`, `sz`] >> simp[] >> decide_tac)
  >> simp[valueEncodingDefsTheory.mem_bytes_at_def] >> rpt strip_tac >> decide_tac
QED
