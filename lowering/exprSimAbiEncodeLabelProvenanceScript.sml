(* Generated-label intervals do not require freshness of the initial state. *)
Theory exprSimAbiEncodeLabelProvenance
Ancestors
  fragExec compileEnv emitHelperProps list rich_list arithmetic pred_set

Definition enc_label_between_def:
  enc_label_between lo hi l <=>
    ?s k. MEM s ["enc_dyn_hdr"; "enc_dyn_body"; "enc_dyn_exit"] /\
      lo <= k /\ k < hi /\ l = fresh_label_output s k
End

Definition enc_label_span_def:
  enc_label_span sa sb <=>
    sa.cs_next_label <= sb.cs_next_label /\
    (?bs. sb.cs_blocks = bs ++ sa.cs_blocks) /\
    (!b. MEM b (emitted_blocks sa sb) ==>
      b.bb_label = sa.cs_current_bb \/
      enc_label_between sa.cs_next_label sb.cs_next_label b.bb_label) /\
    (sb.cs_current_bb = sa.cs_current_bb \/
      enc_label_between sa.cs_next_label sb.cs_next_label sb.cs_current_bb)
End

Theorem enc_label_between_mono:
  lo' <= lo /\ hi <= hi' /\ enc_label_between lo hi l ==>
    enc_label_between lo' hi' l
Proof
  simp[enc_label_between_def] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem enc_label_between_split:
  lo <= mid /\ mid <= hi ==>
  (enc_label_between lo hi l <=>
    enc_label_between lo mid l \/ enc_label_between mid hi l)
Proof
  simp[enc_label_between_def] >> rpt strip_tac >> eq_tac
  >- (strip_tac >> Cases_on `k < mid` >> metis_tac[NOT_LESS]) >>
  strip_tac >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem enc_label_between_older:
  enc_label_between lo hi l /\ k < lo ==> l <> fresh_label_output s k
Proof
  simp[enc_label_between_def] >> rpt strip_tac >> gvs[] >>
  drule fresh_label_output_inj >> strip_tac >> gvs[]
QED

Theorem enc_label_span_refl:
  enc_label_span sa sa
Proof
  simp[enc_label_span_def, emitted_blocks_def]
QED

Theorem enc_label_span_trans:
  enc_label_span sa sm /\ enc_label_span sm sb ==> enc_label_span sa sb
Proof
  simp[enc_label_span_def] >> strip_tac >>
  `emitted_blocks sa sm = bs /\ emitted_blocks sm sb = bs' /\
   emitted_blocks sa sb = bs' ++ bs` by
    (rpt conj_tac >> irule emitted_blocks_append >> simp[APPEND_ASSOC]) >>
  `?new. sb.cs_blocks = new ++ sa.cs_blocks` by
    (qexists_tac `bs' ++ bs` >> simp[APPEND_ASSOC]) >>
  simp[] >> metis_tac[enc_label_between_mono, LESS_EQ_REFL, LESS_EQ_TRANS]
QED

Theorem enc_label_span_older:
  enc_label_span sa sb /\ k < sa.cs_next_label /\
  sa.cs_current_bb <> fresh_label_output s k ==>
  sb.cs_current_bb <> fresh_label_output s k /\
  (!b. MEM b (emitted_blocks sa sb) ==> b.bb_label <> fresh_label_output s k)
Proof
  simp[enc_label_span_def] >> metis_tac[enc_label_between_older]
QED
