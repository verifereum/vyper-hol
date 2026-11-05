(* Label-only compilation interfaces, independent of opcode/environment shape. *)
Theory entryLabelPreservation
Ancestors
  loweringShapeDefs loweringShapeProps compileEnv fragExec abiDecoderAppend
  abiEncoder emitHelper emitHelperProps list

Theorem added_labels_compose:
  cs_extends a b /\ cs_extends b c ==>
  added_labels a c = added_labels a b ++ added_labels b c
Proof
  strip_tac >>
  `cs_extends a c` by metis_tac[cs_extends_trans] >>
  imp_res_tac block_labels_cs_extends >> gvs[]
QED

Theorem label_extends_trans:
  cs_extends a b /\ EVERY LP (added_labels a b) /\
  cs_extends b c /\ EVERY LP (added_labels b c) ==>
  cs_extends a c /\ EVERY LP (added_labels a c)
Proof
  metis_tac[added_labels_compose, EVERY_APPEND, cs_extends_trans]
QED

Theorem added_labels_new_block:
  new_block lbl st = (old, st') ==> added_labels st st' = [lbl]
Proof
  strip_tac >> gvs[new_block_def] >>
  simp[added_labels_def, all_blocks_def, MAP_APPEND, DROP_APPEND,
       LENGTH_MAP]
QED

Theorem added_labels_emit_inst:
  emit_inst opc ops outs st = (r, st') ==> added_labels st st' = []
Proof
  strip_tac >>
  gvs[emit_inst_def, fresh_id_def, comp_bind_def, comp_return_def,
      emit_def] >>
  simp[added_labels_def, all_blocks_def, LENGTH_MAP]
QED


Theorem label_preserving_bind_result:
  !R. (!s r t. f s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t) /\ R r) /\
  (!r. R r ==> !s v t. g r s = (v,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)) ==>
  !s v t. comp_bind f g s = (v,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `f s` >> simp[comp_bind_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  metis_tac[label_extends_trans]
QED

Theorem label_preserving_bind:
  (!s r t. f s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)) /\
  (!r s v t. g r s = (v,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)) ==>
  !s v t. comp_bind f g s = (v,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.SPEC `\r. T` label_preserving_bind_result) >> simp[] >> metis_tac[]
QED

Theorem label_preserving_ignore_bind:
  (!s r t. f s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)) /\
  (!s v t. g s = (v,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)) ==>
  !s v t. comp_ignore_bind f g s = (v,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  ho_match_mp_tac label_preserving_bind >> simp[] >> metis_tac[]
QED

Theorem label_preserving_return:
  !s r t. comp_return x s = (r,t) ==>
    cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  simp[comp_return_def] >> rpt strip_tac >> gvs[] >>
  simp[cs_extends_refl, added_labels_def, all_blocks_def, LENGTH_MAP,
       DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem label_preserving_fresh_label:
  fresh_label suffix s = (lbl,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t) /\
  jump_label_ok lbl /\ added_labels s t = []
Proof
  strip_tac >>
  `cs_extends s t` by metis_tac[cs_extends_fresh_label] >>
  gvs[fresh_label_def] >>
  simp[added_labels_def, all_blocks_def, LENGTH_MAP, DROP_APPEND,
       DROP_LENGTH_TOO_LONG, jump_label_ok_def, compiler_label_def,
       fresh_label_output_in_future]
QED

Theorem label_preserving_new_block:
  LP lbl ==> !s r t. new_block lbl s = (r,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  metis_tac[added_labels_new_block, cs_extends_new_block, EVERY_DEF]
QED

Theorem label_preserving_emit_inst:
  !s r t. emit_inst opc ops outs s = (r,t) ==>
  cs_extends s t /\ EVERY LP (added_labels s t)
Proof
  rpt strip_tac >> drule added_labels_emit_inst >> strip_tac >>
  simp[] >> metis_tac[cs_extends_emit_inst]
QED

Theorem label_preserving_fresh_block[local]:
  !s r t. comp_bind (fresh_label suffix) new_block s = (r,t) ==>
  cs_extends s t /\ EVERY jump_label_ok (added_labels s t)
Proof
  ho_match_mp_tac (Q.ISPEC `jump_label_ok` label_preserving_bind_result) >> conj_tac
  >- metis_tac[label_preserving_fresh_label] >>
  metis_tac[label_preserving_new_block]
QED
