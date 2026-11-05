Theory makeSsaCurrentPathNonclobber
Ancestors makeSsaCurrentDynamicStores makeSsaCurrentLastSite list rich_list
  venomWf venomExecSemantics venomInst venomExecProps makeSsaCurrentDefs livenessDefs

Definition current_source_tail_def:
  (current_source_tail [] n ms = ms) /\
  (current_source_tail (j::js) n ms =
    current_source_tail js (SUC n) (current_origin_write ms n j.inst_outputs))
End

Definition current_source_block_def:
  current_source_block fn p l n ms q out <=>
    ?bb. lookup_block l fn.fn_blocks = SOME bb /\
      q = n + LENGTH (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions) /\
      out = current_source_tail
        (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions) n
        (current_origin_batch ms p (collect_phis bb.bb_instructions))
End

Inductive current_source_segment:
  (!fn p n ms. current_source_segment fn p [] n ms n ms) /\
  (!fn p l ls n ms q mid r out.
    fn_cfg_edge fn p l /\ current_source_block fn p l n ms q mid /\
    current_source_segment fn l ls q mid r out ==>
    current_source_segment fn p (l::ls) n ms r out)
End

Theorem current_origin_snapshot_absent:
  !bs. EVERY (\b. FST b <> v) bs ==>
    current_origin_snapshot ms bs v = ms v
Proof
  Induct >- simp[current_origin_snapshot_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_origin_snapshot_def] >> metis_tac[]
QED

Theorem current_origin_write_absent:
  !outputs k. ~MEM v outputs ==>
    current_origin_snapshot ms (current_occurrence_bindings n k outputs) v = ms v
Proof
  Induct >> simp[current_occurrence_bindings_def, current_origin_snapshot_def]
QED

Theorem current_source_tail_absent:
  !js n ms. EVERY (\j. ~MEM v j.inst_outputs) js ==>
    current_source_tail js n ms v = ms v
Proof
  Induct >> simp[current_source_tail_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[current_origin_write_def, current_origin_write_absent]
QED

Theorem current_origin_batch_absent:
  !phis. EVERY (\j. HD j.inst_outputs <> v) phis ==>
    current_origin_batch ms p phis v = ms v
Proof
  rpt strip_tac >> simp[current_origin_batch_def] >>
  irule current_origin_snapshot_absent >>
  gvs[current_origin_phi_bindings_def, EVERY_MAP, combinTheory.o_DEF, EVERY_MEM,
      MEM_MAP] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Local list interface validates that HD is only used on nonempty PHIs. *)
Theorem current_source_phis_absent:
  !js. EVERY inst_wf js /\ EVERY (\j. ~MEM v j.inst_outputs) js ==>
    EVERY (\j. HD j.inst_outputs <> v) (collect_phis js)
Proof
  Induct >> simp[collect_phis_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >>
  `LENGTH h.inst_outputs = 1` by gvs[inst_wf_def] >>
  Cases_on `h.inst_outputs` >> gvs[]
QED

Theorem current_source_block_nonclobber:
  fn_inst_wf fn /\ ~current_changing_site fn ins v l /\
  current_source_block fn p l n ms q out ==> out v = ms v
Proof
  rw[current_source_block_def] >>
  `EVERY (\j. ~MEM v j.inst_outputs) bb.bb_instructions` by
    (simp[EVERY_MEM] >> metis_tac[current_changing_site_def,
       lookup_block_MEM, lookup_block_label]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  `EVERY (\j. ~MEM v j.inst_outputs)
     (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)` by
    metis_tac[EVERY_DROP] >>
  simp[current_source_tail_absent] >>
  irule current_origin_batch_absent >> metis_tac[current_source_phis_absent]
QED

Theorem current_source_segment_nonclobber:
  !fn p ls n ms q out. current_source_segment fn p ls n ms q out ==>
    fn_inst_wf fn /\ EVERY (\l. ~current_changing_site fn ins v l) ls ==>
    out v = ms v
Proof
  ho_match_mp_tac current_source_segment_ind >> simp[] >>
  rpt strip_tac >> metis_tac[current_source_block_nonclobber]
QED
