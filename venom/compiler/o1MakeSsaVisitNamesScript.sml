Theory o1MakeSsaVisitNames
Ancestors
  o1MakeSsaVisitTrace o1MakeSsaReaching o1MakeSsaFormats o1MakeSsaFlags
  makeSsaDefs makeSsaCurrentInduct venomInst list pair makeSsaCurrentAllocation o1MakeSsaCfg

Definition last_name_def:
  (last_name x n [] = n) /\
  (last_name x n ((a,b)::rest) = last_name x (if a = x then b else n) rest)
End

Definition block_output_pairs_def:
  block_output_pairs insts outs =
    FLAT (MAP (\(i,j). ZIP (i.inst_outputs,j.inst_outputs)) (ZIP (insts,outs)))
End

Definition path_pairs_def:
  path_pairs path = FLAT (MAP (\(lbl,is,js). block_output_pairs is js) path)
End

Theorem last_name_append:
  !pre post x n. last_name x n (pre ++ post) =
    last_name x (last_name x n pre) post
Proof
  Induct >> simp[last_name_def] >> Cases_on `h` >> simp[last_name_def]
QED

Theorem outputs_last_name:
  !vs s rs rt t names x.
    rename_current_outputs s rs vs = (rt,t,names) ==>
    latest_current_name rt x =
      last_name x (latest_current_name rs x) (ZIP (vs,names))
Proof
  Induct >> simp[rename_current_outputs_def, last_name_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule rename_current_outputs_length >> strip_tac >> simp[ZIP,last_name_def] >>
  first_x_assum drule >> disch_then (qspec_then `x` mp_tac) >>
  drule current_push_latest >> disch_then (qspec_then `x` mp_tac) >>
  Cases_on `x = h` >> simp[]
QED

Theorem inst_last_name:
  rename_current_inst s rs inst = (rt,t,out) ==>
  latest_current_name rt x = last_name x (latest_current_name rs x)
    (ZIP (inst.inst_outputs,out.inst_outputs))
Proof
  simp[rename_current_inst_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule outputs_last_name >> simp[]
QED

Theorem block_last_name:
  !insts s rs rt t outs x.
    rename_current_block_insts s rs insts = (rt,t,outs) ==>
    latest_current_name rt x = last_name x (latest_current_name rs x)
      (block_output_pairs insts outs)
Proof
  Induct >> simp[rename_current_block_insts_def,block_output_pairs_def,last_name_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> drule rename_current_block_insts_length >> strip_tac >>
  simp[block_output_pairs_def,ZIP,last_name_append] >>
  first_x_assum drule >> disch_then (qspec_then `x` mp_tac) >>
  drule inst_last_name >> simp[block_output_pairs_def]
QED

Definition visit_name_ok_def:
  visit_name_ok x n e <=>
    latest_current_name e.sve_in x = last_name x n (path_pairs e.sve_path) /\
    latest_current_name e.sve_out x = last_name x n
      (path_pairs (e.sve_path ++ [(e.sve_label,e.sve_before,e.sve_after)]))
End

Theorem path_pairs_append:
  path_pairs (pre ++ post) = path_pairs pre ++ path_pairs post
Proof
  simp[path_pairs_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem visit_path_names:
  (!tree path s rs bbs sm x n.
    latest_current_name rs x = last_name x n (path_pairs path) ==>
    EVERY (visit_name_ok x n) (SND (visit_blocks path s rs bbs sm tree))) /\
  (!trees path s ctrs stacks bbs sm x n.
    latest_current_name (ctrs,stacks) x = last_name x n (path_pairs path) ==>
    EVERY (visit_name_ok x n)
      (SND (visit_children path s ctrs stacks bbs sm trees)))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      drule block_last_name >> disch_then (qspec_then `x` assume_tac) >>
      conj_tac
      >- simp[visit_name_ok_def, path_pairs_append, path_pairs_def,
              last_name_append] >>
      `latest_current_name (FST rs1,SND rs1) x =
         last_name x n (path_pairs (path ++ [(lbl,x'.bb_instructions,insts)]))` by
        simp[path_pairs_append, path_pairs_def, last_name_append] >>
      metis_tac[SND])
  >- simp[visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  `latest_current_name (ctrs1,stacks) x = last_name x n (path_pairs path)` by
    gvs[latest_current_name_def] >>
  conj_tac >> metis_tac[SND]
QED

Theorem visit_event_names:
  MEM e (SND (visit_blocks [] s rs bbs sm tree)) ==>
  latest_current_name e.sve_in x =
    last_name x (latest_current_name rs x) (path_pairs e.sve_path) /\
  latest_current_name e.sve_out x = last_name x (latest_current_name rs x)
    (path_pairs (e.sve_path ++ [(e.sve_label,e.sve_before,e.sve_after)]))
Proof
  strip_tac >>
  `EVERY (visit_name_ok x (latest_current_name rs x))
     (SND (visit_blocks [] s rs bbs sm tree))` by
    (irule (cj 1 visit_path_names) >> simp[path_pairs_def,last_name_def]) >>
  gvs[EVERY_MEM] >> first_x_assum drule >> simp[visit_name_ok_def]
QED

Theorem last_name_source:
  !ps x n. last_name x n ps = n \/
    ?pre v post. ps = pre ++ [(x,v)] ++ post /\
      EVERY (\p. FST p <> x) post /\ last_name x n ps = v
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- simp[last_name_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `x` >> rename1 `SNOC (a,b) ps` >>
  simp[SNOC_APPEND,last_name_append,last_name_def] >>
  Cases_on `a = x'`
  >- (gvs[] >> disj2_tac >> qexistsl [`ps`,`[]`] >> simp[]) >>
  first_x_assum (qspecl_then [`x'`,`n`] strip_assume_tac)
  >- simp[] >>
  disj2_tac >> qexistsl [`pre`,`post ++ [(a,b)]`] >>
  simp[APPEND_ASSOC]
QED

Theorem visit_event_last_source:
  MEM e (SND (visit_blocks [] s rs bbs sm tree)) ==>
  latest_current_name e.sve_out x = latest_current_name rs x \/
  ?pre v post.
    path_pairs (e.sve_path ++ [(e.sve_label,e.sve_before,e.sve_after)]) =
      pre ++ [(x,v)] ++ post /\
    EVERY (\p. FST p <> x) post /\ latest_current_name e.sve_out x = v
Proof
  strip_tac >> drule visit_event_names >> strip_tac >>
  qspec_then `path_pairs (e.sve_path ++ [(e.sve_label,e.sve_before,e.sve_after)])`
    (qspecl_then [`x`,`latest_current_name rs x`] mp_tac) last_name_source >>
  simp[]
QED
