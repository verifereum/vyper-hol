(* Code occurrence in the context installed by raw runtime lowering. *)
Theory rawEntryCode
Ancestors
  vyperCompiler actualDecoderPackaging fragExec compileEnv venomWf
  venomExecSemantics venomInst list loweringShapeDefs rich_list

Theorem run_lowering_member_labels:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info entry_label = SOME unit /\
  MEM fn unit.cu_context.ctx_functions ==>
  ALL_DISTINCT (fn_labels fn)
Proof
  strip_tac >> drule run_lowering_context_ok >>
  disch_then (mp_tac o MATCH_MP lowering_context_ok_bridge) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem run_lowering_entry_interval:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info entry_label = SOME unit /\
  MEM (mk_raw_function "__entry" (all_blocks entry_end)) unit.cu_context.ctx_functions /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  cs_extends first decoder_start /\ cs_extends decoder_start decoder_end /\
  cs_extends decoder_end entry_end ==>
  efn = mk_raw_function "__entry" (all_blocks entry_end) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end)) /\
  fn_has_code decoder_start decoder_end efn
Proof
  strip_tac >>
  drule run_lowering_integrity >> strip_tac >>
  drule lookup_function_MEM >> strip_tac >>
  drule lookup_function_result_name >> strip_tac >>
  `efn = mk_raw_function "__entry" (all_blocks entry_end)` by
    (irule distinct_function_names_unique >>
     gvs[ctx_distinct_fn_names_def, ctx_fn_names_def, mk_raw_function_def] >>
     metis_tac[]) >>
  gvs[] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end))` by
    (drule_all run_lowering_member_labels >>
     simp[fn_labels_def, mk_raw_function_def]) >>
  simp[] >> irule external_decoder_fn_has_code >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `first` >> simp[]
QED

(* Extension preserves the chronological entry block. *)
Theorem cs_extends_raw_entry_label:
  cs_extends first last /\ first.cs_blocks = [] ==>
  fn_entry_label (mk_raw_function fname (all_blocks last)) =
    SOME first.cs_current_bb
Proof
  rw[cs_extends_def] >>
  Cases_on `new = []` >>
  gvs[all_blocks_def, fn_entry_label_def, entry_block_def, mk_raw_function_def,
    HD_REVERSE] >>
  `REVERSE last.cs_blocks <> []` by simp[] >>
  Cases_on `REVERSE last.cs_blocks` >> gvs[] >>
  metis_tac[HD_REVERSE, HD]
QED
