Theory makeSsaCurrentInstructionSingleton
Ancestors makeSsaCurrentValueInvariant makeSsaCurrentTokens makeSsaCurrentSimDefs
  makeSsaCurrentCertificate makeSsaCurrentAllocation venomInst venomState list rich_list finite_map

(* Indices distinguish even equal instruction records or equal block records. *)
Definition current_instruction_sites_def:
  current_instruction_sites fn = FLAT (GENLIST (\b.
    MAP (\i. (b,i)) (GENLIST I (LENGTH (EL b fn.fn_blocks).bb_instructions)))
    (LENGTH fn.fn_blocks))
End

Definition current_defining_sites_def:
  current_defining_sites fn v = FILTER (\bi.
    MEM v (EL (SND bi) (EL (FST bi) fn.fn_blocks).bb_instructions).inst_outputs)
    (current_instruction_sites fn)
End

Definition current_canonical_instruction_token_def:
  current_canonical_instruction_token fn v bi =
    current_output_token v (EL (FST bi) fn.fn_blocks).bb_label (SND bi) 0
      (EL (SND bi) (EL (FST bi) fn.fn_blocks).bb_instructions).inst_outputs
      (CurrentDefault v)
End

(* The enumeration may repeat a table pair for repeated source slots. This
   does not affect its pointwise membership-based agreement semantics. *)
Definition current_instruction_singleton_table_def:
  current_instruction_singleton_table fn H = FLAT (MAP (\v.
    case current_defining_sites fn v of
      [bi] => (case current_token_name H (current_canonical_instruction_token fn v bi) of
                 NONE => [] | SOME n => [(v,n)])
    | _ => []) (MAP SND (current_original_table fn)))
End

Theorem current_output_token_last_slot:
  !outs a k t. k < LENGTH outs /\ EL k outs = v /\
    (!r. k < r /\ r < LENGTH outs ==> EL r outs <> v) ==>
    current_output_token v l i a outs t = CurrentOriginal l i (a+k)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `k` >> simp[] >> strip_tac
  >- (gvs[] >>
      `~MEM h outs` by
        (simp[MEM_EL] >> rpt strip_tac >>
         qpat_x_assum `!r. _ ==> _` (qspec_then `SUC n` mp_tac) >> simp[]) >>
      simp[current_output_token_def, current_output_token_absent]) >>
  simp[current_output_token_def, arithmeticTheory.ADD_CLAUSES] >>
  qpat_x_assum `!a k t. _` (qspecl_then
    [`SUC a`, `n`, `if h = v then CurrentOriginal l i a else t`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >> disch_then irule >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC r` mp_tac) >> simp[]
QED

Theorem current_singleton_entry_member[local]:
  MEM (v,n) (case current_defining_sites fn w of
    [bi] => (case current_token_name H (current_canonical_instruction_token fn w bi) of
      NONE => [] | SOME name => [(w,name)]) | _ => []) <=>
  v = w /\ ?bi. current_defining_sites fn w = [bi] /\
    current_token_name H (current_canonical_instruction_token fn w bi) = SOME n
Proof
  Cases_on `current_defining_sites fn w` >> simp[] >>
  Cases_on `t` >> simp[] >> CASE_TAC >> simp[] >> metis_tac[]
QED

Theorem current_instruction_singleton_member:
  MEM (v,n) (current_instruction_singleton_table fn H) <=>
  MEM v (MAP SND (current_original_table fn)) /\
  ?bi. current_defining_sites fn v = [bi] /\
    current_token_name H (current_canonical_instruction_token fn v bi) = SOME n
Proof
  simp[current_instruction_singleton_table_def, MEM_FLAT, MEM_MAP,
    PULL_EXISTS, current_singleton_entry_member] >> metis_tac[]
QED

Theorem current_instruction_singleton_exclude:
  ~(?bi. current_defining_sites fn v = [bi]) ==>
  ~MEM (v,n) (current_instruction_singleton_table fn H)
Proof
  simp[current_instruction_singleton_member]
QED

Theorem current_instruction_singleton_slots_coverage:
  current_token_name H (CurrentOriginal "E" 0 1) = SOME n ==>
  MEM ("x",n) (current_instruction_singleton_table current_singleton_slots_probe_fn H)
Proof
  simp[current_instruction_singleton_member, current_original_table_def,
    current_singleton_slots_probe_fn_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def, current_original_annotations_def,
    current_original_outputs_def, current_defining_sites_def,
    current_instruction_sites_def, current_canonical_instruction_token_def,
    current_output_token_def]
QED

(* Earlier writes, including duplicate source destinations, are unrestricted.
   Only the suffix after the final effective paired write must avoid the keys. *)
Theorem current_indexed_fold_avoids:
  !events m. EVERY (\kv. EL (FST kv) outs <> v) events ==>
    FLOOKUP (FOLDL (\m kv. m |+ (EL (FST kv) outs,SND kv)) m events) v =
    FLOOKUP m v
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[FLOOKUP_UPDATE]
QED

Theorem current_indexed_fold_last_pair:
  EL j outs = v /\ EL j outs' = n /\
  EVERY (\kv. EL (FST kv) outs <> v /\ EL (FST kv) outs' <> n) post ==>
  FLOOKUP (FOLDL (\m kv. m |+ (EL (FST kv) outs,SND kv)) m
    (pre ++ (j,value)::post)) v =
  FLOOKUP (FOLDL (\m kv. m |+ (EL (FST kv) outs',SND kv)) m'
    (pre ++ (j,value)::post)) n
Proof
  strip_tac >> simp[FOLDL_APPEND] >>
  `EVERY (\kv. EL (FST kv) outs <> v) post /\
   EVERY (\kv. EL (FST kv) outs' <> n) post` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[current_indexed_fold_avoids, FLOOKUP_UPDATE]
QED

Theorem current_repeated_destination_values:
  !m m'.
  FLOOKUP (FOLDL (\m kv. m |+ (EL (FST kv) ["x";"x"],SND kv)) m
    [(0,3w:256 word);(1,4w)]) "x" = SOME 4w /\
  FLOOKUP (FOLDL (\m kv. m |+ (EL (FST kv) ["early";"canonical"],SND kv)) m'
    [(0,3w:256 word);(1,4w)]) "canonical" = SOME 4w /\
  FLOOKUP (FOLDL (\m kv. m |+ (EL (FST kv) ["early";"canonical"],SND kv)) m'
    [(0,3w:256 word);(1,4w)]) "early" = SOME 3w
Proof
  simp[FLOOKUP_UPDATE]
QED
