Theory loadElimSentinelHelpers
Ancestors
  list rich_list finite_map pred_set arithmetic words venomState venomInst
  venomMemDefs memLocDefs basePtrDefs dfgCorrectnessProof
  memoryCopyElisionSound callLayoutDefs unitShapeDefs

(* Sentinel insertion never changes variables or any old allocation lookup.
   BP soundness therefore needs no freshness relative to BP pointer lists.
   Boundedness DOES need access-support freshness: its absent-allocation
   branch is vacuous, unlike ptr_matches_var. *)
Definition le_sentinel_def:
  le_sentinel s j B =
    s with <| vs_allocas := s.vs_allocas |+ (j,(B,1));
              vs_alloca_next := B; vs_inst_idx := 0 |>
End

Theorem le_sentinel_old_lookup:
  FLOOKUP s.vs_allocas j = NONE /\
  FLOOKUP s.vs_allocas a = SOME p ==>
  FLOOKUP (le_sentinel s j B).vs_allocas a = SOME p
Proof
  simp[le_sentinel_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `a = j` >> gvs[]
QED

Theorem le_sentinel_dfg:
  dfg_assigns_sound dfg s ==> dfg_assigns_sound dfg (le_sentinel s j B)
Proof
  `!op. eval_operand op (le_sentinel s j B) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, le_sentinel_def, lookup_var_def]) >>
  simp[dfg_assigns_sound_def, le_sentinel_def, lookup_var_def]
QED

Theorem le_sentinel_ptr_matches:
  FLOOKUP s.vs_allocas j = NONE /\ ptr_matches_var p v s ==>
  ptr_matches_var p v (le_sentinel s j B)
Proof
  Cases_on `p` >> rename1 `Ptr alloc off` >> Cases_on `alloc` >>
  Cases_on `off` >>
  simp[ptr_matches_var_def, le_sentinel_def, lookup_var_def,
       FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `j = n` >> gvs[] >> metis_tac[]
QED

Theorem le_sentinel_lookup[simp]:
  lookup_var v (le_sentinel s j B) = lookup_var v s
Proof
  simp[le_sentinel_def, lookup_var_def]
QED

Theorem le_sentinel_bp_sound:
  FLOOKUP s.vs_allocas j = NONE /\ bp_ptr_sound bp s ==>
  bp_ptr_sound bp (le_sentinel s j B)
Proof
  simp[bp_ptr_sound_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >>
  disch_then (qx_choose_then `p` strip_assume_tac) >>
  qexists_tac `p` >> simp[] >>
  irule le_sentinel_ptr_matches >> simp[]
QED

Theorem le_sentinel_nonoverlap:
  FLOOKUP s.vs_allocas j = NONE /\ allocas_non_overlapping s /\
  (!a b n. FLOOKUP s.vs_allocas a = SOME (b,n) ==> b+n <= B) ==>
  allocas_non_overlapping (le_sentinel s j B)
Proof
  simp[allocas_non_overlapping_def, le_sentinel_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `a1 = j` >> Cases_on `a2 = j` >>
  gvs[] >> metis_tac[]
QED

Theorem le_sentinel_in_word:
  allocas_in_word s /\ B+1 < dimword(:256) ==>
  allocas_in_word (le_sentinel s j B)
Proof
  simp[allocas_in_word_def, le_sentinel_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `aid = j` >> gvs[] >> metis_tac[]
QED

Theorem le_sentinel_memloc:
  ml.ml_alloca <> SOME (Allocation j) ==>
  (memloc_within_alloca ml (le_sentinel s j B) <=>
   memloc_within_alloca ml s)
Proof
  Cases_on `ml.ml_offset` >> Cases_on `ml.ml_size` >>
  Cases_on `ml.ml_alloca` >> simp[memloc_within_alloca_def] >>
  rename1 `SOME alloc` >> Cases_on `alloc` >>
  simp[memloc_within_alloca_def, le_sentinel_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_sentinel_bp_bounded:
  bp_ptrs_bounded bp fn s /\
  (!bb inst ops. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) ==>
     (bp_segment_from_ops bp ops).ml_alloca <> SOME (Allocation j)) ==>
  bp_ptrs_bounded bp fn (le_sentinel s j B)
Proof
  rw[bp_ptrs_bounded_def] >>
  `(bp_segment_from_ops bp ops).ml_alloca <> SOME (Allocation j)` by
    metis_tac[] >>
  simp[le_sentinel_memloc] >> metis_tac[]
QED

(* Finite access support, including unresolved offsets. *)
Definition le_access_ids_def:
  le_access_ids bp fn =
    MAP (\ops. case (bp_segment_from_ops bp ops).ml_alloca of
                 NONE => 0 | SOME (Allocation a) => a)
      (FLAT (MAP (\inst. OPTION_TO_LIST (mem_write_ops inst) ++
                         OPTION_TO_LIST (mem_read_ops inst)) (fn_insts fn)))
End

Theorem le_access_ids_covers:
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
  (bp_segment_from_ops bp ops).ml_alloca = SOME (Allocation j) ==>
  MEM j (le_access_ids bp fn)
Proof
  rpt strip_tac >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `MEM ops (OPTION_TO_LIST (mem_write_ops inst) ++
            OPTION_TO_LIST (mem_read_ops inst))` by
    (gvs[OPTION_TO_LIST_def]) >>
  simp[le_access_ids_def, MEM_MAP] >> qexists_tac `ops` >> simp[] >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem le_sentinel_fresh_id:
  !s bp fn aid.
    ?j. j <> aid /\ FLOOKUP s.vs_allocas j = NONE /\
        ~MEM j (le_access_ids bp fn)
Proof
  rpt gen_tac >>
  `?j:num. j IN UNIV /\
     j NOTIN (aid INSERT (FDOM s.vs_allocas UNION
                         set (le_access_ids bp fn)))` by
    (irule IN_INFINITE_NOT_FINITE >> simp[INFINITE_UNIV] >>
     qexists_tac `SUC` >> simp[] >> qexists_tac `0` >> simp[]) >>
  gvs[FLOOKUP_DEF] >> metis_tac[]
QED

(* The strict endpoint bound really costs one byte of headroom.  The
   original allocas_in_word alone permits an old endpoint at dimword-1.
   Keep the frontier B and its extra headroom explicit for consumers. *)
Theorem le_sentinel_extension:
  dfg_assigns_sound dfg s /\ bp_ptr_sound bp s /\
  allocas_non_overlapping s /\ allocas_in_word s /\
  bp_ptrs_bounded bp fn s /\
  B+1 < dimword(:256) /\
  (!a b n. FLOOKUP s.vs_allocas a = SOME (b,n) ==> b+n <= B) ==>
  ?j t. j <> aid /\ FLOOKUP s.vs_allocas j = NONE /\
    t = le_sentinel s j B /\
    t.vs_vars = s.vs_vars /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas |+ (j,(B,1)) /\
    t.vs_alloca_next = B /\ t.vs_inst_idx = 0 /\
    dfg_assigns_sound dfg t /\ bp_ptr_sound bp t /\
    allocas_non_overlapping t /\ allocas_in_word t /\
    bp_ptrs_bounded bp fn t
Proof
  strip_tac >>
  qspecl_then [`s`, `bp`, `fn`, `aid`]
    (qx_choose_then `j` strip_assume_tac) le_sentinel_fresh_id >>
  `bp_ptrs_bounded bp fn (le_sentinel s j B)` by
    (irule le_sentinel_bp_bounded >> simp[] >>
     metis_tac[le_access_ids_covers]) >>
  `allocas_non_overlapping (le_sentinel s j B)` by
    (irule le_sentinel_nonoverlap >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`j`, `le_sentinel s j B`] >>
  simp[le_sentinel_dfg, le_sentinel_bp_sound, le_sentinel_in_word] >>
  simp[le_sentinel_def]
QED
