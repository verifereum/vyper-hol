(* Probe the source address ADD plus external load with arbitrary provenance.
   Retaining the real intermediate ghost avoids a false scalar-only interface. *)
Theory bodyPtrMakeArrayStorageProbe
Ancestors
  bodyPtrMakeArrayStorageBody bodyPtrMakeArrayAdd typedCopyPtr
  ptrDiscipline venomState fragGasPathPtr finite_map accountsRelProps words
  storageDecodeMemory valueEncodingProofs vyperStorage bodyPtrMakeArrayStorageRobust

Theorem storage_source_load_arbitrary_provenance:
  (opc = SLOAD \/ opc = TLOAD) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ allocas_from 0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [src; Var cv] [av]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst lid opc [Var av] [vv]) /\
  eval_operand src s = SOME a /\ lookup_var cv s = SOME (n2w k) /\
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} /\
  s1 = ((update_var av (a+n2w k) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst id ADD [src; Var cv] [av]) (update_var av (a+n2w k) s) /\
  tm = step_taint (mk_inst id ADD [src; Var cv] [av]) s (update_var av (a+n2w k) s) tn /\
  step_inst_base (mk_inst lid opc [Var av] [vv]) s1 = OK (update_var vv w s1) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT H (COMPL {vv}))
    (tm with t_var := tm.t_var |+
      (vv, if opc = SLOAD then key_taint tm.t_stor (a+n2w k)
           else key_taint tm.t_trans (a+n2w k)))
    (OK ((update_var vv w s1) with vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK s1)` by
    (gvs[] >> irule clean_binop_ptr_path >> simp[eval_operand_def]) >>
  `op_taint tm (Var av) = {}` by
    (gvs[] >> metis_tac[copy_len_binop_ghost_frame]) >>
  `gas_path_ptr D 0 ctx fn PG H tm s1 0
    (DRESTRICT H (COMPL {vv}))
    (tm with t_var := tm.t_var |+
      (vv, if opc = SLOAD then key_taint tm.t_stor (a+n2w k)
           else key_taint tm.t_trans (a+n2w k)))
    (OK ((update_var vv w s1) with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule storage_body_load_path >>
     simp[update_var_def, lookup_var_def, eval_operand_def, allocas_from_def] >>
     qexistsl_tac [`lid`, `Var av`] >>
     gvs[update_var_def, lookup_var_def, eval_operand_def, op_taint_def,
         FLOOKUP_UPDATE]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem storage_range_agree_dead_bytes:
  storage_range_agree st rt a tv ==>
  (dead_bytes rt (w2n a) tv j b <=> dead_bytes st (w2n a) tv j b)
Proof
  strip_tac >> irule (cj 1 dead_bytes_live_frame) >>
  rpt strip_tac >>
  `i < dimword (:256)` by
    (fs[storage_range_agree_def] >> decide_tac) >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >> strip_tac >>
  first_x_assum (qspecl_then [`n2w i`, `c`] mp_tac) >>
  simp[w2n_n2w]
QED

Theorem copied_storage_range_live_memory:
  storage_range_agree st rt a tv /\
  (!i. i < type_slot_size tv ==>
    mem_word_at (dst+32*i) mem = lookup_storage (a+n2w i) rt) ==>
  storage_live_memory st (w2n a) tv dst mem
Proof
  strip_tac >> simp[storage_live_memory_def, copy_bytes_def] >>
  rpt strip_tac >>
  `w2n a+i < dimword (:256)` by
    (fs[storage_range_agree_def] >> decide_tac) >>
  `w2n (a+n2w i) = w2n a+i` by
    (Cases_on `a` >> fs[word_add_n2w]) >>
  qpat_x_assum `!i. i < _ ==> _` drule >> strip_tac >>
  simp[valueEncodingProofsTheory.mem_bytes_at_word] >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >> strip_tac >>
  first_x_assum (qspecl_then [`a+n2w i`, `b`] mp_tac) >>
  simp[read_slot_def] >> Cases_on `a` >>
  fs[word_add_n2w, arithmeticTheory.ADD_COMM]
QED

Theorem copied_storage_range_robust_decode:
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\ storage_range_agree st rt a tv /\
  (!i. i < type_slot_size tv ==>
    mem_word_at (dst+32*i) mem = lookup_storage (a+n2w i) rt) /\
  (!i j. i < type_slot_size tv /\ j < 32 /\ dst+32*i+j IN tainted ==>
    j IN key_taint keys (a+n2w i)) /\
  (!k j. w2n a <= w2n k /\ w2n k < w2n a+type_slot_size tv /\
    j < 32 /\ j IN key_taint keys k ==>
    dead_bytes rt (w2n a) tv (w2n k) j) ==>
  !m. mem_agree_outside tainted mem m ==> val_in_memory tv v dst m
Proof
  strip_tac >> match_mp_tac storage_live_memory_robust_decode >>
  qexistsl_tac [`w2n a`, `st`] >> simp[] >>
  conj_tac
  >- (irule copied_storage_range_live_memory >> metis_tac[]) >>
  rpt strip_tac >>
  `w2n a+i < dimword (:256)` by
    (fs[storage_range_agree_def] >> decide_tac) >>
  `w2n (a+n2w i) = w2n a+i` by
    (Cases_on `a` >> fs[word_add_n2w]) >>
  `j IN key_taint keys (a+n2w i)` by
    metis_tac[arithmeticTheory.ADD_ASSOC] >>
  `dead_bytes rt (w2n a) tv (w2n a+i) j` by
    (qpat_x_assum `!k j. _` (qspecl_then [`a+n2w i`, `j`] mp_tac) >> simp[]) >>
  drule storage_range_agree_dead_bytes >>
  disch_then (qspecl_then [`i+w2n a`, `j`] (irule o iffLR)) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC
QED
