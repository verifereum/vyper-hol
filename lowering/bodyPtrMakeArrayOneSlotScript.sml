(* Existential counted copy boundary: loaded key taint is retained. *)
Theory bodyPtrMakeArrayOneSlot
Ancestors
  bodyPtrMakeArrayCopiedWord bodyPtrMakeArrayCopyStep exprSimStorageCopy valueEncodingProps
  ptrDiscipline venomState venomMemProps finite_map pred_set context

Theorem external_one_slot_endpoint:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [src] [tmp]) /\
  step_inst_base (mk_inst id opc [src] [tmp]) s = OK (update_var tmp w s) /\
  eval_operand src s = SOME key /\ tmp <> dst /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME (n2w b) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst sid MSTORE [Var dst; Var tmp] []) /\
  (!x. not_fresh_at sa x ==> tmp <> x) /\ b + 32 < dimword(:256) ==>
  ?sf H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK sf) /\
    sf.vs_current_bb = s.vs_current_bb /\
    sf.vs_inst_idx = s.vs_inst_idx + 2 /\
    mem_word_at b sf.vs_memory = w /\
    lookup_var dst sf = SOME (n2w b) /\ ptr_covers H tm dst sf 32 /\
    mem_agree_outside {i | b <= i /\ i < b + 32} sf.vs_memory s.vs_memory /\
    tm.t_mem = (tn.t_mem DIFF {i | b <= i /\ i < b + 32}) UNION
      {b + k | k IN (if opc = SLOAD then key_taint tn.t_stor key
                     else if opc = TLOAD then key_taint tn.t_trans key else {})} /\
    (!i. i < b \/ b + 32 <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    copy_static sf = copy_static s /\ LENGTH s.vs_memory <= LENGTH sf.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `sm = (update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gm = step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s)` >>
  qabbrev_tac `tnm = step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn` >>
  qabbrev_tac `sf = (mstore (w2n (n2w b : bytes32)) w sm) with vs_inst_idx := SUC sm.vs_inst_idx` >>
  qabbrev_tac `H = step_prov PG Gm (mk_inst sid MSTORE [Var dst; Var tmp] []) (mstore (w2n (n2w b : bytes32)) w sm)` >>
  qabbrev_tac `tm = step_taint (mk_inst sid MSTORE [Var dst; Var tmp] []) sm (mstore (w2n (n2w b : bytes32)) w sm) tnm` >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  qexistsl_tac [`sf`, `H`, `tm`] >>
  conj_tac >-
    (unabbrev_all_tac >>
     qpat_assum `w2n (n2w b : bytes32) = b`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule external_word_store_path >>
     simp[] >> metis_tac[]) >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all external_word_store_frame >> strip_tac >>
  `lookup_var dst sm = SOME (n2w b) /\ eval_operand (Var tmp) sm = SOME w` by
    fs[lookup_var_def, update_var_def, eval_operand_def, FLOOKUP_UPDATE] >>
  drule_all mstore_raw_ghost_frame >>
  disch_then (qspecl_then [`tnm`, `sid`, `PG`, `Gm`] strip_assume_tac) >>
  `tnm.t_var = tn.t_var |+ (tmp, if opc = SLOAD then key_taint tn.t_stor key
      else if opc = TLOAD then key_taint tn.t_trans key else {}) /\
   tnm.t_stor = tn.t_stor /\ tnm.t_trans = tn.t_trans /\ tnm.t_imm = tn.t_imm` by
    metis_tac[external_load_ghost_frame] >>
  `tm.t_var = tnm.t_var /\ tm.t_stor = tn.t_stor /\
   tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by metis_tac[] >>
  ntac 8 (conj_tac >- metis_tac[]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `tmp <> x` by metis_tac[] >>
      conj_tac >- simp[lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE] >>
      conj_tac >- simp[FLOOKUP_DRESTRICT] >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  simp[] >>
  simp[copy_static_def, mstore_def, update_var_def, venom_state_component_equality,
       LENGTH_mstore_eq]
QED
