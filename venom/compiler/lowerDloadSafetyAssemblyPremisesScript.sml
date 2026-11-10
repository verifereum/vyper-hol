(* Reachable source obligations exposed to ordinary effect consumers. *)
Theory lowerDloadSafetyAssemblyPremises
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyValues lowerDloadSafetyAllocBounds
  lowerDloadSafetyKernel ptrDiscipline finite_map words list pred_set

Theorem ld_sync_access_ok:
  ptr_discipline lo C vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  access_ok lo G fn inst s
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem ld_sync_taint_ok:
  ptr_discipline lo C vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  taint_ok fn tn inst s
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem ld_copy_byte_store_operands_untainted:
  taint_ok fn tn inst s /\
  (inst.inst_opcode = MCOPY \/ inst.inst_opcode = MSTORE8) /\
  MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  simp[taint_ok_def] >> rpt strip_tac >>
  spose_not_then assume_tac >> res_tac >> gvs[]
QED

(* Width audit (C1.11.5.35), not a proved invariant:
   ptrDisciplineScript.sml:239-249 initializes the variable masks to FEMPTY
   and reads them through op_taint.  mem_word_taint/key_taint (252-258) and
   shift_taint (319-329) explicitly restrict results to j<32; out_taint
   (332-354) additionally forwards ASSIGN's input mask.  set_var_taint and
   step_taint (356-361,403-412) update one output or restrict the old map.
   PHIs (415-437) copy masks from the pre-block state in parallel.

   The exact sufficient reachability invariant to prove separately is:
     frame_reachable vs0 C stk PG G tn fn inst s ==>
       (!v m. FLOOKUP tn.t_var v = SOME m ==>
               m SUBSET {j | j < 32}) /\
       (!f v m. MEM f stk /\ FLOOKUP f.cf_tvar v = SOME m ==>
                  m SUBSET {j | j < 32}).
   The saved-frame conjunct is needed by the ret rule (486-499), which
   restores a DRESTRICT of cf_tvar.  Calls save the current bounded map
   and clear callee t_var; entry starts empty.  The ordinary and block
   rules need out_taint/set_var_taint and parallel-PHI preservation.
   From its current-map conjunct, Cases_on op and op_taint_def give the
   mask bound required by MSTORE.  taint_within supplies no such bound.
   No width theorem or call-stack induction is asserted in this theory.
*)

Theorem ld_write_access_cases:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_write_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_write_ranges inst s) /\ 0 < n /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword (:256)) ==>
  (w2n x+n <= lo /\ y=x) \/
  (?a b c sz delta. op_prov H ops.iao_ofst = SOME a /\
    FLOOKUP A a = SOME (b,c,sz) /\ w2n x=b+delta /\
    w2n y=c+delta /\ delta+n <= sz)
Proof
  strip_tac >>
  qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
  simp[access_ok_def] >> strip_tac >>
  qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges inst s) /\ _ ==> _`
    (qspecl_then [`w2n x`, `n`] mp_tac) >> simp[] >>
  Cases_on `op_prov H ops.iao_ofst` >> gvs[]
  >- (Cases_on `w2n y+n <= lo` >> simp[] >>
      strip_tac >> Cases_on `ops.iao_ofst` >>
      gvs[op_prov_def, FLOOKUP_o_f]) >>
  `?b c sz. FLOOKUP A x' = SOME (b,c,sz)` by
    metis_tac[ld_wordrel_SOME] >>
  `op_prov (ld_erase A o_f H) ops.iao_ofst = SOME (b,sz)` by
    (Cases_on `ops.iao_ofst` >> gvs[op_prov_def, FLOOKUP_o_f, ld_erase_def]) >>
  simp[] >> strip_tac >>
  `b <= w2n x /\ w2n x+n <= b+sz` by
    (gvs[op_prov_def, FLOOKUP_o_f, ld_erase_def]) >>
  `w2n y = c+(w2n x-b)` by
    (irule ld_wordrel_site_value >> simp[] >>
     qexistsl_tac [`A`, `x'`, `sz`] >> simp[] >>
     metis_tac[]) >>
  disj2_tac >> qexists_tac `w2n x-b` >>
  simp[] >> decide_tac
QED

Theorem ld_alloc_target_no_wrap:
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\
  (HD frames).lf_tgt.vs_alloca_next < dimword (:256) ==>
  !a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword (:256)
Proof
  rpt strip_tac >> drule_all ld_slot_source_site >> strip_tac >>
  `ld_maps A (EL j frames)` by gvs[EVERY_EL] >>
  `FLOOKUP (EL j frames).lf_src.vs_allocas aid = SOME (b,sz)` by
    gvs[ld_sites_def] >>
  `FLOOKUP (EL j frames).lf_tgt.vs_allocas aid = SOME (c,sz)` by
    (gvs[ld_maps_def] >>
     qpat_x_assum `!aid b n. FLOOKUP _ aid = SOME (b,n) ==> ?c. _ /\ _` drule >> strip_tac >> gvs[]) >>
  `(j,aid,c,sz) IN ld_sites frames F` by
    (simp[ld_sites_def] >> metis_tac[]) >>
  drule_all ld_global_bounds >> simp[]
QED
