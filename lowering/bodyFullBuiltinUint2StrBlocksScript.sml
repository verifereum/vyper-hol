Theory bodyFullBuiltinUint2StrBlocks
Ancestors
  bodyPtrDefs bodyPtrBytestringBuiltinsCalldataCopy
  immutableMemoryFrame valueEncodingProps loweringStateRelDefs
  ptrDiscipline venomState finite_map words list pred_set byte
  localPtrsProps exprSimProps exprSimUint2Str fragGasSeqPtr
  bodyPtrBytestringBuiltinsUintGhost ptrSafeRun venomExecSemantics venomInst
  exprLoweringProps emitHelperProps codegenRel contextCodegenRel bodyFullUnwrapRun
  exprSimPtrLiteralOps bodyPtrBytestringBuiltinsUintArithmetic
  bodyMemBiUint2StrBlocks bodyFullGhostFrame fragGasOriginPtrLoop bodyFullUnwrapSlotPost
  lowerDloadPtrOrdinary exprSimPtrTopLevelImmutableCopy

val _ = temp_delsimps ["copy_allocas_update", "copy_allocas_inst_idx",
                        "copy_update_inst_idx", "copy_mstore_inst_idx"];

Theorem u2s_clean_store_ghost_at:
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_rel fn cenv es.scopes s /\ alloca_inv s /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  lo <= b /\ b <= at /\ at+32 <= b+sz ==>
  ghost_inv_at D lo d cenv cx es G
    (tn with t_mem := tn.t_mem DIFF {j | at <= j /\ j < at+32})
    (mstore at w s)
Proof
  strip_tac >>
  `LENGTH (word_to_bytes w T) = 32` by
    simp[LENGTH_word_to_bytes, dimword_def,
         fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  `mem_bytes_at 0 lo (mstore at w s).vs_memory =
   mem_bytes_at 0 lo s.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  fs[ghost_inv_at_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `ptr_covers G tn p s sz'` by metis_tac[] >>
      conj_tac
      >- gvs[ptr_covers_def, op_taint_def, mstore_def,
             write_memory_with_expansion_def, lookup_var_def] >>
      rpt strip_tac >>
      `lookup_var p s = SOME w'` by
        gvs[lookup_var_def, mstore_def, write_memory_with_expansion_def] >>
      `local_region cenv es.scopes s name (w2n w') sz'` by
        (simp[local_region_def] >> metis_tac[]) >>
      drule_all local_ptrs_rel_alloca_disjoint >> disch_tac >>
      `val_wf entry.type entry.value /\
       val_footprint entry.type entry.value <= sz'` by
        (fs[local_ptrs_rel_def] >>
         qpat_x_assum `!name' entry' p' sz''. _` drule_all >> strip_tac >>
         drule val_footprint_le >> simp[]) >>
      `w2n w' + val_footprint entry.type entry.value <= at \/
       at + 32 <= w2n w'` by (fs[regions_disjoint_def] >> decide_tac) >>
      gvs[immutable_mstore_as_write] >>
      irule write_memory_robust_exterior >> simp[] >>
      qexistsl_tac [`word_to_bytes w T`, `at`, `s`, `tn.t_mem`] >>
      simp[LENGTH_word_to_bytes, dimword_def,
           fcpLib.INDEX_CONV ``dimindex(:256)``] >> metis_tac[])
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >>
      gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def,
          mstore_def, write_memory_with_expansion_def, lookup_var_def])
  >> gvs[op_taint_def, stor_taint_ok_at_def, allocas_from_def,
         mstore_def, write_memory_with_expansion_def] >> metis_tac[]
QED

Theorem u2s_clean_scalar_seq_cons:
  MEM opc [Mod; Div; EQ; ADD] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) /\
  inst_seq_ptr D lo ctx fn PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) ys
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn (mk_inst id opc ops [out]::ys) s G' tn'
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule uint_scalar_ghost >> simp[update_var_def] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (`!v. MEM (Var v) ops ==> FLOOKUP G v = NONE` by
       (rpt strip_tac >> first_x_assum drule >> simp[op_prov_def]) >>
     gvs[] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     gvs[update_var_def, FLOOKUP_DEF] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def, mk_inst_def] >>
  gvs[mk_inst_def]
QED

Theorem u2s_clean_assign_seq_cons:
  op_prov G op = NONE /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK (update_var out w s) /\
  inst_seq_ptr D lo ctx fn PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) ys
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn (mk_inst id ASSIGN [op] [out]::ys) s G' tn'
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id ASSIGN [op] [out]) (update_var out w s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id ASSIGN [op] [out]) s (update_var out w s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule uint_assign_ghost >> simp[update_var_def]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id ASSIGN [op] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  simp[Once inst_seq_ptr_def, mk_inst_def] >> gvs[mk_inst_def]
QED

(* allocas_from is supplied by ghost_inv_at at the loop boundary. *)
Theorem u2s_body_pointer_sequence:
  not_fresh_at a p /\ n+32 <= sz /\ b+sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  0 < x /\ i < n /\ x < dimword(:256) /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\
  lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  lookup_var p s = SOME (n2w b) /\ FLOOKUP G p = SOME (b,sz) /\
  op_taint tn (Var p) = {} /\
  (!k. k < 2 ==> FLOOKUP G (u2s_var a k) = NONE /\
                   op_taint tn (Var (u2s_var a k)) = {}) /\
  s.vs_inst_idx = 0 ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      (TAKE 9 (u2s_body a (Var p) n)) s G' tn') /\
    (!r. not_fresh_at a r ==> FLOOKUP G' r = FLOOKUP G r /\
                            op_taint tn' (Var r) = op_taint tn (Var r)) /\
    FLOOKUP G' p = SOME (b,sz) /\ op_taint tn' (Var p) = {} /\
    (!k. k < 2 ==> FLOOKUP G' (u2s_var a k) = NONE /\
                   op_taint tn' (Var (u2s_var a k)) = {}) /\
    tn'.t_mem = tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `!k. p <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  `!r. not_fresh_at a r ==> !k. r <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  `FLOOKUP G (u2s_var a 0) = NONE /\ FLOOKUP G (u2s_var a 1) = NONE /\
   op_taint tn (Var (u2s_var a 0)) = {} /\
   op_taint tn (Var (u2s_var a 1)) = {}` by simp[] >>
  qabbrev_tac `G2 = DRESTRICT G (COMPL {u2s_var a 5; u2s_var a 6})` >>
  qabbrev_tac `tn2 = tn with t_var := tn.t_var |+ (u2s_var a 5,{}) |+ (u2s_var a 6,{})` >>
  qabbrev_tac `s2 = update_var (u2s_var a 6) (48w + safe_mod (n2w x) 10w)
    (update_var (u2s_var a 5) (safe_mod (n2w x) 10w) s) with vs_inst_idx := 2` >>
  qabbrev_tac `G3 = G2 |+ (u2s_var a 7,(b,sz))` >>
  qabbrev_tac `tn3 = tn2 with t_var := tn2.t_var |+ (u2s_var a 7,{})` >>
  qabbrev_tac `s3 = update_var (u2s_var a 7) (n2w (b+n)) s2 with vs_inst_idx := 3` >>
  qabbrev_tac `subi = mk_inst (a.cs_next_id+11) SUB
    [Var (u2s_var a 7); Var (u2s_var a 1)] [u2s_var a 8]` >>
  qabbrev_tac `u4 = update_var (u2s_var a 8) (n2w (b+n) - n2w i) s3` >>
  qabbrev_tac `G4 = step_prov PG G3 subi u4` >>
  qabbrev_tac `tn4 = step_taint subi s3 u4 tn3` >>
  qabbrev_tac `s4 = u4 with vs_inst_idx := 4` >>
  qabbrev_tac `tn5 = tn4 with t_mem := tn4.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32}` >>
  qexistsl_tac
    [`DRESTRICT G4 (COMPL {u2s_var a 0; u2s_var a 1; u2s_var a 9; u2s_var a 10})`,
     `tn5 with t_var := tn5.t_var |+ (u2s_var a 9,{}) |+ (u2s_var a 0,{})
       |+ (u2s_var a 10,{}) |+ (u2s_var a 1,{})`] >>
  conj_tac >- suspend "sequence" >>
  suspend "frame"
QED

Resume u2s_body_pointer_sequence[frame]:
  `!r. r <> u2s_var a 8 ==> op_taint tn4 (Var r) = op_taint tn3 (Var r)` by
    simp[Abbr `tn4`, Abbr `subi`, Abbr `u4`, pointer_sub_ghost_frame] >>
  fs[op_taint_def] >>
  simp[Abbr `tn5`, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  simp[Abbr `G4`, Abbr `tn4`, Abbr `subi`, Abbr `u4`, pointer_sub_ghost_frame] >>
  simp[Abbr `G3`, Abbr `G2`, Abbr `tn3`, Abbr `tn2`,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  rpt strip_tac >> gvs[]
QED

Resume u2s_body_pointer_sequence[sequence]:
  gen_tac >> fs[op_taint_def] >> simp[u2s_body_def, u2s_inst_def] >>
  irule u2s_clean_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, op_taint_def] >>
  qexists_tac `safe_mod (n2w x) 10w` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  simp[GSYM mk_inst_def] >>
  irule u2s_clean_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, allocas_from_def, update_var_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qexists_tac `48w + safe_mod (n2w x) 10w` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[GSYM mk_inst_def] >>
  simp[GSYM COMPL_UNION, INSERT_UNION_EQ] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D lo ctx fn PG G2 tn2 cs ss` >>
  `ss = s2` by simp[Abbr `ss`, Abbr `s2`, update_var_def] >> gvs[] >>
  `FLOOKUP G2 p = SOME (b,sz) /\ op_taint tn2 (Var p) = {} /\
   lookup_var p s2 = SOME (n2w b) /\ allocas_from lo s2` by
    (fs[lookup_var_def, allocas_from_def] >>
     simp[Abbr `G2`, Abbr `tn2`, Abbr `s2`, FLOOKUP_DRESTRICT,
          FLOOKUP_UPDATE, op_taint_def, lookup_var_def, allocas_from_def,
          update_var_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (a.cs_next_id+10) ADD [Var p; Lit (n2w n)]
      [u2s_var a 7]) s2 = OK (update_var (u2s_var a 7) (n2w b+n2w n) s2)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  `step_prov PG G2 (mk_inst (a.cs_next_id+10) ADD [Var p; Lit (n2w n)]
      [u2s_var a 7]) (update_var (u2s_var a 7) (n2w b+n2w n) s2) = G3 /\
   step_taint (mk_inst (a.cs_next_id+10) ADD [Var p; Lit (n2w n)]
      [u2s_var a 7]) s2 (update_var (u2s_var a 7) (n2w b+n2w n) s2) tn2 = tn3` by
    (simp[Abbr `G3`, Abbr `tn3`] >> irule literal_add_ghost >> simp[]) >>
  simp[Abbr `cs`, Once inst_seq_ptr_def] >>
  conj_tac
  >- (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def] >>
      simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
      rpt gen_tac >> Cases_on `op` >> simp[op_taint_def] >>
      fs[op_taint_def] >> metis_tac[]) >>
  `s2.vs_inst_idx = 2` by simp[Abbr `s2`, update_var_def] >>
  `update_var (u2s_var a 7) (n2w b+n2w n) s2 with
     vs_inst_idx := SUC s2.vs_inst_idx = s3` by
    simp[Abbr `s3`, word_add_n2w] >> simp[] >>
  suspend "middle"
QED

Resume u2s_body_pointer_sequence[middle]:
  `lookup_var (u2s_var a 7) s3 = SOME (n2w (b+n)) /\
   lookup_var (u2s_var a 1) s3 = SOME (n2w i) /\
   FLOOKUP G3 (u2s_var a 7) = SOME (b,sz) /\
   op_taint tn3 (Var (u2s_var a 7)) = {} /\
   op_taint tn3 (Var (u2s_var a 1)) = {} /\ allocas_from lo s3` by
    (fs[lookup_var_def, allocas_from_def] >>
     simp[Abbr `s3`, Abbr `G3`, Abbr `tn3`, Abbr `s2`, Abbr `tn2`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def,
          allocas_from_def] >> metis_tac[]) >>
  `step_inst_base subi s3 = OK u4` by
    simp[Abbr `subi`, Abbr `u4`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, eval_operand_def] >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac
  >- (simp[Abbr `subi`, ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def] >>
      simp[GSYM mk_inst_def, step_inst_non_invoke] >>
      simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
           eval_operand_def, update_var_def] >>
      simp[Abbr `u4`, update_var_def] >>
      rpt gen_tac >> Cases_on `op` >> simp[op_taint_def] >>
      fs[op_taint_def] >> metis_tac[]) >>
  `s3.vs_inst_idx = 3` by simp[Abbr `s3`] >>
  `u4 with vs_inst_idx := SUC s3.vs_inst_idx = s4` by simp[Abbr `s4`] >>
  simp[] >>
  `ptr_covers G4 tn4 (u2s_var a 8)
      (u4 with vs_inst_idx := SUC s3.vs_inst_idx) 32` by
    (map_every qunabbrev_tac [`G4`, `tn4`, `subi`, `u4`] >>
     irule pointer_sub_covers >> simp[eval_operand_def] >> decide_tac) >>
  `ptr_covers G4 tn4 (u2s_var a 8) s4 32` by metis_tac[] >>
  `(n2w (b+n) - n2w i : bytes32) = n2w (b+n-i)` by
    (irule uint2str_sub_word >> conj_tac >- decide_tac >>
     qexists_tac `sz` >> decide_tac) >>
  `op_taint tn4 (Var (u2s_var a 6)) = {}` by
    (simp[Abbr `tn4`, Abbr `subi`, Abbr `u4`, pointer_sub_ghost_frame] >>
     simp[Abbr `tn3`, Abbr `tn2`, op_taint_def, FLOOKUP_UPDATE]) >>
  `lookup_var (u2s_var a 8) s4 = SOME (n2w (b+n-i)) /\
   lookup_var (u2s_var a 6) s4 = SOME (48w + safe_mod (n2w x) 10w) /\
   allocas_from lo s4` by
    (simp[Abbr `s4`, Abbr `u4`, Abbr `s3`, Abbr `s2`,
          lookup_var_def, update_var_def, allocas_from_def, FLOOKUP_UPDATE] >>
     fs[allocas_from_def] >> metis_tac[]) >>
  `b+n-i < dimword(:256)` by decide_tac >>
  `step_inst_base (mk_inst (a.cs_next_id+12) MSTORE
      [Var (u2s_var a 8); Var (u2s_var a 6)] []) s4 =
     OK (mstore (b+n-i) (48w + safe_mod (n2w x) 10w) s4)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
         exec_write2_def] >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac
  >- (irule exprPtrUnwrapCopyEdgesTheory.ptr_inst_ok_mstore_tainted >> simp[]) >>
  `step_taint (mk_inst (a.cs_next_id+12) MSTORE
      [Var (u2s_var a 8); Var (u2s_var a 6)] []) s4
      (mstore (b+n-i) (48w + safe_mod (n2w x) 10w) s4) tn4 = tn5` by
    (simp[Abbr `tn5`] >>
     qpat_assum `lookup_var (u2s_var a 8) s4 = _`
       (mp_then Any mp_tac clean_mstore_taint_state) >>
     disch_then (qspecl_then [`tn4`, `a.cs_next_id+12`,
       `Var (u2s_var a 6)`, `48w + safe_mod (n2w x) 10w`] mp_tac) >>
     simp[eval_operand_def]) >>
  simp[step_prov_def, mk_inst_def, set_prov_def] >>
  simp[GSYM mk_inst_def] >>
  suspend "tail"
QED

Resume u2s_body_pointer_sequence[tail]:
  simp[DRESTRICT_UNIV] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D lo ctx fn PG G4 tn5 cs s5` >>
  `!k. k < 2 ==> FLOOKUP G4 (u2s_var a k) = NONE /\
                      op_taint tn5 (Var (u2s_var a k)) = {}` by
    (gen_tac >> disch_tac >>
     `k <> 8 /\ k <> 7 /\ k <> 6 /\ k <> 5` by decide_tac >>
     qpat_x_assum `n2w (b+n) - n2w i = _` kall_tac >>
     `op_taint tn4 (Var (u2s_var a k)) = op_taint tn3 (Var (u2s_var a k))` by
       simp[Abbr `tn4`, Abbr `subi`, Abbr `u4`, pointer_sub_ghost_frame] >>
     fs[op_taint_def] >>
     simp[Abbr `tn5`, Abbr `G4`, Abbr `subi`, Abbr `u4`,
          pointer_sub_ghost_frame, op_taint_def] >>
     simp[Abbr `G3`, Abbr `G2`, Abbr `tn3`, Abbr `tn2`,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]) >>
  `lookup_var (u2s_var a 0) s5 = SOME (n2w x) /\
   lookup_var (u2s_var a 1) s5 = SOME (n2w i) /\ allocas_from lo s5` by
    (simp[Abbr `s5`, Abbr `s4`, Abbr `u4`, Abbr `s3`, Abbr `s2`,
          mstore_def, write_memory_with_expansion_def, update_var_def,
          lookup_var_def, FLOOKUP_UPDATE, allocas_from_def] >>
     fs[allocas_from_def, lookup_var_def] >> metis_tac[]) >>
  fs[op_taint_def] >>
  simp[Abbr `cs`] >>
  irule u2s_clean_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, op_taint_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  simp[GSYM mk_inst_def] >>
  qexists_tac `safe_div (n2w x) 10w` >> simp[] >>
  irule u2s_clean_assign_seq_cons >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       allocas_from_def, update_var_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[GSYM mk_inst_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qexists_tac `safe_div (n2w x) 10w` >> simp[] >>
  irule u2s_clean_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, allocas_from_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qexists_tac `1w + n2w i` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[GSYM mk_inst_def] >>
  conj_tac >- (fs[lookup_var_def] >> simp[WORD_ADD_COMM]) >>
  irule u2s_clean_assign_seq_cons >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       allocas_from_def, update_var_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qexists_tac `1w + n2w i` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[GSYM mk_inst_def, inst_seq_ptr_def] >>
  AP_TERM_TAC >> simp[EXTENSION] >> metis_tac[]
QED

Finalise u2s_body_pointer_sequence

Theorem u2s_body_joint_step:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ n+32 <= sz /\
  b+sz < dimword(:256) /\ lo <= b /\ ~ctx_has_dalloca ctx /\
  u2s_digits a b n X x str s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
       ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ lookup_var p s = SOME (n2w b) /\
  op_taint tn (Var p) = {} /\
  (!k. k < 2 ==> FLOOKUP G (u2s_var a k) = NONE /\
                   op_taint tn (Var (u2s_var a k)) = {}) /\
  (!j. b+n+32-LENGTH str <= j /\ j < b+n+32 ==> j NOTIN tn.t_mem) /\
  0 < x /\ LENGTH str < n /\ ~s.vs_halted /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 0 ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,G',tn')) /\
    u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
         ghost_inv_at (DF H) lo d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    FLOOKUP G' p = SOME (b,sz) /\ lookup_var p t = SOME (n2w b) /\
    op_taint tn' (Var p) = {} /\
    (!k. k < 2 ==> FLOOKUP G' (u2s_var a k) = NONE /\
                     op_taint tn' (Var (u2s_var a k)) = {}) /\
    LENGTH (CHR (48+x MOD 10)::str) <= n /\
    (!j. b+n+32-LENGTH (CHR (48+x MOD 10)::str) <= j /\ j < b+n+32 ==>
         j NOTIN tn'.t_mem) /\
    t.vs_current_bb = u2s_label a 1 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `u2s_safe H0 ctx fn cenv cx es a (Var p) b sz inst sr s` by metis_tac[] >>
  drule u2s_body_iteration >> simp[] >> disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (TAKE 9 (u2s_body a (Var p) n)) s = OK t` >>
  `ghost_inv_at (DF H0) lo d cenv cx es G tn s` by metis_tac[] >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  `?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn (TAKE 9 (u2s_body a (Var p) n)) s G' tn') /\
    (!r. not_fresh_at a r ==> FLOOKUP G' r = FLOOKUP G r /\
                            op_taint tn' (Var r) = op_taint tn (Var r)) /\
    FLOOKUP G' p = SOME (b,sz) /\ op_taint tn' (Var p) = {} /\
    (!k. k < 2 ==> FLOOKUP G' (u2s_var a k) = NONE /\
                   op_taint tn' (Var (u2s_var a k)) = {}) /\
    tn'.t_mem = tn.t_mem DIFF {j | b+n-LENGTH str <= j /\ j < b+n-LENGTH str+32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    (irule u2s_body_pointer_sequence >> fs[u2s_digits_def] >>
     qexists_tac `x` >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t` by
    (rpt strip_tac >>
     `u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s` by metis_tac[] >>
     drule u2s_body_iteration >> simp[] >> disch_then drule_all >>
     strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok (TAKE 9 (u2s_body a (Var p) n)) s` by
    (irule u2s_body_mem_ok >>
     fs[u2s_digits_def, u2s_safe_def] >>
     simp[venomStateTheory.eval_operand_def] >>
     `b+sz <= s.vs_alloca_next` by
       (fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
     `n2w b + n2w n - n2w (LENGTH str) = (n2w (b+n-LENGTH str):bytes32)` by
       (irule (cj 4 u2s_word_arithmetic) >> simp[] >> metis_tac[]) >>
     simp[] >> decide_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := 9),G',tn')` by
    (gen_tac >>
     qspecl_then [`TAKE 9 (u2s_body a (Var p) n)`, `s`, `t`]
       mp_tac run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspecl_then [`G`, `tn`, `G'`, `tn'`] mp_tac) >>
     disch_then (qspecl_then [`ctx`, `fn`,
       `<|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|>`] mp_tac) >>
     simp[u2s_body_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
     metis_tac[]) >>
  `allocas_from lo t` by
    (fs[allocas_from_def, u2s_safe_def, u2s_frame_def] >>
     ntac 2 (qpat_x_assum `_ = sr` (mp_tac o Q.AP_TERM `\z. z.vs_allocas`)) >>
     simp[] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (t with vs_inst_idx := 9,G',tn') []
       (OK (jump_to (u2s_label a 1) t),G',tn')` by
    (gen_tac >>
     `jump_to (u2s_label a 1) (t with vs_inst_idx := 9) =
      jump_to (u2s_label a 1) t` by simp[jump_to_def] >>
     pop_assum (fn th => once_rewrite_tac [GSYM th]) >>
     irule jmp_origin_ptr_path >>
     simp[u2s_body_def, u2s_inst_def, mk_inst_def, get_instruction_def,
          allocas_from_def] >> fs[allocas_from_def]) >>
  qexistsl_tac [`jump_to (u2s_label a 1) t`, `G'`, `tn'`] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  conj_tac >- (fs[u2s_digits_def, jump_to_def, lookup_var_def] >>
    `b+(n+32)-SUC (LENGTH str) = b+n-SUC (LENGTH str)+32` by decide_tac >>
    metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac
      >- metis_tac[u2s_safe_jump]
      >> `ghost_inv_at (DF H) lo d cenv cx es G tn s` by metis_tac[]
      >> irule unwrap_slot_copy_ghost_inv_at
      >> conj_tac
      >- (fs[u2s_safe_def, u2s_frame_def, venom_state_component_equality,
             ghost_inv_at_def, jump_to_def] >> metis_tac[])
      >> conj_tac >- (fs[allocas_from_def, jump_to_def] >> metis_tac[])
      >> conj_tac
      >- (fs[ghost_inv_at_def, stor_taint_ok_at_def, u2s_safe_def,
             u2s_frame_def, venom_state_component_equality, jump_to_def])
      >> qexistsl_tac [`G`, `fn`, `sz`, `s`, `a`, `b`, `tn`]
      >> fs[u2s_safe_def, u2s_frame_def, jump_to_def, lookup_var_def,
            stmt_state_rel_def]
      >> conj_tac >- metis_tac[]
      >> conj_tac >- metis_tac[arithmeticTheory.ADD_COMM]
      >> fs[state_rel_def]) >>
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >>
      qexistsl_tac [`G`, `tn`] >> simp[] >> metis_tac[]) >>
  simp[jump_to_def, lookup_var_def, eval_operand_def] >>
  conj_tac >- (fs[u2s_safe_def, eval_operand_def, lookup_var_def]) >>
  rpt strip_tac >>
  Cases_on `b+n+32-LENGTH str <= j`
  >- (disj1_tac >> first_x_assum irule >> decide_tac) >>
  decide_tac
QED

Theorem u2s_pointer_arith_seq_cons:
  MEM opc [ADD; SUB] /\ op_prov G (Var p) = SOME region /\
  op_prov G delta = NONE /\ op_taint tn (Var p) = {} /\ op_taint tn delta = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  step_inst_base (mk_inst id opc [Var p;delta] [out]) s = OK (update_var out w s) /\
  inst_seq_ptr D lo ctx fn PG (G |+ (out,region))
    (tn with t_var := tn.t_var |+ (out,{})) ys
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn (mk_inst id opc [Var p;delta] [out]::ys) s G' tn'
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id opc [Var p;delta] [out]) (update_var out w s) =
     G |+ (out,region) /\
   step_taint (mk_inst id opc [Var p;delta] [out]) s (update_var out w s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (fs[] >>
     simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def, mk_inst_def] >>
     simp[step_taint_def, set_var_taint_def, out_taint_def, imm_taint_def,
          adopt_reset_def, mk_inst_def, update_var_def,
          mem_taint_def, store_taint_def, step_writes_def,
          source_memory_write_ranges_def, written_taint_def, range_bytes_def,
          new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
     Cases_on `eval_operand (Var p) s` >> simp[taint_component_equality]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id opc [Var p;delta] [out]) s` by
    (fs[] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     gvs[update_var_def, FLOOKUP_DEF] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def, mk_inst_def] >> gvs[mk_inst_def]
QED

Theorem u2s_pointer_assign_seq_cons:
  op_prov G op = SOME region /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK (update_var out w s) /\
  inst_seq_ptr D lo ctx fn PG (G |+ (out,region))
    (tn with t_var := tn.t_var |+ (out,{})) ys
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn (mk_inst id ASSIGN [op] [out]::ys) s G' tn'
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id ASSIGN [op] [out]) (update_var out w s) =
     G |+ (out,region) /\
   step_taint (mk_inst id ASSIGN [op] [out]) s (update_var out w s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (`eval_operand op s = SOME w` by
       (gvs[step_inst_base_opcode_eqs, mk_inst_def, AllCaseEqs(), update_var_def,
            venom_state_component_equality] >>
        qpat_x_assum `_ |+ _ = _` (mp_tac o Q.AP_TERM `\m. FLOOKUP m out`) >>
        simp[FLOOKUP_UPDATE]) >>
     mp_tac (Q.INST [`i` |-> `mk_inst id ASSIGN [op] [out]`, `a` |-> `w`]
       assign_ghost_updates) >>
     simp[mk_inst_def, set_prov_def, set_var_taint_def]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id ASSIGN [op] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     gvs[update_var_def, FLOOKUP_DEF] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def, mk_inst_def] >> gvs[mk_inst_def]
QED

Theorem u2s_clean_mstore_seq_cons:
  lookup_var p s = SOME addr /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn p s 32 /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  inst_seq_ptr D lo ctx fn PG G
    (tn with t_mem := tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) ys
    (mstore (w2n addr) w s with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn (mk_inst id MSTORE [Var p;value] []::ys) s G' tn'
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var p;value] []) s =
     OK (mstore (w2n addr) w s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  `step_prov PG G (mk_inst id MSTORE [Var p;value] []) (mstore (w2n addr) w s) = G /\
   step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n addr) w s) tn =
     tn with t_mem := tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}` by
    (irule toplevel_immutable_mstore_ghost_frame >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id MSTORE [Var p;value] []) s` by
    (irule exprPtrUnwrapCopyEdgesTheory.ptr_inst_ok_mstore_tainted >>
     simp[eval_operand_def]) >>
  simp[Once inst_seq_ptr_def, mk_inst_def] >> gvs[mk_inst_def]
QED

Theorem u2s_zero_pointer_sequence:
  not_fresh_at a p /\ 1 <= n /\ n+32 <= sz /\ b+sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_var p s = SOME (n2w b) /\ FLOOKUP G p = SOME (b,sz) /\
  op_taint tn (Var p) = {} /\ s.vs_inst_idx = 0 ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn
      (TAKE 6 (u2s_zero a (Var p) n)) s G' tn') /\
    (!r. not_fresh_at a r ==> FLOOKUP G' r = FLOOKUP G r /\
                            op_taint tn' (Var r) = op_taint tn (Var r)) /\
    FLOOKUP G' (u2s_var a 2) = SOME (b,sz) /\
    op_taint tn' (Var (u2s_var a 2)) = {} /\
    tn'.t_mem = (tn.t_mem DIFF {j | b+n <= j /\ j < b+n+32})
                          DIFF {j | b+n-1 <= j /\ j < b+n-1+32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `!k. p <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  `!r. not_fresh_at a r ==> !k. r <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  `b+n < dimword(:256) /\ b+n-1 < dimword(:256)` by decide_tac >>
  qexistsl_tac
    [`G |+ (u2s_var a 11,(b,sz)) |+ (u2s_var a 12,(b,sz))
        |+ (u2s_var a 13,(b,sz)) |+ (u2s_var a 2,(b,sz))`,
     `tn with <|t_var := tn.t_var |+ (u2s_var a 11,{}) |+ (u2s_var a 12,{})
                       |+ (u2s_var a 13,{}) |+ (u2s_var a 2,{});
                t_mem := (tn.t_mem DIFF {j | b+n <= j /\ j < b+n+32})
                                  DIFF {j | b+n-1 <= j /\ j < b+n-1+32}|>`] >>
  conj_tac >- suspend "sequence" >>
  simp[FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]
QED

Resume u2s_zero_pointer_sequence[sequence]:
  gen_tac >> simp[u2s_zero_def, u2s_inst_def] >>
  irule u2s_pointer_arith_seq_cons >>
  simp[op_prov_def, op_taint_def] >>
  qexists_tac `n2w (b+n)` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def,
       word_add_n2w] >> simp[GSYM mk_inst_def] >>
  irule u2s_clean_mstore_seq_cons >>
  simp[op_taint_def, op_prov_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, eval_operand_def, allocas_from_def, w2n_n2w,
       ptr_covers_def] >>
  conj_tac >- fs[allocas_from_def] >>
  irule u2s_pointer_arith_seq_cons >>
  fs[op_taint_def] >>
  simp[op_prov_def, op_taint_def, FLOOKUP_UPDATE, allocas_from_def,
       mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qexists_tac `n2w (b+n)` >>
  fs[lookup_var_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE, word_add_n2w] >>
  simp[GSYM mk_inst_def] >>
  irule u2s_pointer_arith_seq_cons >>
  simp[op_prov_def, op_taint_def, FLOOKUP_UPDATE, allocas_from_def,
       update_var_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qexists_tac `n2w (b+n-1)` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, GSYM n2w_sub] >>
  simp[GSYM mk_inst_def] >>
  irule u2s_clean_mstore_seq_cons >>
  simp[op_taint_def, op_prov_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, eval_operand_def, allocas_from_def, w2n_n2w,
       ptr_covers_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qmatch_goalsub_abbrev_tac `mstore z w (s with <|vs_memory := mem; vs_vars := _; vs_inst_idx := _|>)` >>
  irule u2s_pointer_assign_seq_cons >>
  simp[op_prov_def, op_taint_def, FLOOKUP_UPDATE, allocas_from_def,
       mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qexists_tac `n2w (b+n-1)` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[inst_seq_ptr_def]
QED

Finalise u2s_zero_pointer_sequence

Theorem u2s_zero_joint_result:
  valid_horizon cx st0 H0 es.storage_trace /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at a r) /\
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ 1 <= n /\ n+32 <= sz /\
  b+sz < dimword(:256) /\ lo <= b /\ ~ctx_has_dalloca ctx /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s /\
       ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ghost_kept_at lo cenv es a G0 tn0 s0 G tn /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  ~s.vs_halted /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t /\
       ghost_inv_at (DF H) lo d cenv cx es G' tn' t) /\
    ghost_kept_at lo cenv es a G0 tn0 s0 G' tn' /\
    eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1)) /\
    val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
    FLOOKUP G' (u2s_var a 2) = SOME (b,sz) /\
    op_taint tn' (Var (u2s_var a 2)) = {} /\
    (!j. b+n-1 <= j /\ j < b+n+32 ==> j NOTIN tn'.t_mem) /\
    t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `u2s_safe H0 ctx fn cenv cx es a (Var p) b sz inst sr s` by metis_tac[] >>
  drule u2s_zero_result >> simp[] >> disch_then drule_all >>
  disch_then (qspec_then `ty` strip_assume_tac) >>
  rename1 `run_inst_seq (TAKE 6 (u2s_zero a (Var p) n)) s = OK t` >>
  `allocas_from lo s` by (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `lookup_var p s = SOME (n2w b)` by fs[u2s_safe_def, eval_operand_def] >>
  drule_all u2s_zero_pointer_sequence >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr t` by
    (rpt strip_tac >>
     `u2s_safe H ctx fn cenv cx es a (Var p) b sz inst sr s` by metis_tac[] >>
     drule u2s_zero_result >> simp[] >> disch_then drule_all >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok (TAKE 6 (u2s_zero a (Var p) n)) s` by
    (irule u2s_zero_mem_ok >>
     fs[u2s_safe_def, eval_operand_def] >>
     `b+sz <= s.vs_alloca_next` by
       (fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
     simp[word_add_n2w, GSYM n2w_sub, w2n_n2w] >> decide_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := 6),G',tn')` by
    (gen_tac >>
     qspecl_then [`TAKE 6 (u2s_zero a (Var p) n)`, `s`, `t`]
       mp_tac run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspecl_then [`G`, `tn`, `G'`, `tn'`] mp_tac) >>
     disch_then (qspecl_then [`ctx`, `fn`,
       `<|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|>`] mp_tac) >>
     simp[u2s_zero_def, u2s_inst_def, mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `allocas_from lo t` by
    (fs[allocas_from_def, u2s_safe_def, u2s_frame_def] >>
     ntac 2 (qpat_x_assum `_ = sr` (mp_tac o Q.AP_TERM `\z. z.vs_allocas`)) >>
     simp[] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (t with vs_inst_idx := 6,G',tn') []
       (OK (jump_to (u2s_label a 5) t),G',tn')` by
    (gen_tac >>
     `jump_to (u2s_label a 5) (t with vs_inst_idx := 6) =
      jump_to (u2s_label a 5) t` by simp[jump_to_def] >>
     pop_assum (fn th => once_rewrite_tac [GSYM th]) >>
     irule jmp_origin_ptr_path >>
     simp[u2s_zero_def, u2s_inst_def, mk_inst_def, get_instruction_def,
          allocas_from_def] >> fs[allocas_from_def]) >>
  qexistsl_tac [`jump_to (u2s_label a 5) t`, `G'`, `tn'`] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  conj_tac >- suspend "ghost" >>
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >>
      qexistsl_tac [`G`, `tn`] >> simp[SUBSET_DEF] >> metis_tac[]) >>
  fs[jump_to_def, eval_operand_def, lookup_var_def] >>
  rpt strip_tac >> decide_tac
QED

Resume u2s_zero_joint_result[ghost]:
  rpt strip_tac
  >- metis_tac[u2s_safe_jump] >>
  `ghost_inv_at (DF H) lo d cenv cx es G tn s` by metis_tac[] >>
  irule unwrap_slot_copy_ghost_inv_at >>
  conj_tac
  >- (fs[u2s_safe_def, u2s_frame_def, venom_state_component_equality,
         ghost_inv_at_def, jump_to_def] >> metis_tac[]) >>
  conj_tac >- (fs[allocas_from_def, jump_to_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[ghost_inv_at_def, stor_taint_ok_at_def, u2s_safe_def,
         u2s_frame_def, venom_state_component_equality, jump_to_def]) >>
  qexistsl_tac [`G`, `fn`, `sz`, `s`, `a`, `b`, `tn`] >>
  fs[u2s_safe_def, u2s_frame_def, jump_to_def, lookup_var_def, stmt_state_rel_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  fs[state_rel_def] >> rpt strip_tac >> decide_tac
QED

Finalise u2s_zero_joint_result
