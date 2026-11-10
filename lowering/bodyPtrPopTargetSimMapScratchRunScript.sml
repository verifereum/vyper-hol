(* Fresh two-word scratch hashing for mapping slots. *)
Theory bodyPtrPopTargetSimMapScratchRun
Ancestors bodyPtrPopTargetSimMapKeyRun exprSimMapKey exprLowering
  exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs context
  codegenRel ASCIInumbers rich_list venomInst
  bodyPtrEnvBuiltinsSelectorSuffix bodyPtrEnvBuiltinsSelectorBuffer
  bodyPtrEnvBuiltinsEdges assignBasePtrLiteralGhost
  bodyPtrHashBuiltinsKeccakBytesRun bodyPtrHashBuiltinsKeccak
  exprSimPtrTopLevelImmutableCopy typedCopyPtr fragExecPtr fragGasSeqPtr
  venomState venomExecSemantics ptrDiscipline bodyPtrDefs words finite_map pred_set
  instIdxIndep exprSimHash localPtrsProps bodyPtrEnvBuiltinsMemoryHash
  bodyPtrEnvBuiltinsAllocation instSeqComposePtr loweringHalt
  assignTuplePtrCopyEndpoint fragExec

Theorem map_scratch_emission:
  !base key sa op sb.
    compile_mapping_subscript base key sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) MSTORE
         [Var (STRING #"%" (toString sa.cs_next_var));base] [];
       mk_inst (sa.cs_next_id+2) ADD
         [Var (STRING #"%" (toString sa.cs_next_var));Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var+1))];
       mk_inst (sa.cs_next_id+3) MSTORE
         [Var (STRING #"%" (toString (sa.cs_next_var+1)));key] [];
       mk_inst (sa.cs_next_id+4) SHA3
         [Var (STRING #"%" (toString sa.cs_next_var));Lit 64w]
         [STRING #"%" (toString (sa.cs_next_var+2))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+2)))
Proof
  rpt gen_tac >>
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    emitted_insts_def, DROP_LENGTH_APPEND, arithmeticTheory.ADD_ASSOC] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem map_scratch_shape:
  !base key sa op sb.
    compile_mapping_subscript base key sa = (op,sb) ==>
    ?ia is ip ik ih p q h.
      emitted_insts sa sb =
        [mk_inst ia ALLOCA [Lit 64w] [p];
         mk_inst is MSTORE [Var p;base] [];
         mk_inst ip ADD [Var p;Lit 32w] [q];
         mk_inst ik MSTORE [Var q;key] [];
         mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
      op = Var h /\ ALL_DISTINCT [p;q;h] /\
      (!z. not_fresh_at sa z ==> z <> p /\ z <> q /\ z <> h)
Proof
  rpt gen_tac >> strip_tac >> drule map_scratch_emission >> strip_tac >>
  qexistsl_tac [`sa.cs_next_id`, `sa.cs_next_id+1`, `sa.cs_next_id+2`,
    `sa.cs_next_id+3`, `sa.cs_next_id+4`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED

Theorem map_scratch_store_hash_checked:
  !D ctx fn PG G tn s is ip ik ih p q h base key b root cap w0 w1.
    p <> q /\ q <> h /\ p <> h /\
    (!x. key = Var x ==> x <> q) /\
    eval_operand base s = SOME w0 /\ eval_operand key s = SOME w1 /\
    op_taint tn base = {} /\ op_taint tn key = {} /\
    lookup_var p s = SOME (n2w b) /\ FLOOKUP G p = SOME (root,cap) /\
    root <= b /\ b+64 <= root+cap /\ b+64 < dimword (:256) /\
    op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst is MSTORE [Var p;base] [];
       mk_inst ip ADD [Var p;Lit 32w] [q];
       mk_inst ik MSTORE [Var q;key] [];
       mk_inst ih SHA3 [Var p;Lit 64w] [h]] s
      (DRESTRICT (G |+ (q,(root,cap))) (COMPL {h}))
      (tn with <|t_var := tn.t_var |+ (q,{}) |+ (h,{});
        t_mem := (tn.t_mem DIFF {i | b <= i /\ i < b+32})
          DIFF {i | b+32 <= i /\ i < b+64}|>)
Proof
  rpt gen_tac >> strip_tac >> rename1 `eval_operand slot s = SOME w0` >>
  `b < dimword (:256) /\ b+32 < dimword (:256)` by decide_tac >>
  qabbrev_tac `s1 = mstore b w0 s` >>
  qabbrev_tac `tn1 = tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  `step_inst_base (mk_inst is MSTORE [Var p;slot] []) s = OK s1` by
    simp[Abbr `s1`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, eval_operand_def] >>
  `step_prov PG G (mk_inst is MSTORE [Var p;slot] []) s1 = G /\
   step_taint (mk_inst is MSTORE [Var p;slot] []) s s1 tn = tn1` by
    (simp[Abbr `s1`, Abbr `tn1`] >>
     qpat_assum `eval_operand slot s = SOME w0`
       (mp_then Any mp_tac toplevel_immutable_mstore_ghost_frame) >>
     disch_then drule >>
     disch_then (qspecl_then [`tn`, `is`, `PG`, `G`] mp_tac) >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore >> simp[] >>
    simp[ptr_covers_def] >> qexists_tac `n2w b` >> simp[] >> decide_tac) >>
  simp[] >> suspend "add"
QED

Resume map_scratch_store_hash_checked[add]:
  qabbrev_tac `s2 = update_var q (n2w (b+32)) s1` >>
  qabbrev_tac `G2 = G |+ (q,(root,cap))` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (q,{})` >>
  `eval_operand (Var p) s1 = SOME (n2w b)` by
    simp[Abbr `s1`, eval_operand_def, mstore_def, lookup_var_def] >>
  `step_inst_base (mk_inst ip ADD [Var p;Lit 32w] [q]) s1 = OK s2` by
    simp[Abbr `s2`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, eval_operand_def, word_add_n2w] >>
  `step_prov PG G (mk_inst ip ADD [Var p;Lit 32w] [q]) s2 = G2 /\
   step_taint (mk_inst ip ADD [Var p;Lit 32w] [q]) s1 s2 tn1 = tn2` by
    (simp[Abbr `s2`, Abbr `G2`, Abbr `tn2`] >>
     metis_tac[hash_add_ghost]) >>
  `~is_terminator MSTORE /\ ~is_terminator ADD` by simp[is_terminator_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> gvs[Abbr `tn1`, op_taint_def]) >>
  simp[] >> suspend "store"
QED

Resume map_scratch_store_hash_checked[store]:
  `lookup_var q s2 = SOME (n2w (b+32)) /\
   eval_operand key s2 = SOME w1 /\ op_taint tn2 key = {} /\
   FLOOKUP G2 q = SOME (root,cap) /\ op_taint tn2 (Var q) = {}` by
    (Cases_on `key` >>
     gvs[Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `tn2`, Abbr `tn1`,
       eval_operand_def, lookup_var_def, update_var_def, mstore_def,
       op_taint_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `s3 = mstore (b+32) w1 s2` >>
  qabbrev_tac `tn3 = tn2 with t_mem := tn2.t_mem DIFF {i | b+32 <= i /\ i < b+64}` >>
  `step_inst_base (mk_inst ik MSTORE [Var q;key] []) s2 = OK s3` by
    simp[Abbr `s3`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, eval_operand_def] >>
  `step_prov PG G2 (mk_inst ik MSTORE [Var q;key] []) s3 = G2 /\
   step_taint (mk_inst ik MSTORE [Var q;key] []) s2 s3 tn2 = tn3` by
    (simp[Abbr `s3`, Abbr `tn3`] >>
     drule_all toplevel_immutable_mstore_ghost_frame >> simp[]) >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore >> simp[] >>
    simp[ptr_covers_def] >> qexists_tac `n2w (b+32)` >> simp[] >> decide_tac) >>
  simp[] >> suspend "hash"
QED

Resume map_scratch_store_hash_checked[hash]:
  `eval_operand (Var p) s3 = SOME (n2w b) /\
   FLOOKUP G2 p = SOME (root,cap) /\ op_taint tn3 (Var p) = {}` by
    (simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `tn3`, Abbr `tn2`,
       Abbr `tn1`, eval_operand_def, lookup_var_def, update_var_def,
       mstore_def, op_taint_def, FLOOKUP_UPDATE] >>
     gvs[op_taint_def, lookup_var_def]) >>
  `!i. b <= i /\ i < b+64 ==> i NOTIN tn3.t_mem` by
    (simp[Abbr `tn3`, Abbr `tn2`, Abbr `tn1`] >> rpt strip_tac >> decide_tac) >>
  `step_inst_base (mk_inst ih SHA3 [Var p;Lit 64w] [h]) s3 =
    OK (update_var h (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (mem_bytes_at b 64 s3.vs_memory))) s3)` by
    (irule step_SHA3_bytes >> simp[eval_operand_def, dimword_def]) >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  conj_tac >- (irule hash_sha3_inst_ok >> simp[eval_operand_def, op_taint_def] >>
    qexists_tac `n2w b` >> gvs[eval_operand_def, lookup_var_def]) >>
  `~is_terminator (mk_inst ih SHA3 [Var p;Lit 64w] [h]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
    hash_sha3_ghost, Abbr `G2`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`]
QED

Finalise map_scratch_store_hash_checked

Theorem map_scratch_stores_ghost_inv:
  local_ptrs_rel fn cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa q /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name lb sz. local_region cenv es.scopes s name lb sz ==>
     lb+sz <= b \/ b+64 <= lb) /\
  lookup_var p s = SOME (n2w b) /\ p <> q /\
  FLOOKUP G p = SOME (root,cap) /\ op_taint tn (Var p) = {} ==>
  ghost_inv d cenv cx es (G |+ (q,(root,cap)))
    (tn with <|t_var := tn.t_var |+ (q,{});
      t_mem := (tn.t_mem DIFF {i | b <= i /\ i < b+32})
        DIFF {i | b+32 <= i /\ i < b+64}|>)
    (mstore (b+32) w1 (update_var q (n2w (b+32)) (mstore b w0 s)))
Proof
  strip_tac >>
  qabbrev_tac `s1 = mstore b w0 s` >>
  qabbrev_tac `tn1 = tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  qabbrev_tac `s2 = update_var q (n2w (b+32)) s1` >>
  qabbrev_tac `G2 = G |+ (q,(root,cap))` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (q,{})` >>
  `ghost_inv d cenv cx es G tn1 s1` by
    (simp[Abbr `s1`] >> irule ghost_inv_mstore_clean >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
     conj_tac >- metis_tac[] >> qexists_tac `tn` >> simp[Abbr `tn1`]) >>
  `ghost_inv d cenv cx es G2 tn2 s2` by suspend "add_inv" >>
  `local_ptrs_rel fn cenv es.scopes s2` by suspend "locals" >>
  `!name lb sz. local_region cenv es.scopes s2 name lb sz ==>
     lb+sz <= b+32 \/ b+64 <= lb` by suspend "separation" >>
  `ghost_inv d cenv cx es G2
    (tn2 with t_mem := tn2.t_mem DIFF {i | b+32 <= i /\ i < b+64})
    (mstore (b+32) w1 s2)` suffices_by
    simp[Abbr `G2`, Abbr `tn2`, Abbr `tn1`, Abbr `s2`, Abbr `s1`] >>
  irule ghost_inv_mstore_clean >> simp[] >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED

Resume map_scratch_stores_ghost_inv[add_inv]:
  `step_prov PG G (mk_inst 0 ADD [Var p;Lit 32w] [q]) s2 = G2 /\
   step_taint (mk_inst 0 ADD [Var p;Lit 32w] [q]) s1 s2 tn1 = tn2` by
    (simp[Abbr `s2`, Abbr `G2`, Abbr `tn2`] >>
     simp[hash_add_ghost]) >>
  qpat_x_assum `step_prov _ _ _ _ = G2` (rewrite_tac o single o GSYM) >>
  qpat_x_assum `step_taint _ _ _ _ = tn2` (rewrite_tac o single o GSYM) >>
  irule single_output_ghost_inv >>
  simp[Abbr `s2`, update_var_def, copy_len_binop_ghost_frame] >>
  qexists_tac `sa` >> simp[] >>
  rpt strip_tac >> `x <> q` by metis_tac[] >> simp[lookup_var_def, FLOOKUP_UPDATE]
QED

Resume map_scratch_stores_ghost_inv[locals]:
  `not_local_ptr cenv es.scopes q` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  simp[Abbr `s2`] >> irule local_ptrs_rel_update_var >>
  simp[not_local_ptr_scope] >>
  simp[Abbr `s1`] >> irule local_ptrs_rel_mstore >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Resume map_scratch_stores_ghost_inv[separation]:
  rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s name lb sz` by
    (qpat_x_assum `local_region _ _ s2 _ _ _` mp_tac >>
     simp[local_region_def, Abbr `s2`, Abbr `s1`,
       update_var_def, lookup_var_def, mstore_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> `p' <> q` by
       (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `!name lb sz. local_region _ _ s _ _ _ ==> _` drule >> decide_tac
QED

Finalise map_scratch_stores_ghost_inv

Theorem map_scratch_tail_certificate:
  ALL_DISTINCT [p;q;h] /\ (!x. key = Var x ==> x <> q) /\
  eval_operand slot s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn slot = {} /\ op_taint tn key = {} /\
  lookup_var p s = SOME (n2w b) /\ FLOOKUP G p = SOME (root,cap) /\
  root <= b /\ b+64 <= root+cap /\ b+64 < dimword (:256) /\
  op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx /\
  local_ptrs_rel fn cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa q /\ ~not_fresh_at sa h /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name lb sz. local_region cenv es.scopes s name lb sz ==>
     lb+sz <= b \/ b+64 <= lb) /\
  run_inst_seq [mk_inst is MSTORE [Var p;slot] [];
    mk_inst ip ADD [Var p;Lit 32w] [q]; mk_inst ik MSTORE [Var q;key] [];
    mk_inst ih SHA3 [Var p;Lit 64w] [h]] s = OK t ==>
  ?G' tn'. (!k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst is MSTORE [Var p;slot] []; mk_inst ip ADD [Var p;Lit 32w] [q];
     mk_inst ik MSTORE [Var q;key] []; mk_inst ih SHA3 [Var p;Lit 64w] [h]]
      (s with vs_inst_idx := k) G' tn') /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn' /\
    tn'.t_mem SUBSET tn.t_mem /\ op_taint tn' (Var h) = {} /\ op_prov G' (Var h) = NONE /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> gvs[] >>
  qabbrev_tac `u = mstore b w0 s` >>
  qabbrev_tac `v = update_var q (n2w (b+32)) u` >>
  qabbrev_tac `z = mstore (b+32) w1 v` >>
  qabbrev_tac `G2 = G |+ (q,(root,cap))` >>
  qabbrev_tac `tn2 = tn with <|t_var := tn.t_var |+ (q,{});
    t_mem := (tn.t_mem DIFF {i | b <= i /\ i < b+32})
      DIFF {i | b+32 <= i /\ i < b+64}|>` >>
  `t = update_var h (word_of_bytes T (0w:bytes32)
     (Keccak_256_w64 (mem_bytes_at b 64 z.vs_memory))) z` by suspend "endpoint" >>
  `ghost_inv d cenv cx es G2 tn2 z` by
    (simp[Abbr `z`, Abbr `v`, Abbr `u`, Abbr `G2`, Abbr `tn2`] >>
     irule (SRULE [] map_scratch_stores_ghost_inv) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`DRESTRICT G2 (COMPL {h})`, `tn2 with t_var := tn2.t_var |+ (h,{})`] >>
  conj_tac >- (gen_tac >> simp[Abbr `G2`, Abbr `tn2`] >>
    qpat_assum `q <> h` (fn th => irule (SRULE [th] map_scratch_store_hash_checked)) >>
    simp[lookup_var_def, eval_operand_def] >> metis_tac[lookup_var_def, eval_operand_def]) >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "kept" >>
  simp[op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    Abbr `G2`, Abbr `tn2`, SUBSET_DEF] >>
  rpt strip_tac >> `x <> q /\ x <> h` by metis_tac[] >> simp[]
QED

Resume map_scratch_tail_certificate[endpoint]:
  `b < dimword (:256) /\ b+32 < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst is MSTORE [Var p;slot] []) s = OK u` by
    simp[Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, eval_operand_def] >>
  `lookup_var p u = SOME (n2w b)` by
    simp[Abbr `u`, lookup_var_def, mstore_def] >>
  `step_inst_base (mk_inst ip ADD [Var p;Lit 32w] [q]) u = OK v` by
    simp[Abbr `v`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, eval_operand_def, word_add_n2w] >>
  `lookup_var q v = SOME (n2w (b+32)) /\ eval_operand key v = SOME w1 /\
   lookup_var p z = SOME (n2w b)` by
    (Cases_on `key` >>
     gvs[Abbr `v`, Abbr `u`, Abbr `z`, lookup_var_def, update_var_def,
       mstore_def, FLOOKUP_UPDATE, eval_operand_def]) >>
  `step_inst_base (mk_inst ik MSTORE [Var q;key] []) v = OK z` by
    simp[Abbr `z`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, eval_operand_def] >>
  `step_inst_base (mk_inst ih SHA3 [Var p;Lit 64w] [h]) z =
    OK (update_var h (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (mem_bytes_at b 64 z.vs_memory))) z)` by
    (irule step_SHA3_bytes >> simp[eval_operand_def, dimword_def]) >>
  gvs[run_inst_seq_def]
QED

Resume map_scratch_tail_certificate[ghost]:
  simp[] >> irule (SRULE [hash_sha3_ghost] (cj 1 hash_update_ghosts)) >>
  simp[] >> irule_at Any ghost_kept_refl >> qexists_tac `sa` >> simp[]
QED

Resume map_scratch_tail_certificate[kept]:
  irule ghost_kept_clean_suffix >> qexistsl_tac [`G`, `tn`] >>
  simp[ghost_kept_refl, Abbr `G2`, Abbr `tn2`, op_taint_def, FLOOKUP_UPDATE,
    FLOOKUP_DRESTRICT, SUBSET_DEF] >>
  rpt strip_tac >> `x <> q /\ x <> h` by metis_tac[] >> simp[]
QED

Finalise map_scratch_tail_certificate


Theorem map_scratch_prefix_certificate:
  code = [mk_inst ia ALLOCA [Lit 64w] [p];
          mk_inst is MSTORE [Var p;slot] [];
          mk_inst ip ADD [Var p;Lit 32w] [q];
          mk_inst ik MSTORE [Var q;key] [];
          mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
  ALL_DISTINCT [p;q;h] /\ (!x. slot = Var x ==> x <> p) /\
  (!x. key = Var x ==> x <> p /\ x <> q) /\
  eval_operand slot s = SOME w0 /\ eval_operand key s = SOME w1 /\
  op_taint tn slot = {} /\ op_taint tn key = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\ MEM (mk_inst ia ALLOCA [Lit 64w] [p]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa p /\ ~not_fresh_at sa q /\ ~not_fresh_at sa h /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  run_inst_seq code s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn' /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sa G tn s G' tn' /\
    op_taint tn' (Var h) = {} /\ op_prov G' (Var h) = NONE /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base (mk_inst ia ALLOCA [Lit 64w] [p]) s` >>
  simp[] >> strip_tac >> rename1 `step_inst_base _ s = OK s1` >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all builtin_allocation_certificate >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `local_ptrs_rel fn cenv es.scopes s1` by fs[stmt_state_rel_def, state_rel_def] >>
  `eval_operand slot s1 = SOME w0 /\ eval_operand key s1 = SOME w1 /\
   op_taint tn1 slot = {} /\ op_taint tn1 key = {} /\
   (!x. not_fresh_at sa x ==> FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))` by suspend "allocation_frame" >>
  `?root cap. FLOOKUP G1 p = SOME (root,cap) /\ root <= b /\
    b+64 <= root+cap /\ lookup_var p s1 = SOME (n2w b) /\
    op_taint tn1 (Var p) = {}` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `ALL_DISTINCT [p;q;h] /\ (!x. key = Var x ==> x <> q)` by
    (simp[] >> metis_tac[]) >>
  drule_all map_scratch_tail_certificate >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  conj_tac >- suspend "checks" >>
  irule ghost_kept_clean_suffix >> qexistsl_tac [`G1`, `tn1`] >> simp[]
QED

Resume map_scratch_prefix_certificate[allocation_frame]:
  drule_all alloca_step_frame_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  qspecl_then [`ia`, `64w`, `p`, `s`] strip_assume_tac step_alloca_frame >>
  gvs[] >> Cases_on `slot` >> Cases_on `key` >>
  gvs[eval_operand_def, op_taint_def] >> rpt strip_tac >>
  `x <> p` by metis_tac[] >> metis_tac[op_taint_def]
QED

Resume map_scratch_prefix_certificate[checks]:
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _`
    (strip_assume_tac o SRULE [inst_seq_ptr_def]) >>
  PURE_ONCE_REWRITE_TAC[inst_seq_ptr_def] >> gvs[]
QED

Finalise map_scratch_prefix_certificate

Theorem map_scratch_ptr_frame:
  compile_mapping_subscript base_op key sa = (op,sb) /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME w0 /\ eval_operand key s = SOME w1 /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  op_taint tn base_op = {} /\ op_taint tn key = {} /\
  ghost_inv d cenv cx es G tn s /\ ~ctx_has_dalloca ctx /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (hashmap_slot w0 w1) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_inv d cenv cx es G' tn'
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es sa G tn s G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all compile_mapping_subscript_frame >> strip_tac >>
  drule map_scratch_shape >> strip_tac >>
  `MEM (mk_inst ia ALLOCA [Lit 64w] [p]) (fn_insts func)` by
    suspend "site" >>
  `~not_fresh_at sa p /\ ~not_fresh_at sa q /\ ~not_fresh_at sa h /\
   (!x. base_op = Var x ==> x <> p) /\
   (!x. key = Var x ==> x <> p /\ x <> q)` by metis_tac[] >>
  `?G' tn'. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sa G tn s G' tn' /\
    op_taint tn' (Var h) = {} /\ op_prov G' (Var h) = NONE /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))` by
    (drule_all map_scratch_prefix_certificate >>
     disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> metis_tac[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[ghost_inv_inst_idx] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Resume map_scratch_ptr_frame[site]:
  drule lookup_block_fn_insts >>
  disch_then irule >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  irule MEM_DROP_IMP >> qexists_tac `s.vs_inst_idx` >> simp[]
QED

Finalise map_scratch_ptr_frame
