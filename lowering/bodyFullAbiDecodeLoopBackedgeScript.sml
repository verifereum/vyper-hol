Theory bodyFullAbiDecodeLoopBackedge
Ancestors
  bodyFullAbiDecodeDecoderFrame bodyFullAbiDecodeStoreContents
  bodyFullAbiDecodeOutputOwnership bodyFullAbiDecodeLoopLayout
  venomInst venomExecSemantics venomState bodyPtrDefs words list finite_map
  valueEncodingProps bodyFullAbiDecodeLeafCases bodyFullShared
  sourceArrayBackedgeOriginPtr stateFrame pred_set exprLoweringProps
  loweringStateRelDefs ptrDiscipline codegenRel decoderGhostFramePtr
  abiDecodePtrMemberFrame localPtrsProps revertReasonPrefixPtr wordLoadStorePtr
  abiDecoderFrame fragGasSeqPtr instMemFrontier decoderLoopBackedgeCorePtr
  ptrSafeRun contextCodegenRel abiDecoderExecution memSafeRun
  fragGasPathMem fragGasPathPtr gasCount fragGasOriginPtr fragGasOrigin
  exprPtrUnwrapCopyEdges instIdxIndep ghostPcTransportPtr emitHelperProps arithmetic

(* The store uses the actual counter allocation, not the output allocation.
   Its physical and ghost witnesses are fixed before selecting a horizon. *)
Theorem abi_decode_loop_counter_store_joint[local]:
  fn_inst_ids_distinct fn /\
  MEM ci (fn_insts fn) /\ ci.inst_opcode = ALLOCA /\
  ci.inst_outputs = [counter_owner] /\ ci.inst_id = aid /\
  not_local_ptr ce es.scopes counter_owner /\
  FLOOKUP s.vs_allocas aid = SOME (cell,32) /\
  cell < dimword (:256) /\ lo <= cell /\
  lookup_var counter s = SOME (n2w cell) /\ ptr_covers G tn counter s 32 /\
  eval_operand value s = SOME (n2w (SUC j)) /\ op_taint tn value = {} /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  (w2n input_word+LENGTH input_bytes <= cell \/ cell+32 <= w2n input_word) /\
  local_ptrs_rel fn ce es.scopes s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name b k. local_region ce es.scopes s name b k ==>
    cell+32 <= b \/ b+k <= cell) /\
  (!H. V H ==> ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn /\
    stmt_state_rel H ctx fn ce cx es s) /\
  EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ cell+32 <= a) snapshots /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) snapshots ==>
  ?t Gf tnf.
    t = mstore cell (n2w (SUC j)) s /\
    Gf = step_prov PG G (mk_inst id MSTORE [Var counter;value] []) t /\
    tnf = step_taint (mk_inst id MSTORE [Var counter;value] []) s t tn /\
    mem_word_at cell t.vs_memory = n2w (SUC j) /\
    EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes) snapshots /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!p. lookup_var p t = lookup_var p s) /\
    (!name b k. local_region ce es.scopes t name b k ==>
      cell+32 <= b \/ b+k <= cell) /\
    (!H. V H ==>
      abi_decode_ptr_write_frame tn s tnf t cell 32 /\
      abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes) /\
      ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf /\
      stmt_state_rel H ctx fn ce cx es t)
Proof
  strip_tac >> (
  qexistsl_tac [`mstore cell (n2w (SUC j)) s`,
    `step_prov PG G (mk_inst id MSTORE [Var counter;value] [])
      (mstore cell (n2w (SUC j)) s)`,
    `step_taint (mk_inst id MSTORE [Var counter;value] []) s
      (mstore cell (n2w (SUC j)) s) tn`] >>
  pure_rewrite_tac [REFL_CLAUSE, AND_CLAUSES] >>
  drule_all abi_decode_mstore_snapshots >>
  disch_then (qspec_then `n2w (SUC j)` strip_assume_tac) >>
  simp[abi_decode_counter_store_value] >>
  conj_tac
  >- metis_tac[abi_decode_output_ownership_mstore_frame] >>
  gen_tac >> disch_tac >>
  `ghost_inv_at (DF H) lo delta ce cx es G tn s /\
   ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn /\
   (!H. V H ==> stmt_state_rel H ctx fn ce cx es s)` by metis_tac[] >>
  `?t Gf tnf.
     t = mstore (w2n (n2w cell : 256 word)) (n2w (SUC j)) s /\
     Gf = step_prov PG G (mk_inst id MSTORE [Var counter;value] []) t /\
     tnf = step_taint (mk_inst id MSTORE [Var counter;value] []) s t tn /\
     abi_decode_ptr_write_frame tn s tnf t (w2n (n2w cell : 256 word)) 32 /\
     abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes) /\
     ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
     ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf /\
     (!H. V H ==> stmt_state_rel H ctx fn ce cx es t)` by
    (irule abi_decode_output_write_frame_joint >>
     simp[] >> conj_tac >- metis_tac[] >>
     conj_tac >- (qexists_tac `sa` >> simp[]) >>
     qexistsl_tac [`cell`, `ci`, `counter_owner`, `32`] >> simp[]) >>
  gvs[])
QED

(* The three physical steps and their ghosts are fixed before H. *)
Theorem abi_decode_loop_backedge_joint:
  fn_inst_ids_distinct fn /\
  MEM ci (fn_insts fn) /\ ci.inst_opcode = ALLOCA /\
  ci.inst_outputs = [counter_owner] /\ ci.inst_id = aid /\
  not_local_ptr ce es.scopes counter_owner /\
  FLOOKUP s.vs_allocas aid = SOME (cell,32) /\ lo <= cell /\
  lookup_var counter s = SOME (n2w cell) /\ ptr_covers G tn counter s 32 /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  op_taint tn (Var iv) = {} /\ op_prov G (Var iv) = NONE /\
  j < n /\ n < dimword (:256) /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  (w2n input_word+LENGTH input_bytes <= cell \/ cell+32 <= w2n input_word) /\
  local_ptrs_rel fn ce es.scopes s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name b k. local_region ce es.scopes s name b k ==>
    cell+32 <= b \/ b+k <= cell) /\
  (!H. V H ==> ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn /\
    stmt_state_rel H ctx fn ce cx es s) /\
  EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ cell+32 <= a) snapshots /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) snapshots /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var counter) hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~not_fresh_at sa nv /\ not_fresh_at sa counter /\ not_fresh_at sa input /\
  origin.cs_next_var <= sa.cs_next_var /\
  cell+32 < dimword (:256) /\ cell+32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t Gf tnf.
    t = jump_to hdr (mstore cell (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) /\
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    mem_word_at cell t.vs_memory = n2w (SUC j) /\
    EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes) snapshots /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gf tnf counter t 32 /\
    DISJOINT {a | cell <= a /\ a < cell+32} tnf.t_mem /\
    tnf.t_mem SUBSET tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!name b k. local_region ce es.scopes t name b k ==>
      cell+32 <= b \/ b+k <= cell) /\
    (!H. V H ==>
      abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes) /\
      ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf /\
      stmt_state_rel H ctx fn ce cx es t)
Proof
  strip_tac >> (
  qabbrev_tac `a = update_var nv (n2w (SUC j)) s` >>
  qabbrev_tac `ainst = mk_inst id ADD [Var iv; Lit 1w] [nv]` >>
  qabbrev_tac `A = step_prov PG G ainst a` >>
  qabbrev_tac `v = step_taint ainst s a tn` >>
  `cell < dimword (:256) /\ counter <> nv /\ input <> nv` by
    (conj_tac >- decide_tac >> metis_tac[]) >>
  `A = DRESTRICT G (COMPL {nv}) /\
   v.t_var = tn.t_var |+ (nv,{}) /\ v.t_mem = tn.t_mem /\
   v.t_stor = tn.t_stor /\ v.t_trans = tn.t_trans /\ v.t_imm = tn.t_imm` by
    (simp[Abbr `A`, Abbr `v`, Abbr `ainst`, Abbr `a`, step_prov_def,
      set_prov_def, out_prov_def, first_prov_def, op_prov_def,
      step_taint_def, mem_taint_def, imm_taint_def, new_site_bytes_def,
      update_var_def, set_var_taint_def, out_taint_def, step_writes_def,
      written_taint_def, source_memory_write_ranges_def, range_bytes_def,
      mk_inst_def, store_taint_def, adopt_reset_def, FLOOKUP_DEF, EXTENSION] >>
     metis_tac[]) >>
  `(!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s /\
      FLOOKUP A x = FLOOKUP G x /\ op_taint v (Var x) = op_taint tn (Var x)) /\
   state_frame a = state_frame (s with vs_inst_idx := a.vs_inst_idx)` by
    (simp[Abbr `a`, state_frame_def, update_var_def, lookup_var_def,
      FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es a /\
     ghost_inv_at (DF H) lo delta ce cx es A v a /\
     ghost_kept_at lo ce es0 origin G0 tn0 s0 A v` by
    (ho_match_mp_tac abi_decode_scalar_joint_frame >>
     metis_tac[]) >>
  `ptr_covers A v counter a 32 /\
   abi_decode_ptr_window A v a input input_word (LENGTH input_bytes)` by
    (conj_tac
     >- (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
         simp[Abbr `a`, lookup_var_def, update_var_def, FLOOKUP_DRESTRICT,
           op_taint_def, FLOOKUP_UPDATE]) >>
     irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     simp[Abbr `a`, lookup_var_def, update_var_def, FLOOKUP_DRESTRICT,
       op_taint_def, FLOOKUP_UPDATE, update_var_def]) >>
  `not_local_ptr ce es.scopes nv` by
    (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `local_ptrs_rel fn ce es.scopes a /\
   (!name b k. local_region ce es.scopes a name b k ==>
     cell+32 <= b \/ b+k <= cell)` by
    (simp[Abbr `a`, local_region_update_nonlocal] >>
     metis_tac[local_ptrs_rel_update_var, not_local_ptr_def, not_scope_ptr_def]) >>
  `?t B u.
    t = mstore cell (n2w (SUC j)) a /\
    B = step_prov PG A (mk_inst (id+1) MSTORE [Var counter;Var nv] []) t /\
    u = step_taint (mk_inst (id+1) MSTORE [Var counter;Var nv] []) a t v /\
    mem_word_at cell t.vs_memory = n2w (SUC j) /\
    EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes) snapshots /\
    t.vs_allocas = a.vs_allocas /\ t.vs_alloca_next = a.vs_alloca_next /\
    (!p. lookup_var p t = lookup_var p a) /\
    (!name b k. local_region ce es.scopes t name b k ==>
      cell+32 <= b \/ b+k <= cell) /\
    (!H. V H ==> abi_decode_ptr_write_frame v a u t cell 32 /\
      abi_decode_ptr_window B u t input input_word (LENGTH input_bytes) /\
      ghost_inv_at (DF H) lo delta ce cx es B u t /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 B u /\
      stmt_state_rel H ctx fn ce cx es t)` by
    (irule abi_decode_loop_counter_store_joint >>
     simp[Abbr `a`, update_var_def, lookup_var_def, eval_operand_def,
       FLOOKUP_UPDATE, op_taint_def] >>
     conj_tac >- metis_tac[update_var_def] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexists_tac `sa` >> simp[]) >>
     qexistsl_tac [`ci`, `counter_owner`] >> simp[]) >>
  `B = A /\ u.t_var = v.t_var /\ u.t_stor = v.t_stor /\
   u.t_trans = v.t_trans /\
   u.t_mem = v.t_mem DIFF {i | cell <= i /\ i < cell+32}` by
    (`lookup_var counter a = SOME (n2w cell) /\
      eval_operand (Var nv) a = SOME (n2w (SUC j)) /\
      op_taint v (Var nv) = {}` by
       simp[Abbr `a`, lookup_var_def, update_var_def, eval_operand_def,
         op_taint_def, FLOOKUP_UPDATE] >>
     qpat_assum `lookup_var counter a = _` mp_tac >>
     disch_then (mp_then Any mp_tac mstore_ghost_frame) >>
     disch_then (qspecl_then [`PG`, `A`, `v`, `id+1`, `Var nv`,
       `n2w (SUC j)`] mp_tac) >>
     simp[w2n_n2w]) >>
  `u.t_imm = v.t_imm` by
    simp[step_taint_def, imm_taint_def, mk_inst_def] >>
  qabbrev_tac `z = jump_to hdr t` >>
  `!x. lookup_var x z = lookup_var x t` by
    simp[Abbr `z`, jump_to_def, lookup_var_def] >>
  `!H. V H ==> abi_decode_ptr_window B u z input input_word (LENGTH input_bytes) /\
    ghost_inv_at (DF H) lo delta ce cx es B u z /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 B u /\
    stmt_state_rel H ctx fn ce cx es z` by
    (gen_tac >> disch_tac >>
     `abi_decode_ptr_window B u t input input_word (LENGTH input_bytes) /\
      ghost_inv_at (DF H) lo delta ce cx es B u t /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 B u /\
      stmt_state_rel H ctx fn ce cx es t` by metis_tac[] >>
     simp_tac std_ss [Abbr `z`, ghost_inv_at_jump, stmt_state_rel_jump_to] >>
     conj_tac
     >- (irule abi_decode_ptr_window_frame >>
         qexistsl_tac [`B`, `t`, `u`] >>
         simp_tac (srw_ss()) [jump_to_def, lookup_var_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `step_inst_base ainst s = OK a` by
    (drule_all abi_decode_loop_increment_word >> strip_tac >>
     simp[Abbr `ainst`, Abbr `a`, step_inst_base_opcode_eqs,
       exec_pure2_def, mk_inst_def, eval_operand_def]) >>
  qabbrev_tac `aa = a with vs_inst_idx := SUC (LENGTH prefix)` >>
  `!D. ptr_inst_ok D lo 0 ctx fn G tn ainst s` by
    (gen_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `ainst`, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, op_taint_def] >>
     conj_tac
     >- (gen_tac >> Cases_on `op = Var iv` >> gvs[op_taint_def] >>
         Cases_on `op = Lit 1w` >> gvs[]) >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_def, update_var_def] >> rpt strip_tac >> gvs[]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK aa,A,v)` by
    (gen_tac >>
     simp_tac bool_ss [Abbr `aa`, Abbr `A`, Abbr `v`] >>
     `SUC (LENGTH prefix) = SUC s.vs_inst_idx` by simp[] >>
     pop_assum SUBST1_TAC >>
     simp_tac bool_ss [Abbr `ainst`, mk_inst_def] >>
     irule (straight_line_origin_ptr_edge |> Q.INST
       [`i` |-> `mk_inst id ADD [Var iv; Lit 1w] [nv]`] |> SRULE [mk_inst_def]) >>
     simp[GSYM mk_inst_def, is_terminator_def, below_frontier_no_ranges] >>
     simp[get_instruction_def, abi_decode_backedge_insts_def, EL_APPEND_EQN]) >>
  qabbrev_tac `store = mk_inst (id+1) MSTORE [Var counter; Var nv] []` >>
  qabbrev_tac `tt = t with vs_inst_idx := LENGTH prefix+2` >>
  `lookup_var counter a = SOME (n2w cell) /\
   eval_operand (Var nv) a = SOME (n2w (SUC j))` by
    simp[Abbr `a`, lookup_var_update_var, eval_operand_def] >>
  `step_inst_base store a = OK t` by
    simp[Abbr `store`, step_inst_base_opcode_eqs, exec_write2_def,
      mk_inst_def, eval_operand_def, w2n_n2w] >>
  `!D. ptr_inst_ok D lo 0 ctx fn A v store aa` by
    (gen_tac >> simp_tac bool_ss [Abbr `store`] >>
     irule ptr_inst_ok_mstore_tainted >>
     simp[Abbr `aa`, Abbr `a`, allocas_from_def,
       allocas_below_fmp_def, update_var_def, ptr_covers_def,
       lookup_var_def] >>
     metis_tac[allocas_from_def, allocas_below_fmp_def, ptr_covers_def]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (aa,A,v) [] (OK tt,B,u)` by
    (gen_tac >>
     `step_inst_base store aa = OK (t with vs_inst_idx := SUC (LENGTH prefix))` by
       simp[Abbr `aa`, step_inst_inst_idx_indep, exec_result_map_def,
         Abbr `store`, mk_inst_def, is_terminator_def] >>
     qsuff_tac `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (aa,A,v) []
       (OK ((t with vs_inst_idx := SUC (LENGTH prefix)) with vs_inst_idx := SUC aa.vs_inst_idx),
        step_prov PG A store (t with vs_inst_idx := SUC (LENGTH prefix)),
        step_taint store aa (t with vs_inst_idx := SUC (LENGTH prefix)) v)`
     >- (simp_tac (srw_ss()) [Abbr `aa`, Abbr `tt`, step_prov_inst_idx,
          step_taint_inst_idx, ADD1] >>
         `LENGTH prefix + 1 + 1 = LENGTH prefix + 2` by decide_tac >>
         metis_tac[]) >>
     simp_tac bool_ss [Abbr `store`, mk_inst_def] >>
     irule (straight_line_origin_ptr_edge |> Q.INST
       [`i` |-> `mk_inst (id+1) MSTORE [Var counter; Var nv] []`] |> SRULE [mk_inst_def]) >>
     simp[GSYM mk_inst_def, is_terminator_def] >>
     simp[Abbr `aa`, Abbr `a`, update_var_def, get_instruction_def,
       abi_decode_backedge_insts_def, EL_APPEND_EQN, ADD1] >>
     simp[GSYM mk_inst_def, below_frontier_MSTORE, eval_operand_def,
       GSYM update_var_def, lookup_var_update_var, w2n_n2w] >>
     gvs[update_var_def, ADD1]) >>
  `~tt.vs_halted /\ tt.vs_current_bb = s.vs_current_bb /\
   tt.vs_inst_idx = LENGTH prefix + 2 /\ jump_to hdr tt = z` by
    simp[Abbr `tt`, Abbr `z`, Abbr `a`, mstore_def, update_var_def, jump_to_def] >>
  `gas_path_mem_edge ctx fn tt 0 (OK z)` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst (id+2) JMP [Label hdr] []` >>
     simp[get_instruction_def, EL_APPEND_EQN, abi_decode_backedge_insts_def,
       gas_count_step_def, mem_safe_step_non_invoke, step_inst_non_invoke,
       step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
       inst_dload_in_section_def] >>
     conj_tac
     >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >> qexists_tac `hdr` >> simp[]) >>
  `!D. gas_path_ptr_edge D lo ctx fn PG B u tt 0 B u (OK z)` by
    (gen_tac >> simp[gas_path_ptr_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst (id+2) JMP [Label hdr] []` >>
     simp[get_instruction_def, EL_APPEND_EQN, abi_decode_backedge_insts_def,
       gas_count_step_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       mk_inst_def, is_terminator_def] >>
     conj_tac
     >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
           op_taint_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
           jump_to_def, Abbr `tt`, Abbr `a`, update_var_def, mstore_def,
           allocas_from_def, allocas_below_fmp_def] >>
         metis_tac[allocas_from_def, allocas_below_fmp_def]) >>
     disj2_tac >> disj1_tac >> qexists_tac `hdr` >> simp[]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (tt,B,u) [] (OK z,B,u)` by
    (gen_tac >> simp[gas_origin_ptr_edge_def] >>
     metis_tac[gas_path_mem_edge_zero_origin]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z,B,u)` by
    (gen_tac >>
     `~z.vs_halted` by simp[Abbr `z`, Abbr `a`, jump_to_def, mstore_def, update_var_def] >>
     `~aa.vs_halted` by simp[Abbr `aa`, Abbr `a`, update_var_def] >>
     metis_tac[gas_origin_ptr_path_rules, APPEND]) >>
  `(!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP B x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))` by
    (`!x. op_taint u (Var x) = op_taint v (Var x)` by
       (qpat_assum `u.t_var = v.t_var`
         (fn th => simp_tac std_ss [op_taint_def, th])) >>
     metis_tac[]) >>
  `ptr_covers B u counter z 32` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >> metis_tac[]) >>
  `DISJOINT {a | cell <= a /\ a < cell+32} u.t_mem /\ u.t_mem SUBSET tn.t_mem` by
    (simp[] >> SET_TAC[]) >>
  `z.vs_memory = t.vs_memory /\ z.vs_allocas = s.vs_allocas /\
   z.vs_alloca_next = s.vs_alloca_next /\ z.vs_labels = s.vs_labels` by
    (simp_tac (srw_ss()) [Abbr `z`, jump_to_def] >>
     qpat_assum `t = mstore _ _ _` SUBST1_TAC >>
     simp_tac (srw_ss()) [mstore_def, Abbr `a`, update_var_def]) >>
  `!name b k. local_region ce es.scopes z name b k ==>
    cell+32 <= b \/ b+k <= cell` by
    (simp_tac (srw_ss()) [Abbr `z`, jump_to_def, local_region_def, lookup_var_def] >>
     metis_tac[local_region_def, lookup_var_def]) >>
  qexistsl_tac [`z`, `B`, `u`] >>
  simp_tac bool_ss [] >>
  metis_tac[markerTheory.Abbrev_def])
QED
