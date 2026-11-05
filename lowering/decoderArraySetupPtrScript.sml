(* Pointer ghosts for the complete array-element address setup. *)
Theory decoderArraySetupPtr
Ancestors decoderNavigationPtr abiDecoderLoopSetup abiDecoderIndexedAddress
  abiDecoderDynamic abiEncoder compileEnv emitHelper emitHelperProps fragExecPtr
  fragExec words venomState venomExecSemantics ptrDiscipline bodyPtrDefs
  finite_map pred_set arithmetic list instIdxIndep calldataDynOwned venomInst
  exprLoweringProps codegenRel abiDecoderReentry

Theorem run_inst_seq_append_ok:
  run_inst_seq (xs ++ ys) s = OK t ==>
  ?m. run_inst_seq xs s = OK m /\ run_inst_seq ys m = OK t
Proof
  strip_tac >>
  `?m. run_inst_seq xs s = OK m` by
    (spose_not_then assume_tac >>
     qspecl_then [`xs`,`ys`,`s`] mp_tac run_inst_seq_append_err >> gvs[]) >>
  qexists_tac `m` >> simp[] >>
  drule run_inst_seq_append >> disch_then (qspec_then `ys` mp_tac) >> simp[]
QED

Theorem run_inst_seq_append_aligned:
  run_inst_seq (xs ++ ys) s = OK t /\
  EVERY (\i. ~is_terminator i.inst_opcode) ys ==>
  ?m. run_inst_seq xs s = OK m /\ run_inst_seq ys m = OK t /\
    run_inst_seq ys (m with vs_inst_idx := LENGTH xs + s.vs_inst_idx) =
      OK (t with vs_inst_idx := LENGTH xs + s.vs_inst_idx)
Proof
  strip_tac >> drule run_inst_seq_append_ok >> strip_tac >>
  qexists_tac `m` >> simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem old_operand_ghost_frame:
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
  t.vs_labels = s.vs_labels /\ (!x. op = Var x ==> not_fresh_at st x) ==>
  eval_operand op t = eval_operand op s /\
  op_taint u op = op_taint tn op /\ op_prov H op = op_prov G op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_taint_def, op_prov_def] >>
  metis_tac[]
QED

Theorem emit_op_run_labels:
  emit_op opc ops st = (out,ready) /\
  (opc = ADD \/ opc = MUL \/ opc = MLOAD \/ opc = CALLDATALOAD) /\
  run_inst_seq (emitted_insts st ready) s = OK t ==>
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_read1_def] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def]
QED

Theorem scaled_address_prefix_structure:
  !base idx stride st data c1 off c2 out ready.
  emit_op ADD [base; Lit 32w] st = (data,c1) /\
  emit_op MUL [idx; Lit (n2w stride)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (out,ready) ==>
  inst_extends st ready /\ same_blocks st ready /\
  st.cs_next_var <= ready.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready) /\
  LENGTH (emitted_insts st ready) = 3
Proof
  rpt gen_tac >> strip_tac >>
  `inst_extends st c1 /\ inst_extends c1 c2 /\ inst_extends c2 ready` by
    metis_tac[inst_extends_emit_op] >>
  `same_blocks st c1 /\ same_blocks c1 c2 /\ same_blocks c2 ready` by
    metis_tac[emit_op_same_blocks] >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= ready.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `emitted_insts st ready = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 ready` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  conj_tac >- metis_tac[inst_extends_trans] >>
  conj_tac >- fs[same_blocks_def] >>
  conj_tac >- decide_tac >>
  imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]
QED

Theorem indexed_destination_structure:
  !base idx stride st out ready.
  abi_decode_indexed_address base idx stride st = (out,ready) ==>
  inst_extends st ready /\ same_blocks st ready /\
  st.cs_next_var <= ready.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready) /\
  LENGTH (emitted_insts st ready) = 3
Proof
  rpt gen_tac >> simp[abi_decode_indexed_address_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[scaled_address_prefix_structure]
QED

Theorem calldata_dynamic_element_source_structure:
  compile_abi_decode_dyn_elem_ptr CALLDATALOAD head data (Lit 0w) abi_sz st = (out,ready) ==>
  inst_extends st ready /\ same_blocks st ready /\
  st.cs_next_var <= ready.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready) /\
  LENGTH (emitted_insts st ready) = 2
Proof
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [head] st = (off,mid)` >>
  rename1 `emit_op ADD [data;off] mid = (out,ready)` >>
  `inst_extends st mid /\ inst_extends mid ready` by metis_tac[inst_extends_emit_op] >>
  `same_blocks st mid /\ same_blocks mid ready` by metis_tac[emit_op_same_blocks] >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= ready.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `emitted_insts st ready = emitted_insts st mid ++ emitted_insts mid ready` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append]) >>
  conj_tac >- metis_tac[inst_extends_trans] >>
  conj_tac >- fs[same_blocks_def] >>
  conj_tac >- decide_tac >>
  imp_res_tac emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]
QED

Theorem indexed_destination_endpoint_ptr:
  !st out ready root idx stride s t d j total G tn cx ctx PG R.
    abi_decode_indexed_address (Var root) idx stride st = (out,ready) /\
    lookup_var root s = SOME (n2w d) /\ ptr_covers G tn root s total /\
    eval_operand idx s = SOME (n2w j) /\
    not_fresh_at st root /\ (!x. idx = Var x ==> not_fresh_at st x) /\
    op_taint tn idx = {} /\ op_prov G idx = NONE /\
    32 + j * stride + stride <= total /\
    d + 32 + j * stride < dimword (:256) /\ stride < dimword (:256) /\
    run_inst_seq (emitted_insts st ready) s = OK t ==>
    ?H u child. out = Var child /\
      ptr_covers H u child (t with vs_inst_idx := 3 + s.vs_inst_idx) stride /\
      frag_exec_ptr cx ctx PG st ready
        (\g z v. g = G /\ z = tn /\ v = s)
        (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := 3 + s.vs_inst_idx)) R /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >>
  simp[abi_decode_indexed_address_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD [Var root; Lit 32w] st = (data_op,c1)` >>
  rename1 `emit_op MUL [idx; Lit (n2w stride)] c1 = (offset_op,c2)` >>
  `inst_extends st c1 /\ inst_extends c1 c2 /\ inst_extends c2 ready` by
    metis_tac[inst_extends_emit_op] >>
  `emitted_insts st ready = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 ready` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  fs[] >> drule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 ready) s2 = OK t` >>
  qpat_x_assum `run_inst_seq (_ ++ _) s = OK s2` (strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\
   op_taint tn (Lit 32w) = {} /\ op_prov G (Lit 32w) = NONE /\
   32 + (j * stride + stride) <= total' /\ w2n (n2w d : 256 word) + 32 < dimword (:256)` by
    (simp[eval_operand_def, op_taint_def, op_prov_def, w2n_n2w] >> decide_tac) >>
  drule_all emit_ptr_offset_endpoint_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  rename1 `frag_exec_ptr cx ctx PG st c1 _ (\g z v. g = H1 /\ z = u1 /\ v = _) R` >>
  gvs[] >>
  `d < dimword (:256)` by decide_tac >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!x. not_fresh_at st x ==> not_fresh_at c1 x /\ not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `emit_op ADD [Var root; Lit 32w] st = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def, update_var_def]) >>
  `eval_operand idx s1 = SOME (n2w j) /\ op_taint u1 idx = {} /\ op_prov H1 idx = NONE` by
    (Cases_on `idx` >> gvs[eval_operand_def, op_taint_def, op_prov_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w stride)) s1 = SOME (n2w stride) /\
   op_taint u1 (Lit (n2w stride)) = {} /\ op_prov H1 (Lit (n2w stride)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  qabbrev_tac `ss1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `run_inst_seq (emitted_insts c1 c2) ss1 = OK (s2 with vs_inst_idx := ss1.vs_inst_idx)` by
    (qpat_assum `emit_op MUL _ c1 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s1`,`SUC s.vs_inst_idx`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def, Abbr `ss1`]) >>
  `eval_operand idx ss1 = SOME (n2w j) /\
   eval_operand (Lit (n2w stride)) ss1 = SOME (n2w stride)` by simp[Abbr `ss1`] >>
  drule_all (SRULE [] (Q.SPEC `MUL` emit_scalar_binop_endpoint_ptr)) >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  rename1 `op_prov H2 offset_op = NONE` >> rename1 `op_taint u2 offset_op = {}` >>
  fs[Abbr `ss1`, cj 4 moduleLoweringPropsTheory.control_moves_keep_vars] >>
  `not_fresh_at c1 q` by
    (qpat_assum `emit_op ADD [Var root; Lit 32w] st = _`
      (mp_then Any mp_tac abi_decoder_operand_live_emit) >>
     simp[calldata_operand_live_not_fresh]) >>
  `ptr_covers H2 u2 q s2 (stride + j * stride)` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `lookup_var q s2 = SOME (n2w (d + 32))` by metis_tac[] >>
  `eval_operand offset_op s2 = SOME (n2w (j * stride))` by
    (qpat_assum `emit_op MUL _ c1 = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, GSYM word_mul_n2w]) >>
  qabbrev_tac `ss2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `run_inst_seq (emitted_insts c2 ready) ss2 = OK (t with vs_inst_idx := ss2.vs_inst_idx)` by
    (qpat_assum `emit_op ADD _ c2 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s2`,`SUC (SUC s.vs_inst_idx)`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def, Abbr `ss2`]) >>
  `lookup_var q ss2 = SOME (n2w (d + 32)) /\
   ptr_covers H2 u2 q ss2 (stride + j * stride) /\
   eval_operand offset_op ss2 = SOME (n2w (j * stride)) /\
   j * stride + stride <= stride + j * stride /\
   w2n (n2w (d + 32) : 256 word) + j * stride < dimword (:256)` by
    (simp[Abbr `ss2`, w2n_n2w,
       cj 4 moduleLoweringPropsTheory.control_moves_keep_vars] >> decide_tac) >>
  drule_all emit_ptr_offset_endpoint_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  fs[Abbr `ss2`, ADD1] >>
  `same_blocks st c1 /\ same_blocks c1 c2 /\ same_blocks c2 ready` by
    metis_tac[emit_op_same_blocks] >>
  `cs_extends st c1 /\ cs_extends c1 c2 /\ cs_extends c2 ready` by
    (rpt conj_tac >> irule cs_extends_same_block >>
     fs[inst_extends_def, same_blocks_def]) >>
  qexistsl_tac [`H`,`u`] >> simp[ADD_COMM] >>
  conj_tac >-
    (irule frag_exec_ptr_seq >>
     qexistsl_tac [`(\g z v. g = H1 /\ z = u1 /\ v = s1 with vs_inst_idx := s.vs_inst_idx + 1)`, `c1`] >>
     simp[] >> (conj_tac >- metis_tac[cs_extends_trans]) >>
     irule frag_exec_ptr_seq >>
     qexistsl_tac [`(\g z v. g = H2 /\ z = u2 /\ v = s2 with vs_inst_idx := s.vs_inst_idx + 2)`, `c2`] >>
     simp[]) >>
  rpt strip_tac >>
  fs[cj 4 moduleLoweringPropsTheory.control_moves_keep_vars] >> metis_tac[]
QED

Theorem calldata_dynamic_element_source_endpoint_ptr:
  !head data abi_sz st out ready s a b tn G t cx ctx PG R.
  compile_abi_decode_dyn_elem_ptr CALLDATALOAD head data (Lit 0w) abi_sz st = (out,ready) /\
  eval_operand head s = SOME a /\ eval_operand data s = SOME b /\
  (!x. head = Var x ==> not_fresh_at st x) /\
  (!x. data = Var x ==> not_fresh_at st x) /\
  op_taint tn head = {} /\ op_prov G head = NONE /\
  op_taint tn data = {} /\ op_prov G data = NONE /\
  run_inst_seq (emitted_insts st ready) s = OK t ==>
  ?H u. (?v. eval_operand out t = SOME v) /\
    (!x. out = Var x ==> not_fresh_at ready x) /\
    t.vs_labels = s.vs_labels /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    frag_exec_ptr cx ctx PG st ready
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = t with vs_inst_idx := LENGTH (emitted_insts st ready) + s.vs_inst_idx) R /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [head] st = (off,mid)` >>
  rename1 `emit_op ADD [data;off] mid = (out,ready)` >>
  `inst_extends st mid /\ inst_extends mid ready` by
    metis_tac[inst_extends_emit_op] >>
  `emitted_insts st ready = emitted_insts st mid ++ emitted_insts mid ready` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append]) >>
  fs[] >> drule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK m` >>
  drule_all emit_calldata_load_endpoint_ptr >>
  disch_then (qspecl_then [`G`,`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  rename1 `op_taint u1 off = {}` >> rename1 `op_prov H1 off = NONE` >>
  `m.vs_labels = s.vs_labels` by
    (irule emit_op_run_labels >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `eval_operand data m = SOME b /\ op_taint u1 data = {} /\ op_prov H1 data = NONE` by
    (drule_all old_operand_ghost_frame >> simp[]) >>
  `?c. eval_operand off m = SOME c` by
    (qpat_assum `emit_op CALLDATALOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read1_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `sm = m with vs_inst_idx := SUC s.vs_inst_idx` >>
  `run_inst_seq (emitted_insts mid ready) sm = OK (t with vs_inst_idx := sm.vs_inst_idx)` by
    (qpat_assum `emit_op ADD _ mid = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`m`,`SUC s.vs_inst_idx`] mp_tac) >>
     simp[Abbr `sm`, is_terminator_def, exec_result_map_def]) >>
  `eval_operand data sm = SOME b /\ eval_operand off sm = SOME c` by simp[Abbr `sm`] >>
  drule_all emit_scalar_add_endpoint_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  `LENGTH (emitted_insts st mid) = 1 /\ LENGTH (emitted_insts mid ready) = 1` by
    metis_tac[emit_op_length] >>
  `same_blocks st mid /\ same_blocks mid ready` by metis_tac[emit_op_same_blocks] >>
  `cs_extends st mid /\ cs_extends mid ready` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  `st.cs_next_var <= mid.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  fs[Abbr `sm`, ADD1, cj 4 moduleLoweringPropsTheory.control_moves_keep_vars] >>
  `t.vs_labels = m.vs_labels` by
    (irule emit_op_run_labels >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!x. out = Var x ==> not_fresh_at ready x` by
    (qpat_assum `emit_op ADD _ mid = _`
       (mp_then Any mp_tac abi_decoder_operand_live_emit) >>
     Cases_on `out` >> simp[calldata_operand_live_not_fresh]) >>
  `?v. eval_operand out t = SOME v` by
    (qpat_assum `emit_op ADD _ mid = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`H`,`u`] >> simp[] >>
  irule frag_exec_ptr_seq >>
  qexistsl_tac [`(\g z v. g = H1 /\ z = u1 /\ v = m with vs_inst_idx := s.vs_inst_idx + 1)`,`mid`] >>
  simp[]
QED

Theorem clean_scaled_source_prefix_endpoint_ptr:
  !src st data c1 idx stride off c2 head ready s a b tn G t cx ctx PG R.
  emit_op ADD [src; Lit 32w] st = (data,c1) /\
  emit_op MUL [idx; Lit (n2w stride)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (head,ready) /\
  eval_operand src s = SOME a /\ eval_operand idx s = SOME b /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  (!x. idx = Var x ==> not_fresh_at st x) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  op_taint tn idx = {} /\ op_prov G idx = NONE /\
  run_inst_seq (emitted_insts st ready) s = OK t ==>
  ?H u. eval_operand data t = SOME (a + 32w) /\
    eval_operand head t = SOME (a + 32w + b * n2w stride) /\
    t.vs_labels = s.vs_labels /\
    op_taint u head = {} /\ op_prov H head = NONE /\
    op_taint u data = {} /\ op_prov H data = NONE /\
    (!x. data = Var x ==> not_fresh_at ready x) /\
    (!x. head = Var x ==> not_fresh_at ready x) /\
    frag_exec_ptr cx ctx PG st ready
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = t with vs_inst_idx := LENGTH (emitted_insts st ready) + s.vs_inst_idx) R /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `inst_extends st c1 /\ inst_extends c1 c2 /\ inst_extends c2 ready` by
    metis_tac[inst_extends_emit_op] >>
  `emitted_insts st ready = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 ready` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  fs[] >> drule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 ready) s2 = OK t` >>
  qpat_x_assum `run_inst_seq (_ ++ _) s = OK s2`
    (strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit 32w) s = SOME 32w /\
   op_taint tn (Lit 32w) = {} /\ op_prov G (Lit 32w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all emit_scalar_add_endpoint_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  rename1 `op_taint u1 data = {}` >> rename1 `op_prov H1 data = NONE` >>
  `s1.vs_labels = s.vs_labels` by
    (irule emit_op_run_labels >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `eval_operand idx s1 = SOME b /\ op_taint u1 idx = {} /\ op_prov H1 idx = NONE` by
    (drule_all old_operand_ghost_frame >> simp[]) >>
  `eval_operand (Lit (n2w stride)) s1 = SOME (n2w stride) /\
   op_taint u1 (Lit (n2w stride)) = {} /\ op_prov H1 (Lit (n2w stride)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  qabbrev_tac `ss1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `run_inst_seq (emitted_insts c1 c2) ss1 = OK (s2 with vs_inst_idx := ss1.vs_inst_idx)` by
    (qpat_assum `emit_op MUL _ c1 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s1`,`SUC s.vs_inst_idx`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def, Abbr `ss1`]) >>
  `eval_operand idx ss1 = SOME b /\
   eval_operand (Lit (n2w stride)) ss1 = SOME (n2w stride)` by simp[Abbr `ss1`] >>
  drule_all (SRULE [] (Q.SPEC `MUL` emit_scalar_binop_endpoint_ptr)) >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  rename1 `op_taint u2 off = {}` >> rename1 `op_prov H2 off = NONE` >>
  fs[Abbr `ss1`, cj 4 moduleLoweringPropsTheory.control_moves_keep_vars] >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= ready.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!x. data = Var x ==> not_fresh_at c1 x` by
    (qpat_assum `emit_op ADD [src; Lit 32w] st = _`
      (mp_then Any mp_tac abi_decoder_operand_live_emit) >>
     Cases_on `data` >> simp[calldata_operand_live_not_fresh]) >>
  `!x. data = Var x ==> not_fresh_at c2 x /\ not_fresh_at ready x` by
    (rpt strip_tac >>
     `not_fresh_at c1 x` by metis_tac[] >>
     gvs[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `!n. _ ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  `s2.vs_labels = s1.vs_labels` by
    (irule emit_op_run_labels >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `op_taint u2 data = {} /\ op_prov H2 data = NONE` by
    (drule_all old_operand_ghost_frame >> simp[]) >>
  `?v w. eval_operand data s2 = SOME v /\ eval_operand off s2 = SOME w` by
    (qpat_assum `emit_op ADD [data;off] c2 = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def, AllCaseEqs()]) >>
  qabbrev_tac `ss2 = s2 with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `run_inst_seq (emitted_insts c2 ready) ss2 = OK (t with vs_inst_idx := ss2.vs_inst_idx)` by
    (qpat_assum `emit_op ADD _ c2 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s2`,`SUC (SUC s.vs_inst_idx)`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def, Abbr `ss2`]) >>
  `eval_operand data ss2 = SOME v /\ eval_operand off ss2 = SOME w` by simp[Abbr `ss2`] >>
  drule_all emit_scalar_add_endpoint_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  `t.vs_labels = s2.vs_labels` by
    (irule emit_op_run_labels >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `op_taint u data = {} /\ op_prov H data = NONE` by
    (fs[Abbr `ss2`, cj 4 moduleLoweringPropsTheory.control_moves_keep_vars] >>
     qpat_assum `!q. not_fresh_at c2 q ==> _`
       (mp_then Any mp_tac old_operand_ghost_frame) >>
     disch_then (qspec_then `data` mp_tac) >> simp[]) >>
  `!x. head = Var x ==> not_fresh_at ready x` by
    (qpat_assum `emit_op ADD [data;off] c2 = _`
      (mp_then Any mp_tac abi_decoder_operand_live_emit) >>
     Cases_on `head` >> simp[calldata_operand_live_not_fresh]) >>
  `!x. not_fresh_at st x ==> not_fresh_at c1 x /\ not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `LENGTH (emitted_insts st c1) = 1 /\ LENGTH (emitted_insts c1 c2) = 1 /\
   LENGTH (emitted_insts c2 ready) = 1` by metis_tac[emit_op_length] >>
  `same_blocks st c1 /\ same_blocks c1 c2 /\ same_blocks c2 ready` by
    metis_tac[emit_op_same_blocks] >>
  `cs_extends st c1 /\ cs_extends c1 c2 /\ cs_extends c2 ready` by
    (rpt conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  fs[Abbr `ss2`, ADD1, cj 4 moduleLoweringPropsTheory.control_moves_keep_vars] >>
  `eval_operand data s1 = SOME (a + 32w)` by
    (qpat_assum `emit_op ADD [src; Lit 32w] st = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `eval_operand off s2 = SOME (b * n2w stride)` by
    (qpat_assum `emit_op MUL _ c1 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `eval_operand data s2 = SOME (a + 32w)` by
    (qpat_assum `!q. not_fresh_at c1 q ==> _`
       (mp_then Any mp_tac old_operand_ghost_frame) >>
     disch_then (qspec_then `data` mp_tac) >> simp[]) >>
  `eval_operand head t = SOME (a + 32w + b * n2w stride)` by
    (qpat_assum `emit_op ADD [data;off] c2 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `eval_operand data t = SOME (a + 32w)` by
    (qpat_assum `!q. not_fresh_at c2 q ==> _`
       (mp_then Any mp_tac old_operand_ghost_frame) >>
     disch_then (qspec_then `data` mp_tac) >> simp[]) >>
  qexistsl_tac [`H`,`u`] >> simp[] >>
  irule frag_exec_ptr_seq >>
  qexistsl_tac [`(\g z v. g = H1 /\ z = u1 /\ v = s1 with vs_inst_idx := s.vs_inst_idx + 1)`,`c1`] >>
  simp[] >> (conj_tac >- metis_tac[cs_extends_trans]) >>
  irule frag_exec_ptr_seq >>
  qexistsl_tac [`(\g z v. g = H2 /\ z = u2 /\ v = s2 with vs_inst_idx := s.vs_inst_idx + 2)`,`c2`] >> simp[]
QED

