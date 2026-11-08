(* Actual singleton constructor argument registration. *)
Theory ctorDeployMemoryRunPtrPrefixRegisterWord
Ancestors
  ctorDeployMemoryRunPtrPrefixWord ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixSequence instIdxIndep
  moduleLowering context compileEnv emitHelper
  abiEncoder exprLoweringProps finite_map list
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst memLocDefs codegenRel contextCodegenRel words

Theorem prefix_register_noclamp_code:
  compile_register_constructor_args ce
    [(name,T,F,abi_size,DecPrimWord NoClamp)] off data_size st = (ce',st') /\
  FLOOKUP ce.ce_vars name = SOME (MemLoc old 32) ==>
  let dst = "%" ++ toString st.cs_next_var;
      src = "%" ++ toString (st.cs_next_var+1);
      value = "%" ++ toString (st.cs_next_var+2)
  in
    emitted_insts st st' =
      [mk_inst st.cs_next_id ALLOCA [Lit 32w] [dst];
       mk_inst (st.cs_next_id+1) ADD [Lit 0w;Lit (n2w off)] [src];
       mk_inst (st.cs_next_id+2) DLOAD [Var src] [value];
       mk_inst (st.cs_next_id+3) MSTORE [Var dst;Var value] []] /\
    ce' = ce with ce_vars updated_by (\m. m |+ (name,PtrVar (Var dst) 32))
Proof
  rpt strip_tac >> gvs[compile_register_constructor_args_def, compile_alloc_buffer_def,
       compile_decode_args_def, var_location_memory_size_def,
       var_location_decode_operand_def, compile_abi_clamp_basetype_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       FLOOKUP_UPDATE, emitted_insts_def, DROP_APPEND] >>
  rpt strip_tac >> gvs[]
QED

Theorem prefix_register_names:
  ALL_DISTINCT ["%" ++ toString (n:num); "%" ++ toString (n+1);
                "%" ++ toString (n+2)]
Proof
  simp[ASCIInumbersTheory.toString_11]
QED

Theorem prefix_register_add_dispatch[local]:
  step_inst_base (mk_inst iid ADD ops outs) s =
    exec_pure2 $+ (mk_inst iid ADD ops outs) s
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_register_add_step:
  step_inst_base (mk_inst iid ADD [Lit 0w; Lit (n2w off)] [x]) s =
    OK (update_var x (n2w off) s)
Proof
  simp[prefix_register_add_dispatch, exec_pure2_def, mk_inst_def,
       eval_operand_def, WORD_ADD_0]
QED

Theorem prefix_register_add_ptr_step:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lo fuel ctx fn PG G tn
    (mk_inst iid ADD [Lit 0w; Lit (n2w off)] [x]) s
Proof
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_non_invoke, prefix_register_add_step, mk_inst_def,
       op_taint_def, update_var_def] >>
  rpt strip_tac >> Cases_on `op` >> gvs[]
QED

Theorem prefix_register_add_ghost:
  ghost_step fuel ctx PG G tn
    (mk_inst iid ADD [Lit 0w; Lit (n2w off)] [x]) s =
    (DRESTRICT G (COMPL {x}),
     step_taint (mk_inst iid ADD [Lit 0w; Lit (n2w off)] [x]) s
       (update_var x (n2w off) s) tn)
Proof
  simp[ghost_step_def, step_inst_non_invoke, prefix_register_add_step,
       mk_inst_def, step_prov_def, set_prov_def, out_prov_def,
       op_prov_def, first_prov_def]
QED

Theorem prefix_register_alloc_add:
  dst <> src /\ FLOOKUP s.vs_allocas aid = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s.vs_alloca_next + 32 < dimword (:256) ==>
  let i = mk_inst aid ALLOCA [Lit 32w] [dst];
      j = mk_inst (aid+1) ADD [Lit 0w; Lit (n2w off)] [src];
      a = update_var dst (n2w s.vs_alloca_next)
        (s with <| vs_allocas := s.vs_allocas |+
                    (aid,(s.vs_alloca_next,32));
                   vs_alloca_next := s.vs_alloca_next+32 |>);
      b = update_var src (n2w off) a;
      G1 = G |+ (dst,(s.vs_alloca_next,32));
      G2 = DRESTRICT G1 (COMPL {src});
      tn1 = step_taint i s a tn;
      tn2 = step_taint j a b tn1
  in
    step_inst_base i s = OK a /\ step_inst_base j a = OK b /\
    ghost_step fuel ctx PG G tn i s = (G1,tn1) /\
    ghost_step fuel ctx PG G1 tn1 j a = (G2,tn2) /\
    eval_operand (Var dst) b = SOME (n2w s.vs_alloca_next) /\
    eval_operand (Var src) b = SOME (n2w off) /\
    w2n (n2w s.vs_alloca_next : bytes32) = s.vs_alloca_next /\
    FLOOKUP G2 dst = SOME (s.vs_alloca_next,32) /\
    op_taint tn2 (Var dst) = {} /\ op_taint tn2 (Var src) = {} /\
    allocas_from lo b /\ b.vs_alloca_next = s.vs_alloca_next+32
Proof
  strip_tac >> simp[] >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  simp[prefix_alloca_step, prefix_register_add_step,
       prefix_alloca_ghost_step, prefix_register_add_ghost,
       ghost_step_def, step_inst_non_invoke, step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, op_prov_def,
       eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       out_taint_def, eval_operand_def, FLOOKUP_UPDATE] >>
  gvs[allocas_from_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `aid = aid'` >> gvs[] >> metis_tac[]
QED

Theorem prefix_register_noclamp_raw:
  compile_register_constructor_args ce
    [(name,T,F,abi_size,DecPrimWord NoClamp)] off data_size st = (ce',st') /\
  FLOOKUP ce.ce_vars name = SOME (MemLoc old 32) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  s.vs_alloca_next + 32 < dimword (:256) ==>
  let dst = "%" ++ toString st.cs_next_var;
      src = "%" ++ toString (st.cs_next_var+1);
      x = "%" ++ toString (st.cs_next_var+2);
      a = update_var dst (n2w s.vs_alloca_next)
        (s with <| vs_allocas := s.vs_allocas |+
                    (st.cs_next_id,(s.vs_alloca_next,32));
                   vs_alloca_next := s.vs_alloca_next+32 |>);
      b = update_var src (n2w off) a;
      v = word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n (n2w off:bytes32)) s.vs_data_section ++
          REPLICATE 32 0w));
      l = update_var x v b;
      t = mstore s.vs_alloca_next v l
  in
    run_inst_seq (emitted_insts st st') s = OK t /\
    FLOOKUP ce'.ce_vars name = SOME (PtrVar (Var dst) 32) /\
    eval_operand (Var dst) t = SOME (n2w s.vs_alloca_next) /\
    t.vs_alloca_next = s.vs_alloca_next+32
Proof
  strip_tac >> drule_all prefix_register_noclamp_code >>
  simp[] >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  simp[ASCIInumbersTheory.toString_11, run_inst_seq_def, prefix_alloca_step, prefix_register_add_step,
       prefix_dload_step, prefix_mstore_step, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, mstore_def,
       write_memory_def, step_inst_base_def, mk_inst_def,
       exec_read1_def, exec_write2_def]
QED

Theorem prefix_register_add_taint:
  dst <> src /\ op_taint tn (Var dst) = {} ==>
  let tn' = step_taint
    (mk_inst iid ADD [Lit 0w; Lit (n2w off)] [src]) s t tn
  in op_taint tn' (Var dst) = {} /\ op_taint tn' (Var src) = {}
Proof
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       out_taint_def, eval_operand_def, FLOOKUP_UPDATE]
QED

Theorem prefix_register_word_ptr:
  ALL_DISTINCT [dst;src;x] /\ FLOOKUP s.vs_allocas aid = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s.vs_alloca_next+32 < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  isPREFIX
    [mk_inst aid ALLOCA [Lit 32w] [dst];
     mk_inst (aid+1) ADD [Lit 0w;Lit (n2w off)] [src];
     mk_inst (aid+2) DLOAD [Var src] [x];
     mk_inst (aid+3) MSTORE [Var dst;Var x] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    G' = DRESTRICT (DRESTRICT (G |+ (dst,(s.vs_alloca_next,32)))
           (COMPL {src})) (COMPL {x}) /\
    eval_operand (Var dst) t = SOME (n2w s.vs_alloca_next) /\
    FLOOKUP G' dst = SOME (s.vs_alloca_next,32) /\
    op_taint tn' (Var dst) = {} /\
    allocas_from lo t /\ t.vs_alloca_next = s.vs_alloca_next+32 /\
    (!z. z <> dst /\ z <> src /\ z <> x ==> FLOOKUP G' z = FLOOKUP G z) /\
    (?a b l G1 G2 tn1 tn2 tn3.
      G1 = G |+ (dst,(s.vs_alloca_next,32)) /\
      G2 = DRESTRICT G1 (COMPL {src}) /\
      step_inst_base (mk_inst aid ALLOCA [Lit 32w] [dst]) s = OK a /\
      step_inst_base (mk_inst (aid+1) ADD [Lit 0w;Lit (n2w off)] [src]) a = OK b /\
      step_inst_base (mk_inst (aid+2) DLOAD [Var src] [x]) b = OK l /\
      ghost_step fuel ctx PG G tn (mk_inst aid ALLOCA [Lit 32w] [dst]) s =
        (G1,tn1) /\
      ghost_step fuel ctx PG G1 tn1
        (mk_inst (aid+1) ADD [Lit 0w;Lit (n2w off)] [src])
        (a with vs_inst_idx := s.vs_inst_idx+1) = (G2,tn2) /\
      ghost_step fuel ctx PG G2 tn2 (mk_inst (aid+2) DLOAD [Var src] [x])
        (b with vs_inst_idx := s.vs_inst_idx+2) = (G',tn3) /\
      ghost_step fuel ctx PG G' tn3 (mk_inst (aid+3) MSTORE [Var dst;Var x] [])
        (l with vs_inst_idx := s.vs_inst_idx+3) = (G',tn')) /\
    run_inst_seq
      [mk_inst aid ALLOCA [Lit 32w] [dst];
       mk_inst (aid+1) ADD [Lit 0w;Lit (n2w off)] [src];
       mk_inst (aid+2) DLOAD [Var src] [x];
       mk_inst (aid+3) MSTORE [Var dst;Var x] []] s = OK t /\
    (ptr_safe_block D lo fuel ctx fn PG G' tn' bb
       (t with vs_inst_idx := s.vs_inst_idx+4) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  qpat_x_assum `ALL_DISTINCT _` (strip_assume_tac o SRULE []) >>
  qabbrev_tac `i = mk_inst aid ALLOCA [Lit 32w] [dst]` >>
  qabbrev_tac `j = mk_inst (aid+1) ADD [Lit 0w;Lit (n2w off)] [src]` >>
  qabbrev_tac `k = mk_inst (aid+2) DLOAD [Var src] [x]` >>
  qabbrev_tac `h = mk_inst (aid+3) MSTORE [Var dst;Var x] []` >>
  qabbrev_tac `a = update_var dst (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+ (aid,(s.vs_alloca_next,32));
              vs_alloca_next := s.vs_alloca_next+32|>)` >>
  qabbrev_tac `b = update_var src (n2w off) a` >>
  qabbrev_tac `v = word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n (n2w off:bytes32)) s.vs_data_section ++ REPLICATE 32 0w))` >>
  qabbrev_tac `l = update_var x v b` >>
  qabbrev_tac `t = mstore s.vs_alloca_next v l` >>
  qabbrev_tac `G1 = G |+ (dst,(s.vs_alloca_next,32))` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {src})` >>
  qabbrev_tac `G3 = DRESTRICT G2 (COMPL {x})` >>
  qabbrev_tac `q1 = step_taint i s a tn` >>
  qabbrev_tac `q2 = step_taint j (a with vs_inst_idx := s.vs_inst_idx+1)
    (b with vs_inst_idx := s.vs_inst_idx+1) q1` >>
  qabbrev_tac `q3 = step_taint k (b with vs_inst_idx := s.vs_inst_idx+2)
    (l with vs_inst_idx := s.vs_inst_idx+2) q2` >>
  qabbrev_tac `q4 = step_taint h (l with vs_inst_idx := s.vs_inst_idx+3)
    (t with vs_inst_idx := s.vs_inst_idx+3) q3` >>
  qexistsl [`t`,`G3`,`q4`] >>
  conj_tac >- simp[Abbr `G3`, Abbr `G2`, Abbr `G1`] >>
  conj_tac >- suspend "address" >>
  conj_tac >- simp[Abbr `G3`, Abbr `G2`, Abbr `G1`, FLOOKUP_DRESTRICT,
                  FLOOKUP_UPDATE] >>
  conj_tac >- suspend "clean" >>
  conj_tac >- suspend "frontier" >>
  conj_tac >- simp[Abbr `t`, Abbr `l`, Abbr `b`, Abbr `a`,
                  update_var_def, mstore_def, write_memory_def] >>
  conj_tac >- simp[Abbr `G3`, Abbr `G2`, Abbr `G1`, FLOOKUP_DRESTRICT,
                  FLOOKUP_UPDATE] >>
  conj_tac >- suspend "updates" >>
  qabbrev_tac `u = \n:num. if n=0 then s else if n=1 then a else
    if n=2 then b else if n=3 then l else t` >>
  qabbrev_tac `g = \n:num. if n=0 then G else if n=1 then G1 else
    if n=2 then G2 else G3` >>
  qabbrev_tac `q = \n:num. if n=0 then tn else if n=1 then q1 else
    if n=2 then q2 else if n=3 then q3 else q4` >>
  `isPREFIX [i;j;k;h] (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule prefix_trace_ptr_safe_block >>
  disch_then (qspecl_then [`G`,`tn`,`u`,`g`,`q`] mp_tac) >>
  simp[Abbr `u`, Abbr `g`, Abbr `q`] >> disch_then irule >>
  `i.inst_opcode = ALLOCA /\ j.inst_opcode = ADD /\
   k.inst_opcode = DLOAD /\ h.inst_opcode = MSTORE` by
    simp[Abbr `i`, Abbr `j`, Abbr `k`, Abbr `h`, mk_inst_def] >>
  simp[is_terminator_def] >> qx_gen_tac `n` >> strip_tac >>
  Cases_on `n=0` >- (gvs[] >> suspend "alloc") >>
  Cases_on `n=1` >- (gvs[] >> suspend "add") >>
  Cases_on `n=2` >- (gvs[] >> suspend "load") >>
  `n=3` by decide_tac >> gvs[] >> suspend "store"
QED

Resume prefix_register_word_ptr[alloc]:
  simp[Abbr `i`, Abbr `a`, Abbr `G1`, Abbr `q1`,
       prefix_alloca_step, prefix_alloca_ptr_step,
       ghost_step_def, step_inst_non_invoke, step_prov_def, set_prov_def,
       out_prov_def, mk_inst_def, update_var_def, FLOOKUP_UPDATE,
       venom_state_component_equality]
QED

Resume prefix_register_word_ptr[add]:
  `allocas_from lo a` by
    (simp[Abbr `a`, allocas_from_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `aid = aid'` >> gvs[allocas_from_def] >> metis_tac[]) >>
  simp[Abbr `j`, Abbr `b`, Abbr `G2`, Abbr `q2`,
       prefix_register_add_step, step_inst_non_invoke,
       prefix_register_add_ptr_step, prefix_register_add_ghost,
       allocas_from_def, update_var_def, venom_state_component_equality] >>
  irule prefix_register_add_ptr_step >> gvs[allocas_from_def] >> metis_tac[]
QED

Resume prefix_register_word_ptr[load]:
  `allocas_from lo b` by
    (simp[Abbr `a`, Abbr `b`, allocas_from_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `aid = aid'` >> gvs[allocas_from_def] >> metis_tac[]) >>
  `op_taint q2 (Var src) = {}` by
    simp[Abbr `q2`, Abbr `j`, op_taint_def, step_taint_def,
         set_var_taint_def, out_taint_def, mk_inst_def, eval_operand_def,
         FLOOKUP_UPDATE] >>
  `eval_operand (Var src) b = SOME (n2w off) /\
   b.vs_data_section = s.vs_data_section` by
    simp[Abbr `b`, Abbr `a`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base k b = OK l` by
    simp[Abbr `k`, Abbr `l`, Abbr `v`, step_inst_base_def, mk_inst_def,
         exec_read1_def] >>
  simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
       is_terminator_def] >>
  conj_tac
  >- (simp[Abbr `k`] >> irule prefix_dload_ptr_step >>
      gvs[allocas_from_def] >> metis_tac[]) >>
  simp[Abbr `k`, Abbr `G3`, Abbr `q3`, ghost_step_def,
       step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
       is_terminator_def, step_prov_def, set_prov_def, out_prov_def,
       mk_inst_def]

QED

Resume prefix_register_word_ptr[store]:
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  `w2n (n2w s.vs_alloca_next:bytes32) = s.vs_alloca_next` by simp[] >>
  `eval_operand (Var dst) l = SOME (n2w s.vs_alloca_next) /\
   eval_operand (Var x) l = SOME v` by
    simp[Abbr `l`, Abbr `b`, Abbr `a`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `FLOOKUP G3 dst = SOME (s.vs_alloca_next,32)` by
    simp[Abbr `G3`, Abbr `G2`, Abbr `G1`, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  `allocas_from lo l` by
    (simp[Abbr `l`, Abbr `a`, Abbr `b`, allocas_from_def, update_var_def,
          FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `aid = aid'` >> gvs[allocas_from_def] >> metis_tac[]) >>
  `op_taint q3 (Var dst) = {} /\ op_taint q3 (Var x) = {}` by
    (simp[Abbr `q3`, Abbr `q2`, Abbr `q1`, Abbr `i`, Abbr `j`, Abbr `k`,
          op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
          mk_inst_def, eval_operand_def, FLOOKUP_UPDATE] >>
     Cases_on `lookup_var src (b with vs_inst_idx := s.vs_inst_idx+2)` >> simp[]) >>
  `step_inst_base h l = OK t` by
    simp[Abbr `h`, Abbr `t`, step_inst_base_def, mk_inst_def, exec_write2_def] >>
  `step_inst fuel ctx h (l with vs_inst_idx := s.vs_inst_idx+3) =
    OK (t with vs_inst_idx := s.vs_inst_idx+3)` by
    simp[step_inst_non_invoke, step_inst_inst_idx_indep, exec_result_map_def,
         is_terminator_def] >>
  simp[] >> conj_tac
  >- (simp[Abbr `h`] >> irule prefix_mstore_ptr_step >>
      gvs[eval_op_inst_idx, allocas_from_def] >> metis_tac[]) >>
  simp[Abbr `q4`, Abbr `h`] >> irule prefix_mstore_ghost_step >> simp[]
QED

Resume prefix_register_word_ptr[address]:
  simp[Abbr `t`, Abbr `l`, Abbr `b`, Abbr `a`, eval_operand_def,
       lookup_var_def, update_var_def, mstore_def, write_memory_def,
       FLOOKUP_UPDATE]
QED

Resume prefix_register_word_ptr[clean]:
  `op_taint q1 (Var dst) = {}` by
    simp[Abbr `q1`, Abbr `i`, prefix_alloca_output_taint] >>
  `op_taint q2 (Var dst) = {}` by
    (simp[Abbr `q2`, Abbr `j`, op_taint_def, step_taint_def,
          set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE] >> gvs[op_taint_def]) >>
  `op_taint q3 (Var dst) = {}` by
    (simp[Abbr `q3`, Abbr `k`, op_taint_def, step_taint_def,
          set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE] >> gvs[op_taint_def]) >>
  simp[Abbr `q4`, Abbr `h`, op_taint_def, step_taint_def,
       set_var_taint_def, mk_inst_def, DRESTRICT_UNIV] >> gvs[op_taint_def]
QED

Resume prefix_register_word_ptr[frontier]:
  simp[Abbr `t`, Abbr `l`, Abbr `b`, Abbr `a`, allocas_from_def,
       update_var_def, mstore_def, write_memory_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `aid = aid'` >> gvs[allocas_from_def] >> metis_tac[]
QED

Resume prefix_register_word_ptr[updates]:
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  `eval_operand (Var src) b = SOME (n2w off) /\
   b.vs_data_section = s.vs_data_section /\
   eval_operand (Var dst) l = SOME (n2w s.vs_alloca_next) /\
   eval_operand (Var x) l = SOME v` by
    simp[Abbr `l`, Abbr `b`, Abbr `a`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base i s = OK a` by
    simp[Abbr `i`, Abbr `a`, prefix_alloca_step] >>
  `step_inst_base j a = OK b` by
    simp[Abbr `j`, Abbr `b`, prefix_register_add_step] >>
  `step_inst_base k b = OK l` by
    simp[Abbr `k`, Abbr `l`, Abbr `v`, step_inst_base_def, mk_inst_def,
         exec_read1_def] >>
  `step_inst_base h l = OK t` by
    simp[Abbr `h`, Abbr `t`, step_inst_base_def, mk_inst_def, exec_write2_def] >>
  qexistsl [`a`,`b`,`l`,`G1`,`G2`,`q1`,`q2`,`q3`] >>
  simp[Abbr `i`, Abbr `j`, Abbr `k`, Abbr `h`, Abbr `G1`, Abbr `G2`,
       Abbr `G3`, Abbr `q1`, Abbr `q2`, Abbr `q3`, Abbr `q4`,
       ghost_step_def, step_inst_non_invoke, step_inst_inst_idx_indep,
       exec_result_map_def, is_terminator_def, step_prov_def, set_prov_def,
       out_prov_def, first_prov_def, op_prov_def, mk_inst_def] >>
  simp[Abbr `a`, update_var_def, FLOOKUP_UPDATE]
QED

Finalise prefix_register_word_ptr

Theorem prefix_register_noclamp_ptr:
  compile_register_constructor_args ce
    [(name,T,F,abi_size,DecPrimWord NoClamp)] off data_size st = (ce',st') /\
  FLOOKUP ce.ce_vars name = SOME (MemLoc old 32) /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s.vs_alloca_next+32 < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  let dst = "%" ++ toString st.cs_next_var;
      src = "%" ++ toString (st.cs_next_var+1);
      x = "%" ++ toString (st.cs_next_var+2)
  in ?t G' tn'.
    run_inst_seq (emitted_insts st st') s = OK t /\
    FLOOKUP ce'.ce_vars name = SOME (PtrVar (Var dst) 32) /\
    eval_operand (Var dst) t = SOME (n2w s.vs_alloca_next) /\
    FLOOKUP G' dst = SOME (s.vs_alloca_next,32) /\
    op_taint tn' (Var dst) = {} /\ allocas_from lo t /\
    t.vs_alloca_next = s.vs_alloca_next+32 /\
    G' = DRESTRICT (DRESTRICT (G |+ (dst,(s.vs_alloca_next,32)))
           (COMPL {src})) (COMPL {x}) /\
    (!z. z <> dst /\ z <> src /\ z <> x ==> FLOOKUP G' z = FLOOKUP G z) /\
    (let a = update_var dst (n2w s.vs_alloca_next)
           (s with <|vs_allocas := s.vs_allocas |+
                       (st.cs_next_id,(s.vs_alloca_next,32));
                     vs_alloca_next := s.vs_alloca_next+32|>);
         b = update_var src (n2w off) a;
         v = word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n (n2w off:bytes32)) s.vs_data_section ++
             REPLICATE 32 0w))
     in t = mstore s.vs_alloca_next v (update_var x v b)) /\
    (ptr_safe_block D lo fuel ctx fn PG G' tn' bb
       (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st')) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> drule_all prefix_register_noclamp_code >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  `ALL_DISTINCT ["%" ++ toString st.cs_next_var;
    "%" ++ toString (st.cs_next_var+1); "%" ++ toString (st.cs_next_var+2)]` by
    simp[ASCIInumbersTheory.toString_11] >>
  `isPREFIX
    [mk_inst st.cs_next_id ALLOCA [Lit 32w] ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id+1) ADD [Lit 0w;Lit (n2w off)]
       ["%" ++ toString (st.cs_next_var+1)];
     mk_inst (st.cs_next_id+2) DLOAD [Var ("%" ++ toString (st.cs_next_var+1))]
       ["%" ++ toString (st.cs_next_var+2)];
     mk_inst (st.cs_next_id+3) MSTORE
       [Var ("%" ++ toString st.cs_next_var);Var ("%" ++ toString (st.cs_next_var+2))] []]
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all prefix_register_word_ptr >>
  disch_then (qspecl_then [`tn`,`fuel`,`fn`] mp_tac) >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  drule_all prefix_register_noclamp_raw >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  qexistsl [`t`,`G'`,`tn'`] >> gvs[FLOOKUP_UPDATE]
QED
