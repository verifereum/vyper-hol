(* Joint count validation, count store and scratch-index initialization. *)
Theory decoderArrayInitPtr
Ancestors abiDecoderGuards abiDecoderArrayInitExec decoderArraySetupPtr decoderIndexInitPtr
  decoderNavigationPtr calldataClampPtr typedCopyPtr bodyPtrDefs
  compileEnv emitHelper venomInst venomExecSemantics venomState words list
  rich_list arithmetic finite_map ptrDiscipline ptrSafeRun venomInstProofs codegenRel contextCodegenRel

Theorem calldata_count_guard_layout[local]:
  abi_decode_count_guard CALLDATALOAD src maxn st = (cnt,st') ==>
  cnt = Var ("%" ++ toString st.cs_next_var) /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_next_var = st.cs_next_var + 3 /\
  st'.cs_next_id = st.cs_next_id + 4 /\
  st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id CALLDATALOAD [src]
       ["%" ++ toString st.cs_next_var];
     mk_inst (st.cs_next_id + 1) GT
       [cnt; Lit (n2w maxn)] ["%" ++ toString (st.cs_next_var + 1)];
     mk_inst (st.cs_next_id + 2) ISZERO
       [Var ("%" ++ toString (st.cs_next_var + 1))]
       ["%" ++ toString (st.cs_next_var + 2)];
     mk_inst (st.cs_next_id + 3) ASSERT
       [Var ("%" ++ toString (st.cs_next_var + 2))] []]
Proof
  simp[abi_decode_count_guard_def, emit_op_def, emit_void_def,
    emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem count_bound_comparison_frag_ptr[local]:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id GT [src; Lit bound] [out]] /\
  eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?H u.
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\
        v = (update_var out (bool_to_word (w2n a > w2n bound)) s with
          vs_inst_idx := SUC s.vs_inst_idx)) R /\
    op_taint u (Var out) = {} /\ op_prov H (Var out) = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `inst = mk_inst id GT [src; Lit bound] [out]` >>
  qabbrev_tac `t = update_var out (bool_to_word (w2n a > w2n bound)) s` >>
  `step_inst_base inst s = OK t` by
    (simp[Abbr `inst`, Abbr `t`, step_inst_base_def, mk_inst_def,
      exec_pure2_def] >> Cases_on `src` >> gvs[eval_operand_def]) >>
  `!fuel fn. ~ctx_has_dalloca ctx ==>
    ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn inst s` by
    (rpt strip_tac >>
     `op_taint tn (Lit bound) = {}` by simp[op_taint_def] >>
     qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       allocas_from_def, Abbr `inst`, mk_inst_def, step_inst_non_invoke,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       Abbr `t`, update_var_def] >>
     metis_tac[]) >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  qexistsl_tac [`H`,`u`] >> conj_tac
  >- (irule ptr_fragment_step >>
      simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `t` >>
      simp[Abbr `H`, Abbr `u`] >> gvs[Abbr `t`, update_var_def, mk_inst_def]) >>
  simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `t`,
    op_prov_def, step_prov_def, out_prov_def, set_prov_def,
    op_taint_def, step_taint_def, out_taint_def, set_var_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, mk_inst_def,
    mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    update_var_def, source_memory_write_ranges_def, range_bytes_def,
    pred_setTheory.EXTENSION, FDOM_DRESTRICT, SF CONJ_ss] >>
  simp[FLOOKUP_DEF, SF CONJ_ss]
QED
