(* Data-section copies: total source reads, allocated destination writes. *)
Theory ctorDeployMemoryRunPtrPrefixCopyStep
Ancestors
  ctorDeployMemoryRunPtrPrefixSteps ptrSafeRun ptrDiscipline
  venomExecSemantics venomState venomInst memLocDefs codegenRel contextCodegenRel
  list words finite_map pred_set valueEncodingProps

Theorem prefix_dloadbytes_dispatch[local]:
  step_inst_base (mk_inst iid DLOADBYTES [dst;src;lenop] []) s =
  (case (eval_operand dst s, eval_operand src s, eval_operand lenop s) of
     (SOME d, SOME sb, SOME k) =>
       OK (write_memory_with_expansion (w2n d)
         (TAKE (w2n k) (DROP (w2n sb) s.vs_data_section ++
                       REPLICATE (w2n k) 0w)) s)
   | _ => Error "undefined operand")
Proof
  pure_rewrite_tac[step_inst_base_def, mk_inst_def] >> simp[]
QED

Theorem prefix_dloadbytes_step:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME k ==>
  step_inst fuel ctx (mk_inst iid DLOADBYTES [dst;src;lenop] []) s =
    OK (write_memory_with_expansion (w2n d)
      (TAKE (w2n k) (DROP (w2n sb) s.vs_data_section ++
                    REPLICATE (w2n k) 0w)) s)
Proof
  simp[step_inst_non_invoke, mk_inst_def, prefix_dloadbytes_dispatch]
QED

Theorem prefix_dloadbytes_ptr_step:
  eval_operand (Var dst) s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME k /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= w2n d /\ w2n d + w2n k <= b+sz /\
  op_taint tn (Var dst) = {} /\ op_taint tn src = {} /\
  op_taint tn lenop = {} /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lo fuel ctx fn PG G tn
    (mk_inst iid DLOADBYTES [Var dst;src;lenop] []) s
Proof
  rpt strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, prefix_dloadbytes_step] >>
  simp[access_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       mem_write_ops_def, mk_inst_def, taint_ok_def,
       sized_source_write_range_def, step_inst_non_invoke,
       REWRITE_RULE [mk_inst_def] prefix_dloadbytes_dispatch,
       write_memory_with_expansion_def, allocas_from_def] >> metis_tac[]
QED

Theorem prefix_dloadbytes_ghost_step:
  step_inst fuel ctx (mk_inst iid DLOADBYTES [dst;src;lenop] []) s = OK t ==>
  ghost_step fuel ctx PG G tn (mk_inst iid DLOADBYTES [dst;src;lenop] []) s =
    (G, step_taint (mk_inst iid DLOADBYTES [dst;src;lenop] []) s t tn)
Proof
  rpt strip_tac >>
  simp[ghost_step_def, mk_inst_def, step_prov_def, set_prov_def,
       finite_mapTheory.DRESTRICT_UNIV] >>
  gvs[step_inst_non_invoke, mk_inst_def]
QED

Theorem prefix_dloadbytes_taint_frame:
  let qt = step_taint (mk_inst iid DLOADBYTES [dst;src;lenop] []) s t tn in
  qt.t_var = tn.t_var /\ qt.t_stor = tn.t_stor /\
  qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm
Proof
  simp[step_taint_def, mk_inst_def, set_var_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem prefix_dloadbytes_mem_taint:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME k ==>
  (step_taint (mk_inst iid DLOADBYTES [dst;src;lenop] []) s
    (write_memory_with_expansion (w2n d)
      (TAKE (w2n k) (DROP (w2n sb) s.vs_data_section ++
                    REPLICATE (w2n k) 0w)) s) tn).t_mem =
    tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + w2n k}
Proof
  rpt strip_tac >>
  simp[step_taint_def, mem_taint_def, mk_inst_def, new_site_bytes_def,
       write_memory_with_expansion_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def, finite_mapTheory.FLOOKUP_DEF] >>
  simp[SF CONJ_ss]
QED

Theorem prefix_dloadbytes_window:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME k /\
  step_inst fuel ctx (mk_inst iid DLOADBYTES [dst;src;lenop] []) s = OK t ==>
  mem_bytes_at (w2n d) (w2n k) t.vs_memory =
    TAKE (w2n k) (DROP (w2n sb) s.vs_data_section ++ REPLICATE (w2n k) 0w)
Proof
  rpt strip_tac >>
  `t = write_memory_with_expansion (w2n d)
    (TAKE (w2n k) (DROP (w2n sb) s.vs_data_section ++ REPLICATE (w2n k) 0w)) s` by
    (qpat_x_assum `step_inst _ _ _ _ = OK t` mp_tac >>
     simp[step_inst_non_invoke, REWRITE_RULE [mk_inst_def] prefix_dloadbytes_dispatch, mk_inst_def]) >> gvs[] >>
  `LENGTH (TAKE (w2n k)
    (DROP (w2n sb) s.vs_data_section ++ REPLICATE (w2n k) 0w)) = w2n k` by simp[] >>
  metis_tac[write_memory_mem_bytes_at_same]
QED

Theorem prefix_dloadbytes_zero:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME 0w ==>
  step_inst fuel ctx (mk_inst iid DLOADBYTES [dst;src;lenop] []) s =
    OK (write_memory_with_expansion (w2n d) [] s)
Proof
  rpt strip_tac >> simp[step_inst_non_invoke, REWRITE_RULE [mk_inst_def] prefix_dloadbytes_dispatch, mk_inst_def]
QED

Theorem prefix_dloadbytes_past_data:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME k /\ LENGTH s.vs_data_section <= w2n sb ==>
  step_inst fuel ctx (mk_inst iid DLOADBYTES [dst;src;lenop] []) s =
    OK (write_memory_with_expansion (w2n d) (REPLICATE (w2n k) 0w) s)
Proof
  rpt strip_tac >> simp[step_inst_non_invoke, REWRITE_RULE [mk_inst_def] prefix_dloadbytes_dispatch, mk_inst_def, DROP_LENGTH_TOO_LONG, TAKE_LENGTH_TOO_LONG]
QED

Theorem prefix_dloadbytes_frame:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME k /\
  step_inst fuel ctx (mk_inst iid DLOADBYTES [dst;src;lenop] []) s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (allocas_from lo t <=> allocas_from lo s) /\
  t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_vars = s.vs_vars /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK t` mp_tac >>
  simp[step_inst_non_invoke, mk_inst_def,
       REWRITE_RULE [mk_inst_def] prefix_dloadbytes_dispatch] >>
  strip_tac >> gvs[write_memory_with_expansion_def, allocas_from_def]
QED

Theorem prefix_dloadbytes_clean:
  eval_operand dst s = SOME d /\ eval_operand src s = SOME sb /\
  eval_operand lenop s = SOME k /\
  step_inst fuel ctx (mk_inst iid DLOADBYTES [dst;src;lenop] []) s = OK t ==>
  let qt = step_taint (mk_inst iid DLOADBYTES [dst;src;lenop] []) s t tn in
  qt.t_mem SUBSET tn.t_mem /\
  DISJOINT (range_bytes [(w2n d,w2n k)]) qt.t_mem
Proof
  rpt strip_tac >>
  `t = write_memory_with_expansion (w2n d)
    (TAKE (w2n k) (DROP (w2n sb) s.vs_data_section ++ REPLICATE (w2n k) 0w)) s` by
    (qpat_x_assum `step_inst _ _ _ _ = OK t` mp_tac >>
     simp[step_inst_non_invoke, mk_inst_def,
          REWRITE_RULE [mk_inst_def] prefix_dloadbytes_dispatch]) >>
  gvs[] >> simp[prefix_dloadbytes_mem_taint, range_bytes_def] >>
  simp[step_taint_def, mem_taint_def, mk_inst_def, new_site_bytes_def,
       write_memory_with_expansion_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def, finite_mapTheory.FLOOKUP_DEF] >>
  simp[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

val _ = export_theory();
