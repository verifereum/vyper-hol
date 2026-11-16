(* Clean scalar instruction sequences share one execution and ghost endpoint
   at every dead mask and reserved-memory bound. *)
Theory augAssignFullScalar
Ancestors
  augAssignPtrScalarRun augAssignPtrScalarSafety augAssignPtrScalarCertificate
  instSeqPtrLo fragGasSeqPtr fragGasOriginPtr fragExecMem fragGasFresh
  bodyPtrDefs ptrDiscipline codegenRel contextCodegenRel unitTransformDefs
  instMemFrontier memSafeRun
  venomExecSemantics venomInst venomState freshWrites varsExt
  list rich_list pred_set

Theorem scalar_shape_memory_checks:
  scalar_shape i ==>
  inst_mem_below_frontier i s /\ inst_dload_in_section i s
Proof
  simp[scalar_shape_def, scalar_binary_def, scalar_unary_def] >>
  strip_tac >> gvs[] >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem scalar_code_memory_checks:
  !code A s.
    scalar_code A code ==>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s
Proof
  Induct >> simp[scalar_code_def, run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule scalar_shape_control >> strip_tac >>
  `inst_mem_below_frontier h s /\ inst_dload_in_section h s` by
    metis_tac[scalar_shape_memory_checks] >>
  conj_tac >- metis_tac[] >> simp[] >>
  Cases_on `step_inst_base h s` >> simp[] >> metis_tac[]
QED

(* The endpoint is chosen before D and lo, so callers may use D = DF H
   under a valid-horizon guard without choosing different ghosts per H. *)
Theorem scalar_code_origin_ptr_success:
  !code A s t G tn ctx func PG explicit bb.
    scalar_code A code /\
    (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq code s = OK t ==>
    ?G' tn'.
      (!D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
        gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
          (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code), G', tn')) /\
      (!v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) code)) ==>
        FLOOKUP G' v = FLOOKUP G v /\
        op_taint tn' (Var v) = op_taint tn (Var v)) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!v. v IN A UNION BIGUNION (set (MAP (\i. set i.inst_outputs) code)) ==>
        op_prov G' (Var v) = NONE /\ op_taint tn' (Var v) = {})
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
                     d_imm := K {}; d_ret := K {}|>` >>
  `?G' tn'. inst_seq_ptr D0 0 ctx func PG G tn code s G' tn'` by
    metis_tac[scalar_code_inst_seq_ptr] >>
  pop_assum strip_assume_tac >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  qspecl_then [`code`, `A`, `G`, `tn`, `s`, `G'`, `tn'`, `t`] mp_tac
    (Q.INST [`D` |-> `D0`, `ctx` |-> `ctx`, `fn` |-> `func`, `PG` |-> `PG`]
      scalar_seq_success_clean) >>
  impl_tac >- simp[] >> disch_tac >>
  qspecl_then [`code`, `A`, `s`] mp_tac scalar_code_memory_checks >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> rpt gen_tac >> strip_tac >>
  `inst_seq_ptr D lo ctx func PG G tn code s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D0` >>
     simp[Abbr `D0`]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code`
    by fs[EVERY_MEM] >>
  qspecl_then [`code`, `s`, `t`, `G`, `tn`, `G'`, `tn'`, `ctx`, `func`, `bb`]
    mp_tac (Q.INST [`D` |-> `D`, `lo` |-> `lo`, `PG` |-> `PG`,
                   `explicit` |-> `explicit`] run_inst_seq_gas_origin_ptr_path) >>
  simp[]
QED
