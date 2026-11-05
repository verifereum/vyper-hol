Theory lowerDloadCleanCopy
Ancestors
  lowerDloadRelocation regularCallEmitSim regularMemorySim codegenRel
  venomState list pred_set ptrDiscipline memLocDefs venomExecSemantics finite_map

Theorem ld_shared_payload_write:
  ld_byte_rel R Ts Tt (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a b. R a b ==> ((p <= a /\ a < p + LENGTH bs) <=>
                        (q <= b /\ b < q + LENGTH bs))) /\
  (!a b. R a b /\ p <= a /\ a < p + LENGTH bs ==> a-p = b-q) ==>
  ld_byte_rel R
    (Ts DIFF {a | p <= a /\ a < p + LENGTH bs})
    (Tt DIFF {b | q <= b /\ b < q + LENGTH bs})
    (\a. read_memory a 1 (write_memory_with_expansion p bs s))
    (\b. read_memory b 1 (write_memory_with_expansion q bs t))
Proof
  simp[ld_byte_rel_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `p <= a /\ a < p + LENGTH bs`
  >- (`q <= b /\ b < q + LENGTH bs` by metis_tac[] >>
      `a-p = b-q` by metis_tac[] >>
      simp[read_memory_def, venom_returndata_read_byte, GENLIST,
           read_byte_write_memory_with_expansion]) >>
  `~(q <= b /\ b < q + LENGTH bs)` by metis_tac[] >>
  qpat_x_assum `!a b. R a b ==> (b IN Tt ==> a IN Ts) /\ _`
    (qspecl_then [`a`,`b`] mp_tac) >>
  simp[read_memory_def, venom_returndata_read_byte, GENLIST,
       read_byte_write_memory_with_expansion]
QED

Theorem ld_clean_copy_mem_taint:
  i.inst_opcode IN {DLOADBYTES; CODECOPY} /\
  i.inst_operands = [dst;off;sz] /\
  eval_operand dst s = SOME p /\ eval_operand sz s = SOME n /\
  step_inst fuel C i s = OK z ==>
  (step_taint i s z tn).t_mem =
    tn.t_mem DIFF {a | w2n p <= a /\ a < w2n p + w2n n}
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst fuel C i s = OK z` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  gvs[] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    written_taint_def, step_writes_def, source_memory_write_ranges_def,
    write_memory_with_expansion_def, expand_memory_def, write_memory_def,
    range_bytes_def, sized_source_write_range_def, EXTENSION, FLOOKUP_DEF] >>
  simp[SF CONJ_ss]
QED
