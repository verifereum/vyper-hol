Theory lowerDloadCleanCopy
Ancestors
  lowerDloadRelocation regularCallEmitSim regularMemorySim codegenRel
  venomState list pred_set

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
