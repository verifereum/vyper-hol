Theory lowerDloadCopyReadback
Ancestors
  lowerDloadDefs venomState words list rich_list

Theorem ld_codecopy_payload:
  code_layout_valid s /\ r.vs_code = s.vs_code /\
  w2n (x:256 word) + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256) ==>
  TAKE n
    (DROP (w2n (x + n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)))
      r.vs_code ++ REPLICATE n 0w) =
  TAKE n (DROP (w2n x) s.vs_data_section ++ REPLICATE n 0w)
Proof
  strip_tac >>
  `w2n (x + n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) =
   w2n x + (LENGTH s.vs_code - LENGTH s.vs_data_section)` by
    simp[word_add_def, w2n_n2w] >>
  gvs[code_layout_valid_def] >> simp[DROP_APPEND2]
QED

(* Observe the copied data at arbitrary width, including zero bytes. *)
Theorem ld_codecopy_readback:
  code_layout_valid s /\ r.vs_code = s.vs_code /\
  w2n (x:256 word) + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256) ==>
  let bs = TAKE n
    (DROP (w2n (x + n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)))
      r.vs_code ++ REPLICATE n 0w) in
  TAKE n (DROP p (write_memory_with_expansion p bs r).vs_memory) =
    TAKE n (DROP (w2n x) s.vs_data_section ++ REPLICATE n 0w)
Proof
  strip_tac >> drule_all ld_codecopy_payload >>
  disch_then (qspec_then `n` (fn th => rewrite_tac[th])) >>
  qabbrev_tac `bs = TAKE n (DROP (w2n x) s.vs_data_section ++ REPLICATE n 0w)` >>
  `LENGTH bs = n` by simp[Abbr `bs`, LENGTH_TAKE] >>
  simp[write_memory_with_expansion_def] >>
  qabbrev_tac `mem = r.vs_memory` >>
  Cases_on `0 < p + n - LENGTH mem`
  >- (simp[] >>
      `p <= LENGTH (mem ++ REPLICATE (n + p - LENGTH mem) 0w)` by
        (simp[] >> decide_tac) >>
      once_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_APPEND, LENGTH_TAKE, DROP_TAKE, TAKE_APPEND]) >>
  `p <= LENGTH mem` by decide_tac >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_APPEND, LENGTH_TAKE, DROP_TAKE, TAKE_APPEND]
QED
