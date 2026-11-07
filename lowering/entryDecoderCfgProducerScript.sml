Theory entryDecoderCfgProducer
Ancestors
  entryDecoderCfgAdapters entryDecoderCfgRules abiEncoder compileEnv
  emitHelper venomInst context pred_set

Theorem entry_cfg_decode_preserves_mutual[local]:
  (!dst src lop hi info. lop = CALLDATALOAD ==>
    entry_cfg_preserves (compile_abi_decode_to_buf dst src lop hi info)) /\
  (!dst src lop hi elems ao vo. lop = CALLDATALOAD ==>
    entry_cfg_preserves (compile_abi_decode_complex_elems dst src lop hi elems ao vo)) /\
  (!dst src lop hi ei asz msz ip cnt. lop = CALLDATALOAD ==>
    entry_cfg_preserves (compile_abi_decode_dyn_loop dst src lop hi ei asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume entry_cfg_decode_preserves_mutual[word]:
  simp[Once compile_abi_decode_to_buf_def, entry_cfg_preserves_decode_static,
       entry_cfg_preserves_clamp_basetype]
QED
Resume entry_cfg_decode_preserves_mutual[bytes]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  rewrite_tac[Once (cj 2 compile_abi_decode_to_buf_def)] >>
  ntac 3 (irule entry_cfg_preserves_bind >> reverse conj_tac
    >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
    gen_tac >> BETA_TAC) >>
  irule entry_cfg_preserves_ignore_bind >> reverse conj_tac
  >- (Cases_on `hi = Lit 0w` >>
      simp[entry_cfg_preserves_bind, entry_cfg_preserves_ignore_bind,
           entry_cfg_preserves_emit_op, entry_cfg_preserves_emit_void,
           entry_cfg_preserves_return, is_terminator_def] >>
      irule entry_cfg_preserves_ignore_bind >> reverse conj_tac
      >- simp[entry_cfg_preserves_emit_void, is_terminator_def] >>
      irule entry_cfg_preserves_bind >> reverse conj_tac
      >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
      gen_tac >> simp[entry_cfg_preserves_bind, entry_cfg_preserves_emit_op,
                     entry_cfg_preserves_emit_void, is_terminator_def]) >>
  simp[entry_cfg_preserves_emit_void, is_terminator_def]
QED
Resume entry_cfg_decode_preserves_mutual[array]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  simp[Once (cj 3 compile_abi_decode_to_buf_def)] >>
  ntac 3 (irule entry_cfg_preserves_bind >> reverse conj_tac
    >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
    gen_tac >> BETA_TAC) >>
  irule entry_cfg_preserves_ignore_bind >> reverse conj_tac
  >- (irule entry_cfg_preserves_ignore_bind >> conj_tac
      >- (Cases_on `hi = Lit 0w` >>
          simp[entry_cfg_preserves_return] >>
          ntac 2 (irule entry_cfg_preserves_bind >> reverse conj_tac
            >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
            gen_tac >> BETA_TAC) >>
          simp[entry_cfg_preserves_bind, entry_cfg_preserves_emit_op,
               entry_cfg_preserves_emit_void, is_terminator_def]) >>
      irule entry_cfg_preserves_bind >> reverse conj_tac
      >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
      gen_tac >> BETA_TAC >>
      irule entry_cfg_preserves_ignore_bind >> reverse conj_tac
      >- (Cases_on `elem_is_dyn \/ dec_info_needs_clamp ei` >> gvs[] >>
          simp[entry_cfg_preserves_bind, entry_cfg_preserves_ignore_bind,
               entry_cfg_preserves_alloc_buffer, entry_cfg_preserves_emit_op,
               entry_cfg_preserves_emit_void, is_terminator_def]) >>
      simp[entry_cfg_preserves_emit_void, is_terminator_def]) >>
  simp[entry_cfg_preserves_emit_void, is_terminator_def]
QED
Resume entry_cfg_decode_preserves_mutual[complex]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  Cases_on `hi = Lit 0w` >> gvs[] >>
  simp[Once (cj 4 compile_abi_decode_to_buf_def),
       entry_cfg_preserves_bind, entry_cfg_preserves_ignore_bind,
       entry_cfg_preserves_emit_op, entry_cfg_preserves_emit_void,
       is_terminator_def] >>
  irule entry_cfg_preserves_bind >> reverse conj_tac
  >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
  gen_tac >> simp[entry_cfg_preserves_bind, entry_cfg_preserves_ignore_bind,
                  entry_cfg_preserves_emit_op, entry_cfg_preserves_emit_void,
                  is_terminator_def]
QED
Resume entry_cfg_decode_preserves_mutual[nil]:
  simp[Once compile_abi_decode_to_buf_def, entry_cfg_preserves_return]
QED
Resume entry_cfg_decode_preserves_mutual[cons]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  simp[Once (cj 6 compile_abi_decode_to_buf_def), entry_cfg_preserves_bind,
       entry_cfg_preserves_ignore_bind, entry_cfg_preserves_getelemptr_abi,
       entry_cfg_preserves_emit_op, is_terminator_def]
QED
Resume entry_cfg_decode_preserves_mutual[loop]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  irule entry_cfg_preserves_decode_dyn_loop >> simp[]
QED
Finalise entry_cfg_decode_preserves_mutual

Theorem entry_cfg_preserves_decode_to_buf:
  entry_cfg_preserves (compile_abi_decode_to_buf dst src CALLDATALOAD hi info)
Proof
  metis_tac[entry_cfg_decode_preserves_mutual]
QED

Theorem entry_cfg_preserves_decode_complex_elems:
  entry_cfg_preserves
    (compile_abi_decode_complex_elems dst src CALLDATALOAD hi elems ao vo)
Proof
  metis_tac[entry_cfg_decode_preserves_mutual]
QED

Theorem entry_cfg_preserves_decode_loop:
  entry_cfg_preserves
    (compile_abi_decode_dyn_loop dst src CALLDATALOAD hi ei asz msz ip cnt)
Proof
  metis_tac[entry_cfg_decode_preserves_mutual]
QED

Theorem entry_cfg_decode_to_buf_cert:
  compile_state_ok st /\ ~block_is_terminated st /\
  compile_abi_decode_to_buf dst src CALLDATALOAD hi info st = ((),st') ==>
  entry_cfg_cert st st' (bound_labels st' DIFF bound_labels st) {} F
Proof
  strip_tac >>
  `entry_cfg_cert st st {} {} F` by metis_tac[entry_cfg_cert_initial] >>
  `entry_cfg_preserves (compile_abi_decode_to_buf dst src CALLDATALOAD hi info)`
    by simp[entry_cfg_preserves_decode_to_buf] >>
  drule_all entry_cfg_preserves_apply >> strip_tac >>
  gvs[entry_cfg_cert_def]
QED
