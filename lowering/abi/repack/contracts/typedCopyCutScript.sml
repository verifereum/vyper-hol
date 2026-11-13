(* TOP-LEVEL: a compiler action can transport an actual continuation's
   no-PHI fact backwards. This property composes through real code spans. *)
Theory typedCopyCut
Ancestors
  typedCopyContract compileAppendProps fragExec compileEnv venomExecSemantics
  venomState venomInst list rich_list pair

Definition compiler_cut_continuation_def:
  compiler_cut_continuation m <=>
    !cs ret cs' func.
      m cs = (ret,cs') /\ fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func ==>
      cut_continuation_no_phi cs func
End

Theorem compiler_cut_continuation_return:
  !x. compiler_cut_continuation (comp_return x)
Proof
  simp[compiler_cut_continuation_def, comp_return_def]
QED

Theorem compiler_cut_continuation_bind:
  !m f. cs_appends m /\ (!a. cs_appends (f a)) /\
    compiler_cut_continuation m /\ (!a. compiler_cut_continuation (f a)) ==>
    compiler_cut_continuation (comp_bind m f)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [compiler_cut_continuation_def] >>
  MAP_EVERY qx_gen_tac [`cs`, `ret`, `cs'`, `func`] >> strip_tac >>
  drule_all compile_bind_contains >>
  disch_then (qx_choose_then `value` (qx_choose_then `mid` strip_assume_tac)) >>
  `cut_continuation_no_phi mid func` by
    (qpat_x_assum `!a. compiler_cut_continuation (f a)` (qspec_then `value` mp_tac) >>
     simp_tac bool_ss [compiler_cut_continuation_def] >>
     disch_then (qspecl_then [`mid`, `ret`, `cs'`, `func`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `compiler_cut_continuation m` (mp_tac o REWRITE_RULE [compiler_cut_continuation_def]) >>
  disch_then (qspecl_then [`cs`, `value`, `mid`, `func`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem compiler_cut_continuation_ignore_bind:
  !m n. cs_appends m /\ cs_appends n /\ compiler_cut_continuation m /\ compiler_cut_continuation n ==>
    compiler_cut_continuation (comp_ignore_bind m n)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [comp_ignore_bind_def] >>
  irule compiler_cut_continuation_bind >> simp[]
QED

Theorem compiler_cut_continuation_prims:
  compiler_cut_continuation fresh_var /\
  (!suffix. compiler_cut_continuation (fresh_label suffix)) /\
  compiler_cut_continuation fresh_id
Proof
  rw[compiler_cut_continuation_def, fresh_var_def, fresh_label_def, fresh_id_def, LET_THM,
    cut_continuation_no_phi_def] >> gvs[]
QED

Theorem compiler_cut_continuation_emit:
  !inst. inst.inst_opcode <> PHI ==> compiler_cut_continuation (emit inst)
Proof
  rpt gen_tac >> DISCH_TAC >>
  rw[compiler_cut_continuation_def, emit_def, cut_continuation_no_phi_def] >>
  fs[fn_has_code_def] >>
  qmatch_assum_rename_tac `lookup_block cs.cs_current_bb func.fn_blocks = SOME bb` >>
  Cases_on `bb.bb_instructions` >> gvs[phi_prefix_length_def]
QED

Theorem compiler_cut_continuation_new_block:
  !label. compiler_cut_continuation (new_block label)
Proof
  rw[compiler_cut_continuation_def, new_block_def, LET_THM, cut_continuation_no_phi_def] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  simp[phi_prefix_length_def]
QED
