(* Chronological occurrence provenance: inherited syntax may be arbitrary. *)
Theory compilerOccurrences
Ancestors
  compileEnv context emitHelper venomInst list rich_list arithmetic

Definition compiler_chrono_def:
  compiler_chrono st =
    FLAT (MAP (\bb. bb.bb_instructions) (REVERSE st.cs_blocks)) ++
    st.cs_current_insts
End

Definition compiler_emitted_def:
  compiler_emitted first last =
    DROP (LENGTH (compiler_chrono first)) (compiler_chrono last)
End

(* Parameterizing shape keeps generic provenance below decoder syntax. *)
Definition compiler_emits_def:
  compiler_emits shape first last <=>
    ?xs. compiler_chrono last = compiler_chrono first ++ xs /\
      first.cs_next_id <= last.cs_next_id /\
      EVERY (\i. first.cs_next_id <= i.inst_id /\
        i.inst_id < last.cs_next_id /\ shape i) xs
End

Theorem compiler_emits_refl[simp]:
  compiler_emits shape st st
Proof
  simp[compiler_emits_def] >> qexists_tac `[]` >> simp[]
QED

Theorem compiler_emits_suffix:
  compiler_emits shape first last ==>
  compiler_chrono last = compiler_chrono first ++ compiler_emitted first last /\
  EVERY (\i. first.cs_next_id <= i.inst_id /\
    i.inst_id < last.cs_next_id /\ shape i) (compiler_emitted first last)
Proof
  rw[compiler_emits_def, compiler_emitted_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem compiler_emitted_concat:
  compiler_chrono middle = compiler_chrono first ++ xs /\
  compiler_chrono last = compiler_chrono middle ++ ys ==>
  compiler_emitted first last = xs ++ ys
Proof
  strip_tac >>
  pure_asm_rewrite_tac[compiler_emitted_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  REFL_TAC
QED

Theorem compiler_emits_trans:
  compiler_emits shape first middle /\ compiler_emits shape middle last ==>
  compiler_emits shape first last
Proof
  rw[compiler_emits_def] >> qexists_tac `xs ++ xs'` >>
  simp[APPEND_ASSOC, EVERY_APPEND] >>
  gvs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem compiler_emits_return:
  compiler_emits shape st (SND (comp_return v st))
Proof
  simp[comp_return_def]
QED

Theorem compiler_emits_bind:
  (!st. compiler_emits shape st (SND (f st))) /\
  (!v st. compiler_emits shape st (SND (g v st))) ==>
  compiler_emits shape st (SND (comp_bind f g st))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule compiler_emits_trans >> metis_tac[pairTheory.SND]
QED

Theorem compiler_emits_ignore_bind:
  (!st. compiler_emits shape st (SND (f st))) /\
  (!st. compiler_emits shape st (SND (g st))) ==>
  compiler_emits shape st (SND (comp_ignore_bind f g st))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_emits_bind >> simp[]
QED

Theorem compiler_chrono_emit[simp]:
  compiler_chrono (SND (emit i st)) = compiler_chrono st ++ [i]
Proof
  simp[emit_def, compiler_chrono_def, APPEND_ASSOC]
QED

Theorem compiler_chrono_new_block[simp]:
  compiler_chrono (SND (new_block name st)) = compiler_chrono st
Proof
  simp[new_block_def, compiler_chrono_def, MAP_APPEND, FLAT_APPEND,
       APPEND_ASSOC]
QED

Theorem compiler_emits_new_block:
  compiler_emits shape st (SND (new_block name st))
Proof
  simp[compiler_emits_def, new_block_def] >> qexists_tac `[]` >>
  simp[compiler_chrono_def, MAP_APPEND, FLAT_APPEND, APPEND_ASSOC]
QED

Theorem compiler_emits_fresh_label:
  compiler_emits shape st (SND (fresh_label name st))
Proof
  simp[fresh_label_def, compiler_emits_def, compiler_chrono_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem compiler_emits_fresh_var:
  compiler_emits shape st (SND (fresh_var st))
Proof
  simp[fresh_var_def, compiler_emits_def, compiler_chrono_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem compiler_emits_fresh_id:
  compiler_emits shape st (SND (fresh_id st))
Proof
  simp[fresh_id_def, compiler_emits_def, compiler_chrono_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem compiler_emits_emit_inst:
  shape (mk_inst st.cs_next_id opc ops outs) ==>
  compiler_emits shape st (SND (emit_inst opc ops outs st))
Proof
  strip_tac >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def, compiler_emits_def, compiler_chrono_def] >>
  simp[mk_inst_def, APPEND_ASSOC]
QED

Theorem compiler_emits_emit_op:
  shape (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) ==>
  compiler_emits shape st (SND (emit_op opc ops st))
Proof
  strip_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def, compiler_emits_def, compiler_chrono_def] >>
  simp[mk_inst_def, APPEND_ASSOC]
QED

Theorem compiler_emits_emit_void:
  shape (mk_inst st.cs_next_id opc ops []) ==>
  compiler_emits shape st (SND (emit_void opc ops st))
Proof
  strip_tac >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def, compiler_emits_def, compiler_chrono_def] >>
  simp[mk_inst_def, APPEND_ASSOC]
QED

(* In particular, these equations hold when i also occurs in old code. *)
Theorem compiler_emitted_emit_inst:
  compiler_emitted st (SND (emit_inst opc ops outs st)) =
    [mk_inst st.cs_next_id opc ops outs]
Proof
  simp[compiler_emitted_def, emit_inst_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def,
       compiler_chrono_def, DROP_APPEND]
QED

Theorem compiler_emitted_new_block:
  compiler_emitted st (SND (new_block name st)) = []
Proof
  simp[compiler_emitted_def]
QED

Theorem compiler_emits_emitted_concat:
  compiler_emits shape first middle /\ compiler_emits shape middle last ==>
  compiler_emitted first last =
    compiler_emitted first middle ++ compiler_emitted middle last
Proof
  strip_tac >>
  irule compiler_emitted_concat >>
  metis_tac[compiler_emits_suffix]
QED
Theorem compiler_chrono_extends:
  cs_extends first last ==> isPREFIX (compiler_chrono first) (compiler_chrono last)
Proof
  rw[cs_extends_def] >> Cases_on `new` using SNOC_CASES >>
  gvs[compiler_chrono_def, IS_PREFIX_APPEND, REVERSE_SNOC, MAP_APPEND, FLAT_APPEND] >>
  simp[GSYM APPEND_ASSOC]
QED

Theorem compiler_emitted_subsegment:
  cs_extends first child /\ cs_extends child child_end /\ cs_extends child_end last ==>
  !i. MEM i (compiler_emitted child child_end) ==> MEM i (compiler_emitted first last)
Proof
  strip_tac >> imp_res_tac compiler_chrono_extends >>
  simp_tac bool_ss [compiler_emitted_def] >>
  qabbrev_tac `a = compiler_chrono first` >>
  qabbrev_tac `b = compiler_chrono child` >>
  qabbrev_tac `c = compiler_chrono child_end` >>
  qabbrev_tac `d = compiler_chrono last` >>
  qpat_x_assum `Abbrev (a = _)` kall_tac >>
  qpat_x_assum `Abbrev (b = _)` kall_tac >>
  qpat_x_assum `Abbrev (c = _)` kall_tac >>
  qpat_x_assum `Abbrev (d = _)` kall_tac >>
  gvs[IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, MEM_APPEND]
QED
