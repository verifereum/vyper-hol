(* Caller-target confinement for the two ABI encoder array loops. *)
Theory createSizeEncodeLoopCode
Ancestors
  createSizeCutOpens createSizeCutCode abiEncoder context compileEnv emitHelper
  venomInst pair pred_set

Theorem encode_add_open[local]:
  (!v s. create_cut_code exits s (SND (k v s)) /\
         opened SUBSET set (added_labels s (SND (k v s)))) ==>
  create_cut_code exits a (SND (comp_bind (new_block l) k a)) /\
  (l INSERT opened) SUBSET set (added_labels a (SND (comp_bind (new_block l) k a)))
Proof
  strip_tac >> pure_once_rewrite_tac[INSERT_SING_UNION] >>
  irule create_cut_opens_bind >>
  simp[] >> Cases_on `new_block l a` >> simp[] >>
  drule externalEntryShapeTheory.added_labels_new_block >> simp[]
QED

val encode_primitive_rules =
  [LET_THM, create_cut_code_emit_inst, create_cut_code_emit_op,
   create_cut_code_emit_void, create_cut_targets_def, DISJ_IMP_THM];

fun encode_straight ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ encode_primitive_rules)),
              irule create_cut_code_bind, conj_tac]);

Theorem encode_static_info[local,simp]:
  create_cut_code exits a (SND (compile_abi_encode_static_info dst src ei a))
Proof
  Cases_on `ei` >>
  encode_straight [compile_abi_encode_static_info_def, compile_abi_encode_static_def,
                   comp_ignore_bind_def]
QED

Theorem encode_label_bind[local]:
  (!l s. create_cut_code exits s (SND (k l s))) ==>
  create_cut_code exits a (SND (comp_bind (fresh_label suffix) k a))
Proof
  strip_tac >> irule create_cut_code_bind >> simp[]
QED

fun encode_labels labels =
  map_every (fn l => match_mp_tac encode_label_bind >>
                 qx_gen_tac l >> gen_tac >> BETA_TAC) labels;

(* Keep the three destinations pending until their actual block openings.
   Each ordinary bind preserves the obligations on the remaining suffix. *)
val encode_loop =
  match_mp_tac (Q.INST [`opened` |-> `{h_lbl;b_lbl;x_lbl}`, `pending` |-> `{h_lbl;b_lbl;x_lbl}`]
                       create_cut_opens_close) >>
  (conj_tac >-
     (rpt (FIRST [match_mp_tac encode_add_open,
                  match_mp_tac create_cut_opens_bind_keep >>
                    (conj_tac >-
                       (gen_tac >>
                        FIRST [rename1 `emit_inst JNZ [c; Label _; Label _] [] _` >>
                                 Cases_on `c` >> simp encode_primitive_rules,
                               encode_straight []]))] >>
           rpt gen_tac >> BETA_TAC) >>
      simp encode_primitive_rules)) >>
  simp[];

Theorem create_encode_dyn_static_loop_cut_code:
  !a. create_cut_code {} a
    (SND (compile_abi_encode_dyn_static_loop dst src ei asz msz len a))
Proof
  gen_tac >> simp[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def, LET_THM] >>
  ntac 2 (irule create_cut_code_bind >>
    (conj_tac >- encode_straight [compile_alloc_buffer_def]) >> BETA_TAC) >>
  encode_labels [`h_lbl`, `b_lbl`, `x_lbl`] >>
  encode_loop
QED

Theorem create_encode_dyn_loop_case:
  (!d s a. create_cut_code {} a (SND (compile_abi_encode_to_buf d s ei a))) ==>
  !a. create_cut_code {} a
    (SND (compile_abi_encode_dyn_loop dst src ei asz msz len a))
Proof
  strip_tac >>
  `!exits d s a. create_cut_code exits a (SND (compile_abi_encode_to_buf d s ei a))` by
    (rpt gen_tac >> irule create_cut_code_weaken >> qexists_tac `{}` >> simp[]) >>
  gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[comp_ignore_bind_def, LET_THM] >>
  ntac 5 (irule create_cut_code_bind >>
    (conj_tac >- encode_straight [compile_alloc_buffer_def]) >> BETA_TAC) >>
  encode_labels [`h_lbl`, `b_lbl`, `x_lbl`] >>
  encode_loop
QED
