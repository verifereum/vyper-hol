(* Caller-target confinement for the recursive ABI to-buffer encoder. *)
Theory createSizeEncodeCoreCode
Ancestors
  createSizeEncodeLoopCode createSizeCutOpens createSizeCutCode abiEncoder context compileEnv
  emitHelper venomInst pair pred_set arithmetic

val encode_core_bind =
  Q.INST [`exits` |-> `{}`] create_cut_code_bind_uniform;

val encode_atoms =
  [create_cut_code_emit_op, create_cut_code_emit_void, create_cut_targets_def,
   LET_THM, comp_ignore_bind_def];

fun encode_walk ths =
  rpt gen_tac >>
  rpt (FIRST [CHANGED_TAC (simp (ths @ encode_atoms)),
              match_mp_tac encode_core_bind >> conj_tac] >>
       rpt gen_tac >> BETA_TAC);

Theorem encode_core_family:
  (!dst cp info dyn off dp a.
    create_cut_code {} a (SND (compile_abi_encode_child dst cp info dyn off dp a))) /\
  (!dst src info a.
    create_cut_code {} a (SND (compile_abi_encode_to_buf dst src info a))) /\
  (!dst src elems so ho dp a.
    create_cut_code {} a (SND (compile_abi_encode_complex_elems dst src elems so ho dp a))) /\
  (!dst src info asz msz len a.
    create_cut_code {} a (SND (compile_abi_encode_dyn_loop dst src info asz msz len a)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty_tuple"
  >- suspend "tuple"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume encode_core_family[child]:
  rpt gen_tac >> strip_tac >> rename1 `compile_abi_encode_child _ _ _ dyn _ _ _` >>
  Cases_on `dyn` >> gvs[] >>
  once_rewrite_tac[compile_abi_encode_child_def] >> encode_walk []
QED

Resume encode_core_family[word]:
  rpt gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  encode_walk [compile_abi_encode_static_def]
QED

Resume encode_core_family[bytes]:
  rpt gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >> encode_walk []
QED

Resume encode_core_family[copy]:
  rpt gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >> encode_walk []
QED

Resume encode_core_family[array]:
  rpt gen_tac >> strip_tac >> rename1 `AbiDynArray _ _ _ dyn` >>
  Cases_on `dyn` >> gvs[] >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  encode_walk [compile_alloc_buffer_def, create_encode_dyn_static_loop_cut_code]
QED

Resume encode_core_family[empty_tuple]:
  rpt gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >> simp[]
QED

Resume encode_core_family[tuple]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >> simp[LET_THM] >>
  IF_CASES_TAC >> encode_walk [compile_alloc_buffer_def] >> gvs[]
QED

Resume encode_core_family[nil]:
  rpt gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >> simp[]
QED

Resume encode_core_family[cons]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >> encode_walk [] >>
  fs[ADD_COMM]
QED

Resume encode_core_family[loop]:
  rpt gen_tac >> strip_tac >>
  irule create_encode_dyn_loop_case >>
  rpt gen_tac >> first_x_assum irule >> simp[]
QED

Finalise encode_core_family[local]

Theorem create_encode_to_buf_cut_code:
  !a. create_cut_code {} a (SND (compile_abi_encode_to_buf dst src info a))
Proof
  simp[encode_core_family]
QED
