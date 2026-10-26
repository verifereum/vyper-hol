(* Establish static array input from every source slot, including default slots. *)
Theory abiEncoderStaticInput
Ancestors
  abiEncoderInput abiEncoderMemory abiStaticAggregateProps abiStaticSparseProps
  valueEncoding valueEncodingProps vyperABI contractABI list rich_list arithmetic

Theorem abi_encoder_static_chunk_lengths:
  !avs. ~is_dynamic ct /\ static_length ct = esz /\ have_type ct avs ==>
    EVERY (\av. LENGTH (enc ct av) = esz) avs
Proof
  Induct >- simp[] >> qx_gen_tac `av` >> simp[has_type_def] >> rpt strip_tac >>
  `LENGTH (enc ct av) = esz` by (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  simp[]
QED

Theorem abi_encoder_static_chunks_tail:
  (!i. i < LENGTH (av::avs) ==>
    mem_bytes_at (sb+i*esz) esz mem = enc ct (EL i (av::avs))) ==>
  !i. i < LENGTH avs ==>
    mem_bytes_at (sb+esz+i*esz) esz mem = enc ct (EL i avs)
Proof
  strip_tac >> qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[MULT_CLAUSES, AC ADD_COMM ADD_ASSOC]
QED

Theorem abi_encoder_static_chunks:
  !avs sb. EVERY (\av. LENGTH (enc ct av) = esz) avs /\
    (!i. i < LENGTH avs ==> mem_bytes_at (sb+i*esz) esz mem = enc ct (EL i avs)) ==>
  mem_bytes_at sb (LENGTH avs * esz) mem = FLAT (MAP (enc ct) avs)
Proof
  Induct_on `avs` >- simp[mem_bytes_at_def] >>
  qx_gen_tac `av` >> rpt gen_tac >> strip_tac >>
  `mem_bytes_at sb esz mem = enc ct av` by
    (qpat_x_assum `!i. i < LENGTH (av::avs) ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `EVERY (\av. LENGTH (enc ct av) = esz) avs` by fs[] >>
  drule abi_encoder_static_chunks_tail >> strip_tac >>
  `mem_bytes_at (sb+esz) (LENGTH avs*esz) mem = FLAT (MAP (enc ct) avs)` by
    (qpat_x_assum `!off. EVERY _ avs /\ _ ==> _` irule >>
     asm_simp_tac bool_ss []) >>
  simp[Once abi_encoder_mem_split, MULT_CLAUSES, ADD_ASSOC] >>
  qpat_x_assum `mem_bytes_at (sb+esz) _ mem = _` mp_tac >>
  simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM]
QED

Theorem abi_encoder_static_array_input:
  has_type (Array (SOME n) ct) (ListV avs) /\ ~is_dynamic ct /\
  static_length ct = esz /\ n*esz <= cap /\
  (!i. i < n ==> mem_bytes_at (sb+i*esz) esz mem = enc ct (EL i avs)) ==>
  abi_encoder_input (AbiCopy (n*esz)) (Array (SOME n) ct) (ListV avs) sb cap mem
Proof
  strip_tac >>
  `LENGTH avs = n /\ have_type ct avs` by fs[has_type_def, valid_length_def] >>
  drule_all abi_encoder_static_chunk_lengths >> strip_tac >>
  `mem_bytes_at sb (n*esz) mem = FLAT (MAP (enc ct) avs)` by
    (mp_tac (Q.INST [`avs` |-> `avs`, `sb` |-> `sb`] (SPEC_ALL abi_encoder_static_chunks)) >>
     asm_simp_tac bool_ss []) >>
  simp[abi_encoder_input_copy_iff, is_dynamic_def, static_length_def, enc_static_array]
QED

Theorem abi_encoder_sparse_default:
  !n sparse avs i.
  vyper_to_abi_sparse env ty tv n sparse = SOME avs /\ i < n /\ ALOOKUP sparse i = NONE ==>
  EL i avs = default_to_abi tv
Proof
  Induct_on `n` >- simp[] >> rpt gen_tac >>
  simp[Once vyper_to_abi_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac canonical_sparse_length >>
  Cases_on `i = n` >> gvs[EL_APPEND_EQN] >>
  rename1 `vyper_to_abi_sparse env ty tv (LENGTH prefix) sparse = SOME prefix` >>
  `i < LENGTH prefix` by decide_tac >> first_x_assum drule_all >> simp[]
QED

Theorem abi_encoder_sparse_static_input:
  vyper_to_abi_sparse env ty tv n sparse = SOME avs /\
  has_type (Array (SOME n) (vyper_to_abi_type env ty)) (ListV avs) /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ static_length (vyper_to_abi_type env ty) = esz /\
  n*esz <= cap /\
  (!i. i < n ==> mem_bytes_at (sb+i*esz) esz mem =
    (case ALOOKUP sparse i of
       NONE => enc (vyper_to_abi_type env ty) (default_to_abi tv)
     | SOME v => case vyper_to_abi env ty v of
         NONE => [] | SOME av => enc (vyper_to_abi_type env ty) av)) ==>
  abi_encoder_input (AbiCopy (n*esz)) (Array (SOME n) (vyper_to_abi_type env ty))
    (ListV avs) sb cap mem
Proof
  strip_tac >> irule abi_encoder_static_array_input >> asm_simp_tac bool_ss [] >>
  qx_gen_tac `i` >> strip_tac >> Cases_on `ALOOKUP sparse i`
  >- (drule_all abi_encoder_sparse_default >> strip_tac >>
      qpat_x_assum `!i. i < n ==> _` (qspec_then `i` mp_tac) >> asm_simp_tac (srw_ss()) []) >>
  rename1 `ALOOKUP sparse i = SOME elt` >>
  drule_all canonical_sparse_lookup >> strip_tac >>
  qpat_x_assum `!i. i < n ==> _` (qspec_then `i` mp_tac) >> asm_simp_tac (srw_ss()) []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_STATIC_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder static input not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderStaticInput");
