(* Bounds for source slots inside recursive encoder input windows. *)
Theory abiEncoderInputLayout
Ancestors
  abiEncoderInput valueEncoding list rich_list arithmetic

Theorem abi_encoder_member_span_append:
  abi_encoder_member_span (xs ++ ys) = abi_encoder_member_span xs + abi_encoder_member_span ys
Proof
  simp[abi_encoder_member_span_def, MAP_APPEND, SUM_APPEND]
QED

Theorem abi_encoder_prefix_sum_bound:
  !f xs i. i < LENGTH xs ==>
    SUM (MAP f (TAKE i xs)) + f (EL i xs) <= SUM (MAP f xs)
Proof
  Induct_on `xs` >- simp[] >> rpt gen_tac >> Cases_on `i` >> simp[] >>
  strip_tac >> first_x_assum drule >> disch_then (qspec_then `f` mp_tac) >> decide_tac
QED

Theorem abi_encoder_member_slot_bound:
  i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
  abi_encoder_member_span (TAKE i infos) + mem_sz <= abi_encoder_member_span infos
Proof
  strip_tac >>
  mp_tac (Q.ISPEC `(\(_,_,mem_sz,_). mem_sz):abi_enc_info # num # num # bool -> num`
    abi_encoder_prefix_sum_bound) >>
  disch_then (qspecl_then [`infos`, `i`] mp_tac) >>
  asm_simp_tac (srw_ss()) [abi_encoder_member_span_def]
QED

Theorem abi_encoder_array_slot_bound:
  (i:num) < ncount /\ 32 + ncount * mem_sz <= cap ==>
  32 + i * mem_sz + mem_sz <= cap
Proof
  strip_tac >> `(i+1)*mem_sz <= ncount*mem_sz` by
    simp[LE_MULT_RCANCEL] >> pop_assum mp_tac >>
  PURE_REWRITE_TAC [RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> strip_tac >> decide_tac
QED

Theorem abi_encoder_array_input_iff:
  abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn) at av sb cap mem <=>
  ?ct avs. at = Array NONE ct /\ av = ListV avs /\
    has_type (Array NONE ct) (ListV avs) /\
    abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
    32 + LENGTH avs * mem_sz <= cap /\ mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      abi_encoder_input ei ct (EL i avs) (sb+32+i*mem_sz) mem_sz mem)
Proof
  simp[Once abi_encoder_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_complex_input_iff:
  abi_encoder_input (AbiComplex infos) at av sb cap mem <=>
  ?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats /\ has_type at (ListV avs) /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    abi_encoder_member_span infos <= cap /\
    (!i ei abi_sz mem_sz dyn. i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
      abi_encoder_input ei (EL i ats) (EL i avs)
        (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem)
Proof
  simp[Once abi_encoder_input_cases] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_INPUT_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder input layout not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderInputLayout");
