(* A source-type condition for recursive readable child heads. It excludes the
   dynamic zero-length fixed-array edge explicitly and contains no execution. *)
Theory abiDecoderReadableTypes
Ancestors
  compileEnv vyperAST vyperABI contractABI finite_map list rich_list pred_set arithmetic pair

Definition abi_decoder_readable_head_def:
  abi_decoder_readable_head env ty <=>
    is_dynamic (vyper_to_abi_type env ty) ==>
      !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem
End

Definition abi_decoder_readable_type_def:
  abi_decoder_readable_type env (BaseT bt) = abi_decoder_readable_head env (BaseT bt) /\
  abi_decoder_readable_type env (FlagT nsid) = abi_decoder_readable_head env (FlagT nsid) /\
  abi_decoder_readable_type env (ArrayT ty bound) =
    (abi_decoder_readable_head env (ArrayT ty bound) /\ abi_decoder_readable_type env ty) /\
  abi_decoder_readable_type env (TupleT tys) =
    (abi_decoder_readable_head env (TupleT tys) /\ EVERY (abi_decoder_readable_type env) tys) /\
  abi_decoder_readable_type env (StructT nsid) =
    (abi_decoder_readable_head env (StructT nsid) /\
     case FLOOKUP env nsid of
       SOME (StructArgs args) => EVERY (abi_decoder_readable_type (env \\ nsid) o SND) args
     | _ => F) /\
  abi_decoder_readable_type env NoneT = F
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (\(env,ty). (CARD (FDOM env), type_size ty))` >>
  rw[FLOOKUP_DEF] >> disj1_tac >> CCONTR_TAC >> fs[]
End

Theorem abi_decoder_readable_type_head:
  !env ty. abi_decoder_readable_type env ty ==>
    (is_dynamic (vyper_to_abi_type env ty) ==>
      !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[Once abi_decoder_readable_type_def, abi_decoder_readable_head_def]
QED

Theorem abi_decoder_readable_array_iff:
  abi_decoder_readable_type env (ArrayT ty bound) <=>
    abi_decoder_readable_type env ty /\ abi_decoder_readable_head env (ArrayT ty bound)
Proof
  simp[Once abi_decoder_readable_type_def, CONJ_COMM]
QED

Theorem abi_decoder_readable_tuple_iff:
  abi_decoder_readable_type env (TupleT tys) <=> EVERY (abi_decoder_readable_type env) tys
Proof
  simp[Once abi_decoder_readable_type_def, abi_decoder_readable_head_def,
    Once vyper_to_abi_type_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem abi_decoder_readable_struct_iff:
  FLOOKUP env nsid = SOME (StructArgs args) ==>
  (abi_decoder_readable_type env (StructT nsid) <=>
    EVERY (abi_decoder_readable_type (env \\ nsid)) (MAP SND args))
Proof
  strip_tac >> simp[Once abi_decoder_readable_type_def, abi_decoder_readable_head_def,
    Once vyper_to_abi_type_def, EVERY_MAP, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem abi_decoder_readable_base:
  !bt. abi_decoder_readable_type env (BaseT bt)
Proof
  Cases >> simp[Once abi_decoder_readable_type_def, abi_decoder_readable_head_def,
    vyper_to_abi_type_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[]
QED

Theorem abi_decoder_readable_flag:
  abi_decoder_readable_type env (FlagT nsid)
Proof
  simp[Once abi_decoder_readable_type_def, abi_decoder_readable_head_def, vyper_to_abi_type_def]
QED

Theorem abi_decoder_readable_dynamic_array_iff:
  abi_decoder_readable_type env (ArrayT ty (Dynamic maxn)) <=> abi_decoder_readable_type env ty
Proof
  simp[abi_decoder_readable_array_iff, abi_decoder_readable_head_def, vyper_to_abi_type_def]
QED

Theorem abi_decoder_readable_positive_fixed_array:
  0 < n /\ abi_decoder_readable_type env ty ==>
    abi_decoder_readable_type env (ArrayT ty (Fixed n))
Proof
  Cases_on `n` >>
  simp[abi_decoder_readable_array_iff, abi_decoder_readable_head_def, vyper_to_abi_type_def]
QED

Theorem abi_decoder_readable_members_head:
  EVERY (abi_decoder_readable_type env) tys ==>
  EVERY (\ty. is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) tys
Proof
  rw[EVERY_MEM] >> irule abi_decoder_readable_type_head >> metis_tac[]
QED

Theorem abi_decoder_readable_list_relation:
  !xs ys. LIST_REL (\x y. P x ==> R x y) xs ys /\ EVERY P xs ==> LIST_REL R xs ys
Proof
  Induct_on `xs` >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_READABLE_TYPES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI readable source types not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderReadableTypes");
