Theory immutableSection
Ancestors
  immutableEncoding compileVyper

(* Each declaration has a capacity even when its source value is absent.
   Correctness uses initialization below; this total default is computational. *)
Definition immutable_decl_bytes_def:
  immutable_decl_bytes sft imms name ty =
    let n = type_mem_bytes sft ty in
    case FLOOKUP (get_source_immutables NONE imms) name of
      NONE => REPLICATE n (0w:word8)
    | SOME (tv,v) => immutable_fit n (encode_immutable_value tv v)
End

Definition immutables_section_with_def:
  immutables_section_with sft [] imms = ([]:word8 list) /\
  immutables_section_with sft (top::rest) imms =
    (case top of
       VariableDecl _ Immutable name ty _ =>
         immutable_decl_bytes sft imms name ty ++
         immutables_section_with sft rest imms
     | _ => immutables_section_with sft rest imms)
End

Definition immutables_section_def:
  immutables_section tops imms =
    immutables_section_with
      (get_struct_fields (make_struct_fields_map tops)) tops imms
End

(* Size agreement is not a claim of source type coherence. Consumers also
   need the source typing invariant connecting the declaration to tv. *)
Definition immutables_initialized_with_def:
  immutables_initialized_with sft tops imms <=>
    !vis name ty slot.
      MEM (VariableDecl vis Immutable name ty slot) tops ==>
      ?tv v. FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
             immutable_value_admissible tv v /\
             type_memory_size tv = type_mem_bytes sft ty
End

Definition immutables_initialized_def:
  immutables_initialized tops imms <=>
    immutables_initialized_with
      (get_struct_fields (make_struct_fields_map tops)) tops imms
End

Theorem immutable_decl_bytes_length[simp]:
  LENGTH (immutable_decl_bytes sft imms name ty) = type_mem_bytes sft ty
Proof
  simp[immutable_decl_bytes_def] >>
  Cases_on `FLOOKUP (get_source_immutables NONE imms) name` >> simp[] >>
  Cases_on `x` >> simp[]
QED

Theorem immutables_section_with_append:
  !xs ys. immutables_section_with sft (xs ++ ys) imms =
    immutables_section_with sft xs imms ++ immutables_section_with sft ys imms
Proof
  Induct >> simp[immutables_section_with_def] >>
  Cases_on `h` >> simp[immutables_section_with_def] >>
  CASE_TAC >> simp[listTheory.APPEND_ASSOC]
QED

Theorem immutables_section_with_length[simp]:
  !tops. LENGTH (immutables_section_with sft tops imms) =
    compute_immutables_len sft tops
Proof
  Induct >> simp[immutables_section_with_def, compute_immutables_len_def] >>
  Cases_on `h` >> simp[immutables_section_with_def, compute_immutables_len_def] >>
  CASE_TAC >> simp[]
QED

Theorem immutables_section_length[simp]:
  LENGTH (immutables_section tops imms) =
    compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
Proof
  simp[immutables_section_def]
QED

Theorem immutable_section_concat_slice[local]:
  TAKE (LENGTH middle) (DROP (LENGTH pre) (pre ++ middle ++ post)) = middle
Proof
  Induct_on `pre` >> simp[] >>
  simp[listTheory.TAKE_APPEND1]
QED

Theorem immutables_section_with_slice:
  TAKE (type_mem_bytes sft ty)
    (DROP (compute_immutables_len sft pre)
      (immutables_section_with sft
        (pre ++ VariableDecl vis Immutable name ty slot :: post) imms)) =
  immutable_decl_bytes sft imms name ty
Proof
  simp[immutables_section_with_append, immutables_section_with_def] >>
  metis_tac[immutable_section_concat_slice, immutables_section_with_length,
            immutable_decl_bytes_length]
QED

Theorem immutables_section_no_immutables:
  (!vis name ty slot. ~MEM (VariableDecl vis Immutable name ty slot) tops) ==>
  immutables_section_with sft tops imms = []
Proof
  Induct_on `tops` >> simp[immutables_section_with_def] >>
  rpt strip_tac >> Cases_on `h` >>
  gvs[immutables_section_with_def] >> CASE_TAC >> gvs[] >> metis_tac[]
QED

Theorem immutables_section_empty[simp]:
  immutables_section [] imms = []
Proof
  simp[immutables_section_def, immutables_section_with_def]
QED

Theorem immutables_section_without_immutables:
  (!vis name ty slot. ~MEM (VariableDecl vis Immutable name ty slot) tops) ==>
  immutables_section tops imms = []
Proof
  simp[immutables_section_def, immutables_section_no_immutables]
QED

Theorem immutables_section_slice:
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
  TAKE (type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty)
    (DROP (compute_immutables_len
       (get_struct_fields (make_struct_fields_map tops)) pre)
       (immutables_section tops imms)) =
  immutable_decl_bytes (get_struct_fields (make_struct_fields_map tops))
    imms name ty
Proof
  strip_tac >> pure_rewrite_tac[immutables_section_def] >>
  qpat_x_assum `tops = _` SUBST1_TAC >>
  irule immutables_section_with_slice
QED

Theorem immutable_decl_bytes_initialized:
  immutables_initialized_with sft tops imms /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  ?tv v. FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
    immutable_value_admissible tv v /\
    type_memory_size tv = type_mem_bytes sft ty /\
    immutable_decl_bytes sft imms name ty = encode_immutable_value tv v
Proof
  rw[immutables_initialized_with_def] >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`tv`, `v`] >> simp[immutable_decl_bytes_def, immutable_fit_def,
    listTheory.TAKE_APPEND1]
QED

(* Missing values and duplicate names do not break total capacity. Constants
   in the same source map contribute no section bytes. *)
Theorem immutable_section_capacity_probe:
  LENGTH (immutables_section
    [VariableDecl Private Immutable "X" (BaseT (UintT 256)) NONE;
     VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 7))) "C" (BaseT (UintT 256)) NONE;
     VariableDecl Private Immutable "X" (BaseT (StringT 40)) NONE] []) = 128
Proof
  simp[immutables_section_length] >> EVAL_TAC
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_SECTION_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed immutable section theorem: " ^ name)
  end) (DB.thms "immutableSection");
