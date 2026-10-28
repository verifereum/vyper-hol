(* TOP-LEVEL: the fields half of native semantic induction records each
   child assertion at its actual source-memory stride. Unrolled aggregates
   consume the head; runtime array loops select any live element. *)
Theory abiNativeFields
Ancestors
  abiNativeEncodingDefs abiMemoryEncoding compileEnv list rich_list pair arithmetic

Definition abi_native_fields_def:
  abi_native_fields [] source reference fields = (fields = []) /\
  abi_native_fields ((info,abi_sz,mem_sz,is_dyn)::entries) source reference fields =
    case fields of
      [] => F
    | (flag,payload)::remaining =>
        flag = is_dyn /\ abi_native_encoder info source mem_sz reference payload /\
        abi_native_fields entries (source + mem_sz) reference remaining
End

Theorem abi_native_fields_cons:
  !info abi_sz mem_sz is_dyn entries source reference flag payload fields.
    abi_native_fields ((info,abi_sz,mem_sz,is_dyn)::entries) source reference ((flag,payload)::fields) <=>
    flag = is_dyn /\ abi_native_encoder info source mem_sz reference payload /\
    abi_native_fields entries (source + mem_sz) reference fields
Proof
  simp[abi_native_fields_def]
QED

Theorem abi_native_fields_length:
  !entries source reference fields.
    abi_native_fields entries source reference fields ==> LENGTH entries = LENGTH fields
Proof
  Induct_on `entries` >- simp[abi_native_fields_def] >>
  simp_tac bool_ss [FORALL_PROD] >> rpt gen_tac >> Cases_on `fields` >>
  simp[abi_native_fields_def, pair_CASE_def] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem abi_native_array_element:
  !fields info abi_sz mem_sz is_dyn source reference index.
    abi_native_fields (REPLICATE (LENGTH fields) (info,abi_sz,mem_sz,is_dyn)) source reference fields /\
    index < LENGTH fields ==>
    abi_native_encoder info (source + index * mem_sz) mem_sz reference (SND (EL index fields))
Proof
  Induct_on `fields` >- simp[] >> rpt gen_tac >> Cases_on `index`
  >- simp[abi_native_fields_def, REPLICATE, pair_CASE_def] >>
  simp_tac (srw_ss()) [REPLICATE, abi_native_fields_def, pair_CASE_def] >> strip_tac >>
  first_x_assum drule_all >>
  rename1 `abi_native_encoder info (source + SUC index * mem_sz) mem_sz reference (SND (EL index fields))` >>
  `source + SUC index * mem_sz = source + mem_sz + index * mem_sz` by
    (simp_tac bool_ss [MULT_CLAUSES] >> decide_tac) >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native recursive field induction assertions: " ^ name)
  end) (DB.thms "abiNativeFields")
