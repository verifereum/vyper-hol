(* Small proof-only kernels for occurrence-indexed relocation.
   No reachability or operational success is assumed by these predicates. *)
Theory o1LowerDloadRelocationKernel
Ancestors
  ptrDiscipline finite_map words pred_set codegenRel

Definition ld_value_agree_def:
  ld_value_agree (sites : (num # num) |-> (num # num # num)) h m
    (x:bytes32) y <=>
    case h of
      NONE => word_agree_except m x y
    | SOME id => ?b c z. FLOOKUP sites id = SOME (b,c,z) /\
                         y = x + n2w c - n2w b
End

Definition ld_memory_agree_def:
  ld_memory_agree (sites : (num # num) |-> (num # num # num)) lo mask sm tm <=>
    (!i. i < lo /\ i NOTIN mask ==> read_byte i sm = read_byte i tm) /\
    (!id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j < z /\ b+j NOTIN mask ==>
       read_byte (b+j) sm = read_byte (c+j) tm)
End

Theorem ld_value_agree_scalar:
  ld_value_agree sites NONE m x y <=> word_agree_except m x y
Proof
  simp[ld_value_agree_def]
QED

Theorem ld_value_agree_pointer:
  ld_value_agree sites (SOME id) m x y <=>
    ?b c z. FLOOKUP sites id = SOME (b,c,z) /\ y = x + n2w c - n2w b
Proof
  simp[ld_value_agree_def]
QED

Theorem ld_value_agree_clean:
  ld_value_agree sites NONE {} x y ==> x = y
Proof
  simp[ld_value_agree_def, word_agree_except_bits, fcpTheory.CART_EQ] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]
QED

Theorem ld_value_agree_identity:
  (!id b c z. FLOOKUP sites id = SOME (b,c,z) ==> c = b) /\
  (h = NONE \/ ?id site. h = SOME id /\ FLOOKUP sites id = SOME site) ==>
  ld_value_agree sites h m x x
Proof
  Cases_on `h`
  >- simp[ld_value_agree_def, word_agree_except_def] >>
  simp_tac bool_ss [ld_value_agree_def, optionTheory.option_CLAUSES] >>
  rpt strip_tac >> PairCases_on `site` >>
  first_x_assum drule >> disch_then SUBST_ALL_TAC >>
  qexistsl_tac [`site0`, `site0`, `site2`] >>
  asm_rewrite_tac[wordsTheory.WORD_ADD_SUB]
QED

Theorem ld_value_agree_mono:
  ld_value_agree sites h m x y /\ m SUBSET m' ==>
  ld_value_agree sites h m' x y
Proof
  Cases_on `h` >> simp[ld_value_agree_def, word_agree_except_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem ld_memory_agree_identity:
  (!id b c z. FLOOKUP sites id = SOME (b,c,z) ==> c = b) ==>
  ld_memory_agree sites lo mask mem mem
Proof
  simp[ld_memory_agree_def] >> metis_tac[]
QED

Theorem ld_memory_agree_empty:
  ld_memory_agree FEMPTY lo mask mem mem
Proof
  simp[ld_memory_agree_def]
QED

Theorem ld_memory_agree_fixed_byte:
  ld_memory_agree sites lo mask sm tm /\ i < lo /\ i NOTIN mask ==>
  read_byte i sm = read_byte i tm
Proof
  simp[ld_memory_agree_def] >> metis_tac[]
QED

Theorem ld_memory_agree_site_byte:
  ld_memory_agree sites lo mask sm tm /\
  FLOOKUP sites id = SOME (b,c,z) /\ j < z /\ b+j NOTIN mask ==>
  read_byte (b+j) sm = read_byte (c+j) tm
Proof
  simp[ld_memory_agree_def] >> metis_tac[]
QED

Theorem ld_memory_agree_mono:
  ld_memory_agree sites lo mask sm tm /\ mask SUBSET mask' ==>
  ld_memory_agree sites lo mask' sm tm
Proof
  simp[ld_memory_agree_def, SUBSET_DEF] >> metis_tac[]
QED

(* A framing interface for arbitrary writes: consumers supply byte framing
   only at protected addresses, not equality of whole memory lists. *)
Theorem ld_memory_agree_frame:
  ld_memory_agree sites lo mask sm tm /\
  (!i. i < lo /\ i NOTIN mask ==>
       read_byte i sm' = read_byte i sm /\ read_byte i tm' = read_byte i tm) /\
  (!id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j < z /\ b+j NOTIN mask ==>
       read_byte (b+j) sm' = read_byte (b+j) sm /\
       read_byte (c+j) tm' = read_byte (c+j) tm) ==>
  ld_memory_agree sites lo mask sm' tm'
Proof
  simp[ld_memory_agree_def] >> metis_tac[]
QED
