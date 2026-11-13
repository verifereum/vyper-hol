Theory concretizePtrByteHistory
Ancestors concretizePtrBytes codegenRel arithmetic pred_set

Theorem ptr_observation_interval_constant[local]:
  !n start f. start <= n /\
    (!k. start <= k /\ k < n ==> f (SUC k) = f k) ==>
    (f:num -> 'a) n = f start
Proof
  Induct >> rpt strip_tac
  >- (`start = 0` by decide_tac >> gvs[]) >>
  Cases_on `start = SUC n` >- simp[] >>
  `start <= n` by decide_tac >>
  `f (SUC n) = f n` by (first_x_assum irule >> decide_tac) >>
  `f n = f start` by (first_x_assum irule >> simp[] >> metis_tac[LESS_TRANS]) >>
  metis_tac[]
QED

Theorem ptr_bytes_agree_last_writers:
  (!x. x IN live ==> ?w. w < n /\
    read_byte x (M (SUC w)) = read_byte (reloc x) (target (SUC w)) /\
    (!k. w < k /\ k < n ==>
      read_byte x (M (SUC k)) = read_byte x (M k) /\
      read_byte (reloc x) (target (SUC k)) = read_byte (reloc x) (target k))) ==>
  ptr_bytes_agree live reloc (M n) (target n)
Proof
  simp[ptr_bytes_agree_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  `read_byte i (M n) = read_byte i (M (SUC w))` by
    (qspecl_then [`n`,`SUC w`,`\k. read_byte i (M k)`]
       mp_tac ptr_observation_interval_constant >> simp[] >>
     (impl_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac)) >> simp[]) >>
  `read_byte (reloc i) (target n) = read_byte (reloc i) (target (SUC w))` by
    (qspecl_then [`n`,`SUC w`,`\k. read_byte (reloc i) (target k)`]
       mp_tac ptr_observation_interval_constant >> simp[] >>
     (impl_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac)) >> simp[]) >>
  metis_tac[]
QED

Theorem ptr_bytes_agree_last_writer_footprints:
  (!x. x IN live ==> ?w. w < n /\
    read_byte x (M (SUC w)) = read_byte (reloc x) (target (SUC w)) /\
    (!k. w < k /\ k < n ==> x NOTIN WS k /\ reloc x NOTIN Wtarget k)) /\
  (!k i. k < n /\ i NOTIN WS k ==>
    read_byte i (M (SUC k)) = read_byte i (M k)) /\
  (!k i. k < n /\ i NOTIN Wtarget k ==>
    read_byte i (target (SUC k)) = read_byte i (target k)) ==>
  ptr_bytes_agree live reloc (M n) (target n)
Proof
  strip_tac >> irule ptr_bytes_agree_last_writers >> metis_tac[]
QED
