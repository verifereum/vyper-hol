Theory exprSimAbiDecodeShape
Ancestors
  exprSimAbiDecodeTrace exprSimAbiDecodePrims exprSimAbiGasBridge
  fragExec exprLoweringProps compileEnv venomInst list rich_list sorting emitHelperProps

Definition decode_instructions_def:
  (decode_instructions [] = []) /\
  (decode_instructions (DecodeEmit i::es) = i::decode_instructions es) /\
  (decode_instructions (DecodeSwitch l::es) = decode_instructions es)
End

Definition decode_switches_def:
  (decode_switches [] = []) /\
  (decode_switches (DecodeEmit i::es) = decode_switches es) /\
  (decode_switches (DecodeSwitch l::es) = l::decode_switches es)
End

Theorem decode_instructions_append:
  !es fs. decode_instructions (es ++ fs) =
    decode_instructions es ++ decode_instructions fs
Proof
  Induct >> simp[decode_instructions_def] >> Cases_on `h` >>
  simp[decode_instructions_def]
QED

Theorem decode_switches_append:
  !es fs. decode_switches (es ++ fs) =
    decode_switches es ++ decode_switches fs
Proof
  Induct >> simp[decode_switches_def] >> Cases_on `h` >>
  simp[decode_switches_def]
QED

Theorem decode_frag_code_emit:
  cs_extends sa sb ==>
  frag_code sa (decode_step (DecodeEmit i) sb) = frag_code sa sb ++ [i]
Proof
  rw[cs_extends_def] >>
  `emitted_blocks sa sb = new` by
    (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new` >>
  gvs[frag_code_def, emitted_insts_def, decode_step_def, emitted_blocks_def,
      IS_PREFIX_APPEND, DROP_APPEND, TAKE_LENGTH_APPEND,
      arithmeticTheory.ADD1, APPEND_ASSOC] >>
  `LENGTH sa.cs_current_insts -
    (LENGTH l + LENGTH sa.cs_current_insts) = 0` by decide_tac >> simp[]
QED

Theorem decode_frag_code_switch:
  cs_extends sa sb ==>
  PERM (frag_code sa (decode_step (DecodeSwitch l) sb)) (frag_code sa sb)
Proof
  rw[cs_extends_def] >>
  `emitted_blocks sa sb = new` by
    (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new` >>
  gvs[frag_code_def, emitted_insts_def, decode_step_def, emitted_blocks_def,
      IS_PREFIX_APPEND, DROP_APPEND, TAKE_LENGTH_APPEND,
      arithmeticTheory.ADD1, APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, PERM_APPEND_IFF, PERM_APPEND]
QED

Theorem decode_replay_frag_code_aux:
  !es sa sb. cs_extends sa sb ==>
    PERM (frag_code sa (decode_replay es sb))
         (frag_code sa sb ++ decode_instructions es)
Proof
  Induct >> simp[decode_replay_def, decode_instructions_def] >>
  rpt gen_tac >> strip_tac >>
  `cs_extends sa (decode_step h sb)` by
    metis_tac[cs_extends_trans, decode_step_extends] >>
  first_x_assum drule >> Cases_on `h` >>
  simp[decode_instructions_def, decode_frag_code_emit, APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[] >> strip_tac >>
  `PERM (frag_code sa (decode_step (DecodeSwitch s) sb) ++ decode_instructions es)
        (frag_code sa sb ++ decode_instructions es)` by
    simp[PERM_APPEND_IFF, decode_frag_code_switch] >>
  metis_tac[PERM_TRANS]
QED

Theorem decode_replay_frag_code:
  PERM (frag_code s (decode_replay es s)) (decode_instructions es)
Proof
  mp_tac (Q.SPECL [`es`, `s`, `s`] decode_replay_frag_code_aux) >>
  simp[cs_extends_refl, frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem decode_replay_frag_code_history:
  PERM (frag_code s (decode_history n (decode_replay es s)))
       (decode_instructions es)
Proof
  `frag_code s (decode_history n (decode_replay es s)) =
   frag_code s (decode_replay es s)` by
    simp[frag_code_def, emitted_blocks_def, emitted_insts_def, decode_history_def] >>
  simp[decode_replay_frag_code]
QED

Theorem decode_replay_labels_raw:
  !es s.
    (decode_replay es s).cs_current_bb ::
      MAP (\b. b.bb_label) (decode_replay es s).cs_blocks =
    REVERSE (decode_switches es) ++
      (s.cs_current_bb :: MAP (\b. b.bb_label) s.cs_blocks)
Proof
  Induct >> simp[decode_replay_def, decode_switches_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[decode_replay_def, decode_switches_def, decode_step_def, APPEND_ASSOC]
QED

Theorem decode_replay_labels:
  (decode_replay es s).cs_current_bb ::
    MAP (\b. b.bb_label) (emitted_blocks s (decode_replay es s)) =
  REVERSE (decode_switches es) ++ [s.cs_current_bb]
Proof
  mp_tac (Q.SPECL [`es`, `s`] decode_replay_labels_raw) >>
  mp_tac (Q.SPECL [`es`, `s`] decode_replay_extends) >>
  simp[cs_extends_def] >> strip_tac >>
  `emitted_blocks s (decode_replay es s) = new` by
    (irule emitted_blocks_append >> simp[]) >>
  simp[] >>
  `MAP (\b. b.bb_label) (decode_replay es s).cs_blocks =
   MAP (\b. b.bb_label) new ++ MAP (\b. b.bb_label) s.cs_blocks` by simp[] >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[APPEND_ASSOC, GSYM APPEND] >> simp[]
QED


Theorem decode_final_label_list:
  !c bs ss entry. c::bs = REVERSE ss ++ [entry] /\ ALL_DISTINCT ss ==>
    ~MEM c (FRONT bs)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bs` >- simp[] >>
  `c::FRONT (h::t) = REVERSE ss` by
    (qpat_x_assum `c::_ = _` (mp_tac o AP_TERM ``FRONT``) >>
     simp[FRONT_APPEND]) >>
  `ALL_DISTINCT (c::FRONT (h::t))` by
    metis_tac[ALL_DISTINCT_REVERSE] >>
  fs[]
QED

Theorem decode_replay_final_label:
  ALL_DISTINCT (decode_switches es) ==>
  ~MEM (decode_replay es s).cs_current_bb
    (MAP (\b. b.bb_label) (FRONT (emitted_blocks s (decode_replay es s))))
Proof
  strip_tac >> rewrite_tac[MAP_FRONT] >>
  irule decode_final_label_list >>
  qexistsl_tac [`s.cs_current_bb`, `decode_switches es`] >>
  simp[decode_replay_labels]
QED

Theorem decode_replay_final_label_history:
  ALL_DISTINCT (decode_switches es) ==>
  ~MEM (decode_history n (decode_replay es s)).cs_current_bb
    (MAP (\b. b.bb_label)
      (FRONT (emitted_blocks s (decode_history n (decode_replay es s)))))
Proof
  `emitted_blocks s (decode_history n (decode_replay es s)) =
   emitted_blocks s (decode_replay es s)` by
    simp[emitted_blocks_def, decode_history_def] >>
  simp[decode_history_def, decode_replay_final_label]
QED
