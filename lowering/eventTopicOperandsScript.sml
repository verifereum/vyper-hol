(* TOP-LEVEL: topic hashing executes with previously bound generated outputs.
   Operand lifetimes protect the input pointer and earlier saved arguments.
   Helpers expose the frame of a single emitted SSA assignment. *)
Theory eventTopicOperands
Ancestors
  valueEncodingDefs eventTopicCode eventTopicExecProps eventTopicValueProps eventTopicProps nameValueCode
  valueLoadProps valueEncoding valueEncodingProps vyperTyping vyperTypeSystem vyperValue byte
  abiFieldOperands abiStaticLoopCode context compileEnv exprLoweringProps emitHelperProps emitHelper
  venomExecSemantics venomState venomInst vyperEvent vfmState keccak words arithmetic
Libs pairLib wordsLib

Theorem emit_op_operand_frame:
  emit_op opc args cs = (op,cs') /\
  step_inst_base (mk_inst cs.cs_next_id opc args
    [STRING #"%" (toString cs.cs_next_var)]) ss =
    OK (update_var (STRING #"%" (toString cs.cs_next_var)) value ss) ==>
  ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
    eval_operand op out = SOME value /\ same_blocks cs cs' /\
    abi_operand_before cs'.cs_next_var op /\ cs.cs_next_var <= cs'.cs_next_var /\
    (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
    out with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, eval_operand_update_var] >> conj_tac
  >- (mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var + 1`] abi_operand_before_reserved) >>
      simp[compiler_var_name_def]) >>
  conj_tac >- simp[generated_update_before_operand] >> simp[update_var_def]
QED

Theorem emit_op_ADD_operands:
  emit_op ADD [a;b] cs = (op,cs') /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y ==>
  ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
    eval_operand op out = SOME (x+y) /\ same_blocks cs cs' /\
    abi_operand_before cs'.cs_next_var op /\ cs.cs_next_var <= cs'.cs_next_var /\
    (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
    out with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >> irule emit_op_operand_frame >>
  qexistsl_tac [`[a;b]`, `ADD`] >> simp[step_ADD]
QED

Theorem emit_op_MLOAD_operands:
  emit_op MLOAD [a] cs = (op,cs') /\ eval_operand a ss = SOME x ==>
  ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
    eval_operand op out = SOME (mload (w2n x) ss) /\ same_blocks cs cs' /\
    abi_operand_before cs'.cs_next_var op /\ cs.cs_next_var <= cs'.cs_next_var /\
    (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
    out with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >> irule emit_op_operand_frame >>
  qexistsl_tac [`[a]`, `MLOAD`] >> simp[step_MLOAD]
QED

Theorem emit_op_SHA3_operands:
  emit_op SHA3 [a;b] cs = (op,cs') /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y ==>
  ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
    eval_operand op out = SOME (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (read_memory (w2n x) (w2n y) ss))) /\
    same_blocks cs cs' /\ abi_operand_before cs'.cs_next_var op /\ cs.cs_next_var <= cs'.cs_next_var /\
    (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
    out with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >> irule emit_op_operand_frame >> qexistsl_tac [`[a;b]`, `SHA3`] >>
  simp[Once step_inst_base_def, mk_inst_def, read_memory_def]
QED

Theorem compile_bytestring_topic_operands:
  !ptr_op cs op cs' ss addr.
    compile_encode_log_topic ptr_op T cs = (op,cs') /\
    eval_operand ptr_op ss = SOME addr /\ abi_operand_before cs.cs_next_var ptr_op ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand op out = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64
        (read_memory (w2n (addr+32w)) (w2n (mload (w2n addr) ss)) ss))) /\
      same_blocks cs cs' /\ abi_operand_before cs'.cs_next_var op /\ cs.cs_next_var <= cs'.cs_next_var /\
      (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> simp[compile_encode_log_topic_def, comp_bind_def] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [ptr_op;Lit 32w] cs = (data_op,cs1)` >>
  rename1 `emit_op MLOAD [ptr_op] cs1 = (length_op,cs2)` >>
  imp_res_tac emit_op_extends >>
  `?ss1. run_inst_seq (emitted_insts cs cs1) ss = OK ss1 /\
    eval_operand data_op ss1 = SOME (addr+32w) /\ same_blocks cs cs1 /\
    abi_operand_before cs1.cs_next_var data_op /\ cs.cs_next_var <= cs1.cs_next_var /\
    (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old ss1 = eval_operand old ss) /\
    ss1 with vs_vars := ss.vs_vars = ss` by
    (irule emit_op_ADD_operands >> qexistsl_tac [`ptr_op`, `Lit 32w`] >> simp[eval_operand_def]) >>
  `eval_operand ptr_op ss1 = SOME addr` by
    (qpat_x_assum `!old. _ ==> eval_operand old ss1 = _` (qspec_then `ptr_op` mp_tac) >> simp[]) >>
  drule_all emit_op_MLOAD_operands >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss2` >>
  `ss1.vs_memory = ss.vs_memory /\ ss2.vs_memory = ss1.vs_memory` by
    (conj_tac >> irule assignment_frame_memory >> first_assum MATCH_ACCEPT_TAC) >>
  `eval_operand data_op ss2 = SOME (addr+32w)` by
    (qpat_x_assum `!old. _ ==> eval_operand old ss2 = _` (qspec_then `data_op` mp_tac) >> simp[]) >>
  drule_all emit_op_SHA3_operands >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs2 cs') ss2 = OK ss3` >>
  `!old. abi_operand_before cs.cs_next_var old ==> eval_operand old ss3 = eval_operand old ss` by
    (rpt gen_tac >> DISCH_TAC >>
     `abi_operand_before cs1.cs_next_var old /\ abi_operand_before cs2.cs_next_var old` by
       (conj_tac >> irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[] >> decide_tac) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `ss3` >> conj_tac
  >- (mp_tac (Q.SPECL [`cs`, `cs1`, `cs2`, `cs'`, `ss`, `ss1`, `ss2`, `ss3`]
       run_emitted_compose3) >> simp[]) >>
  simp[read_memory_def, mload_def] >> conj_tac
  >- (irule same_blocks_trans >> qexists_tac `cs1` >> simp[] >>
      irule same_blocks_trans >> qexists_tac `cs2` >> simp[]) >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac,
    irule assignment_frame_trans >> qexists_tac `ss1` >> simp[] >>
    irule assignment_frame_trans >> qexists_tac `ss2` >> simp[]]
QED

Theorem bytes_topic_operand_hash:
  !tenv ptr_op cap v ss addr.
    topic_value_rel tenv (ptr_op,BaseT (BytesT (Dynamic cap))) v ss /\ eval_operand ptr_op ss = SOME addr ==>
    SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64
      (read_memory (w2n (addr+32w)) (w2n (mload (w2n addr) ss)) ss))) =
      encode_event_topic (BaseT (BytesT (Dynamic cap))) v
Proof
  rpt gen_tac >> strip_tac >> fs[topic_value_rel_def, is_bytestring_type_def] >>
  drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (BytesV bs) (w2n addr) ss.vs_memory` >> Cases_on `bs = []`
  >- gvs[val_in_memory_def, mem_word_at_eq_mload, read_memory_def,
       encode_event_topic_def, is_event_bytestring_type_def, word_of_bytes_be_def] >>
  `0 < LENGTH bs` by (Cases_on `bs` >> gvs[]) >>
  `w2n addr + 32 < 2 ** 256` by
    (irule bytestring_header_in_range >> qexists_tac `LENGTH bs` >> fs[val_memory_size_def]) >>
  `LENGTH bs < 2 ** 256` by
    (drule (cj 1 evaluate_bytestring_bound) >> simp[] >>
     `dimword(:256) = 2 ** 256` by EVAL_TAC >> fs[] >> decide_tac) >>
  drule_all bytes_topic_memory >> simp[encode_event_topic_def, is_event_bytestring_type_def]
QED

Theorem string_topic_operand_hash:
  !tenv ptr_op cap v ss addr.
    topic_value_rel tenv (ptr_op,BaseT (StringT cap)) v ss /\ eval_operand ptr_op ss = SOME addr ==>
    SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64
      (read_memory (w2n (addr+32w)) (w2n (mload (w2n addr) ss)) ss))) =
      encode_event_topic (BaseT (StringT cap)) v
Proof
  rpt gen_tac >> strip_tac >> fs[topic_value_rel_def, is_bytestring_type_def] >>
  drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (StringV s) (w2n addr) ss.vs_memory` >> Cases_on `s = ""`
  >- gvs[val_in_memory_def, mem_word_at_eq_mload, read_memory_def,
       encode_event_topic_def, is_event_bytestring_type_def, word_of_bytes_be_def] >>
  `0 < LENGTH s` by (Cases_on `s` >> gvs[]) >>
  `w2n addr + 32 < 2 ** 256` by
    (irule bytestring_header_in_range >> qexists_tac `LENGTH s` >> fs[val_memory_size_def]) >>
  `LENGTH s < 2 ** 256` by
    (drule (cj 2 evaluate_bytestring_bound) >> simp[] >>
     `dimword(:256) = 2 ** 256` by EVAL_TAC >> fs[] >> decide_tac) >>
  `val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV (MAP (n2w o ORD) s)) (w2n addr) ss.vs_memory` by
    gvs[val_in_memory_def] >>
  `LENGTH (MAP (n2w o ORD) s : byte list) < 2 ** 256` by fs[] >>
  drule_all bytes_topic_memory >> simp[encode_event_topic_def, is_event_bytestring_type_def]
QED

Theorem bytestring_topic_operand_hash:
  !tenv ptr_op ty v ss addr.
    topic_value_rel tenv (ptr_op,ty) v ss /\ is_bytestring_type ty /\ eval_operand ptr_op ss = SOME addr ==>
    SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64
      (read_memory (w2n (addr+32w)) (w2n (mload (w2n addr) ss)) ss))) = encode_event_topic ty v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bound))` >> Cases_on `bound` >> gvs[is_bytestring_type_def]) >>
  FIRST [drule_all bytes_topic_operand_hash >> simp[], drule_all string_topic_operand_hash >> simp[]]
QED

Theorem compile_topic_value_operands:
  !tenv ptr_op ty v cs op cs' ss.
    topic_value_rel tenv (ptr_op,ty) v ss /\
    compile_encode_log_topic ptr_op (is_bytestring_type ty) cs = (op,cs') /\
    abi_operand_before cs.cs_next_var ptr_op ==>
    ?out. run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand op out = encode_event_topic ty v /\
      same_blocks cs cs' /\ abi_operand_before cs'.cs_next_var op /\ cs.cs_next_var <= cs'.cs_next_var /\
      (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_bytestring_type ty`
  >- (`?addr. eval_operand ptr_op ss = SOME addr` by fs[topic_value_rel_def] >>
      `compile_encode_log_topic ptr_op T cs = (op,cs')` by fs[] >>
      drule_all bytestring_topic_operand_hash >> DISCH_TAC >>
      drule_all compile_bytestring_topic_operands >> strip_tac >> goal_assum drule >> simp[]) >>
  fs[topic_value_rel_def] >> gvs[] >>
  drule_all compile_word_topic_correct >> strip_tac >> gvs[] >>
  qexists_tac `ss` >> simp[run_inst_seq_def, emitted_insts_def, same_blocks_def]
QED

Theorem topic_value_rel_operand_frame:
  !tenv ptr_op ty v ss out.
    topic_value_rel tenv (ptr_op,ty) v ss /\ out.vs_memory = ss.vs_memory /\
    eval_operand ptr_op out = eval_operand ptr_op ss ==>
    topic_value_rel tenv (ptr_op,ty) v out
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `topic_value_rel _ _ _ _` mp_tac >>
  asm_simp_tac bool_ss [topic_value_rel_def]
QED
