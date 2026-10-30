(* Runtime simulation for the three instructions that hash a bytestring topic.
   TOP-LEVEL: compile_word_topic_execution_correct,
     compile_bytestring_topic_correct, compile_bytes_topic_correct,
     compile_string_topic_correct.
   Helpers give an exact frame for instructions that only assign an SSA value. *)
Theory eventTopicExecProps
Ancestors
  context compileEnv exprLoweringProps emitHelperProps emitHelper
  venomExecSemantics venomState venomInst vyperEvent vyperValue vfmState
  keccak ASCIInumbers valueEncoding byte words eventTopicProps
Libs wordsLib

Theorem compile_word_topic_execution_correct:
  compile_encode_log_topic ptr_op (is_bytestring_type ty) cs = (op,cs') /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  eval_operand ptr_op ss = SOME (typed_val_to_w256 tv v) /\
  fresh_vars_wrt cs ss ==>
  run_inst_seq (emitted_insts cs cs') ss = OK ss /\
  eval_operand op ss = encode_event_topic ty v /\
  same_blocks cs cs' /\ fresh_vars_wrt cs' ss
Proof
  strip_tac >> drule_all word_topic_encoding >> strip_tac >>
  gvs[compile_encode_log_topic_def, comp_return_def, emitted_insts_def,
      same_blocks_def, run_inst_seq_def]
QED

Theorem emit_op_assignment_frame:
  emit_op opc args cs = (op,cs') /\ fresh_vars_wrt cs ss /\
  step_inst_base (mk_inst cs.cs_next_id opc args
    [STRING #"%" (toString cs.cs_next_var)]) ss =
    OK (update_var (STRING #"%" (toString cs.cs_next_var)) value ss) ==>
  ?ss'. run_inst_seq (emitted_insts cs cs') ss = OK ss' /\
    eval_operand op ss' = SOME value /\ same_blocks cs cs' /\
    fresh_vars_wrt cs' ss' /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss' = SOME w) /\
    ss' with vs_vars := ss.vs_vars = ss
Proof
  rw[] >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, eval_operand_update_var] >>
  drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule fresh_vars_wrt_advance >> simp[] >>
      goal_assum $ drule_at Any >> gvs[]) >>
  conj_tac
  >- (rw[] >> irule eval_operand_update_fresh >> rw[] >>
      goal_assum $ drule_at Any >> gvs[]) >>
  simp[update_var_def]
QED

Theorem emit_op_ADD_frame:
  emit_op ADD [a;b] cs = (op,cs') /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt cs ss ==>
  ?ss'. run_inst_seq (emitted_insts cs cs') ss = OK ss' /\
    eval_operand op ss' = SOME (x+y) /\ same_blocks cs cs' /\
    fresh_vars_wrt cs' ss' /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss' = SOME w) /\
    ss' with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >> irule emit_op_assignment_frame >>
  conj_tac
  >- (qexistsl_tac [`[a;b]`,`ADD`] >> simp[step_ADD]) >> simp[]
QED

Theorem emit_op_MLOAD_frame:
  emit_op MLOAD [a] cs = (op,cs') /\ eval_operand a ss = SOME x /\
  fresh_vars_wrt cs ss ==>
  ?ss'. run_inst_seq (emitted_insts cs cs') ss = OK ss' /\
    eval_operand op ss' = SOME (mload (w2n x) ss) /\ same_blocks cs cs' /\
    fresh_vars_wrt cs' ss' /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss' = SOME w) /\
    ss' with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >> irule emit_op_assignment_frame >>
  conj_tac
  >- (qexistsl_tac [`[a]`,`MLOAD`] >> simp[step_MLOAD]) >> simp[]
QED

Theorem emit_op_SHA3_frame:
  emit_op SHA3 [a;b] cs = (op,cs') /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt cs ss ==>
  ?ss'. run_inst_seq (emitted_insts cs cs') ss = OK ss' /\
    eval_operand op ss' = SOME
      (word_of_bytes T (0w:bytes32)
        (Keccak_256_w64 (read_memory (w2n x) (w2n y) ss))) /\
    same_blocks cs cs' /\ fresh_vars_wrt cs' ss' /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss' = SOME w) /\
    ss' with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >> irule emit_op_assignment_frame >>
  conj_tac
  >- (qexistsl_tac [`[a;b]`,`SHA3`] >>
      simp[Once step_inst_base_def, mk_inst_def, read_memory_def]) >> simp[]
QED

Theorem assignment_frame_memory:
  ss' with vs_vars := ss.vs_vars = ss ==> ss'.vs_memory = ss.vs_memory
Proof
  disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >> simp[]
QED

Theorem assignment_frame_trans:
  ss1 with vs_vars := ss.vs_vars = ss /\
  ss2 with vs_vars := ss1.vs_vars = ss1 ==>
  ss2 with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >>
  qpat_x_assum `ss2 with vs_vars := _ = _`
    (mp_tac o AP_TERM ``\s:venom_state. s with vs_vars := ss.vs_vars``) >>
  simp[]
QED

Theorem compile_bytestring_topic_correct:
  compile_encode_log_topic ptr_op T cs = (op,cs') /\
  eval_operand ptr_op ss = SOME addr /\ fresh_vars_wrt cs ss ==>
  ?ss'. run_inst_seq (emitted_insts cs cs') ss = OK ss' /\
    eval_operand op ss' = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64
        (read_memory (w2n (addr+32w)) (w2n (mload (w2n addr) ss)) ss))) /\
    same_blocks cs cs' /\ fresh_vars_wrt cs' ss' /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss' = SOME w) /\
    ss' with vs_vars := ss.vs_vars = ss
Proof
  simp[compile_encode_log_topic_def, comp_bind_def] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [ptr_op;Lit 32w] cs = (data_op,cs1)` >>
  rename1 `emit_op MLOAD [ptr_op] cs1 = (length_op,cs2)` >>
  imp_res_tac emit_op_extends >>
  `?ss1. run_inst_seq (emitted_insts cs cs1) ss = OK ss1 /\
    eval_operand data_op ss1 = SOME (addr+32w) /\ same_blocks cs cs1 /\
    fresh_vars_wrt cs1 ss1 /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss1 = SOME w) /\
    ss1 with vs_vars := ss.vs_vars = ss`
    by (irule emit_op_ADD_frame >> conj_tac
        >- (qexistsl_tac [`ptr_op`,`Lit 32w`] >> simp[eval_operand_def]) >>
        simp[]) >>
  `eval_operand ptr_op ss1 = SOME addr` by (first_x_assum irule >> simp[]) >>
  drule_all emit_op_MLOAD_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss2` >>
  `ss1.vs_memory = ss.vs_memory` by (irule assignment_frame_memory >> simp[]) >>
  `ss2.vs_memory = ss1.vs_memory` by (irule assignment_frame_memory >> simp[]) >>
  `eval_operand data_op ss2 = SOME (addr+32w)` by (first_x_assum irule >> simp[]) >>
  drule_all emit_op_SHA3_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs2 cs') ss2 = OK ss3` >>
  qexists_tac `ss3` >>
  conj_tac
  >- (mp_tac (Q.SPECL [`cs`,`cs1`,`cs2`,`cs'`,`ss`,`ss1`,`ss2`,`ss3`]
       run_emitted_compose3) >> simp[]) >>
  simp[read_memory_def, mload_def] >>
  conj_tac >- (irule same_blocks_trans >> qexists_tac `cs1` >> simp[] >>
              irule same_blocks_trans >> qexists_tac `cs2` >> simp[]) >>
  irule assignment_frame_trans >> qexists_tac `ss1` >> simp[] >>
  irule assignment_frame_trans >> qexists_tac `ss2` >> simp[]
QED

(* The pointer addition is a word operation. The region premise rules out
   wrapping the payload pointer; the length premise rules out length truncation. *)
Theorem bytes_topic_memory:
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs)
    (w2n (addr:bytes32)) ss.vs_memory /\
  w2n addr + 32 < 2 ** 256 /\ LENGTH bs < 2 ** 256 ==>
  word_of_bytes T (0w:bytes32) (Keccak_256_w64
    (read_memory (w2n (addr+32w)) (w2n (mload (w2n addr) ss)) ss)) =
  word_of_bytes_be (Keccak_256_w64 bs)
Proof
  simp[val_in_memory_def, mem_word_at_def, mem_bytes_at_def, mload_def,
       read_memory_def, word_of_bytes_be_def] >> strip_tac >>
  `dimword (:256) = 2 ** 256` by EVAL_TAC >> simp[w2n_add_2]
QED

Theorem compile_bytes_topic_correct:
  compile_encode_log_topic ptr_op T cs = (op,cs') /\
  eval_operand ptr_op ss = SOME addr /\ fresh_vars_wrt cs ss /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs)
    (w2n addr) ss.vs_memory /\
  w2n addr + 32 < 2 ** 256 /\ LENGTH bs < 2 ** 256 ==>
  ?ss'. run_inst_seq (emitted_insts cs cs') ss = OK ss' /\
    eval_operand op ss' = encode_event_topic (BaseT (BytesT (Dynamic cap))) (BytesV bs) /\
    same_blocks cs cs' /\ fresh_vars_wrt cs' ss' /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss' = SOME w) /\
    ss' with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >> drule_all compile_bytestring_topic_correct >> strip_tac >>
  drule_all bytes_topic_memory >> strip_tac >>
  goal_assum drule >>
  simp[encode_event_topic_def, is_event_bytestring_type_def]
QED

Theorem compile_string_topic_correct:
  compile_encode_log_topic ptr_op T cs = (op,cs') /\
  eval_operand ptr_op ss = SOME addr /\ fresh_vars_wrt cs ss /\
  val_in_memory (BaseTV (StringT cap)) (StringV s)
    (w2n addr) ss.vs_memory /\
  w2n addr + 32 < 2 ** 256 /\ LENGTH s < 2 ** 256 ==>
  ?ss'. run_inst_seq (emitted_insts cs cs') ss = OK ss' /\
    eval_operand op ss' = encode_event_topic (BaseT (StringT cap)) (StringV s) /\
    same_blocks cs cs' /\ fresh_vars_wrt cs' ss' /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss' = SOME w) /\
    ss' with vs_vars := ss.vs_vars = ss
Proof
  strip_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic cap)))
     (BytesV (MAP (n2w o ORD) s)) (w2n addr) ss.vs_memory`
    by gvs[val_in_memory_def] >>
  `LENGTH (MAP (n2w o ORD) s : byte list) < 2 ** 256` by fs[] >>
  drule_all compile_bytes_topic_correct >> strip_tac >>
  goal_assum drule >>
  gvs[encode_event_topic_def, is_event_bytestring_type_def]
QED
