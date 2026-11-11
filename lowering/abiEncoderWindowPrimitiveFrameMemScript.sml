(* Public assembly of the S3 primitive endpoint frame interfaces. *)
Theory abiEncoderWindowPrimitiveFrameMem
Ancestors
  abiEncoderWindowSequenceFrameMem abiEncoderWindowPhaseFrameMem
  abiEncoderWindowLeavesMem abiEncoderWindowChildMem

Theorem window_copy_contract_mem_frame:
  !dst src st out st' ctx func s at av sb cap d.
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiCopy sz) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  ACCEPT_TAC window_copy_contract_mem
QED

Theorem window_word_contract_mem_frame:
  !dst src st out st' ctx func s at av sb cap d.
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src AbiPrimWord at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  ACCEPT_TAC window_word_contract_mem
QED

Theorem window_bytes_contract_mem_frame:
  !dst src st out st' ctx func s at av sb cap d.
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiBytestring maxlen) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  ACCEPT_TAC window_bytes_contract_mem
QED

Theorem window_child_prefix_run_mem_frame:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  fn_has_code st en func /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w slot) /\
  (!x. dst = Var x \/ dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  mem_word_at slot s.vs_memory = n2w off /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ fn_inst_ids_distinct func ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST ops) t = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w off) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x \/
         SND (SND ops) = Var x ==> not_fresh_at en x) /\
    t.vs_labels = s.vs_labels /\ mem_cont_sim ctx func s t /\
    window_mem_frame ctx func s t
Proof
  strip_tac >> drule_all window_child_prefix_run_mem >> metis_tac[]
QED
