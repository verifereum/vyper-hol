(* Public same-endpoint array frame contract; concrete primitives are integrated. *)
Theory abiEncoderWindowArrayFrameMem
Ancestors
  abiEncoderWindowArrayMem abiEncoderWindowPrimitiveFrameMem
  abiEncoderWindowArrayGrowthMem
  abiEncoderWindowMemFrame memContinuation abiEncoderWindowContract

Theorem window_array_strong_contract_mem_frame_from_primitives:
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t) ==>
  !dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src (AbiDynArray ei asz msz active)
      at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >>
  `!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t` by metis_tac[] >>
  drule window_array_strong_contract_mem >>
  strip_tac >> metis_tac[]
QED
