Theory vyperExternalHeadersTest
Ancestors
  vyperTypeContract vyperABIEntries vyperAST vyperContext
  jsonToVyperTopLevel
Libs
  cv_transLib

Theorem external_header_checks:
  function_header_ok Deploy Nonpayable F F "__init__"
    [("a",BaseT (UintT 8))] [] NoneT /\
  ~function_header_ok Deploy Nonpayable F F "__init__"
    [("a",BaseT (UintT 8))] [Literal (BaseT (UintT 8)) (IntL 5)] NoneT /\
  ~function_header_ok Deploy Nonpayable F F "__init__" [] []
    (BaseT (UintT 256)) /\
  ~function_header_ok External Pure T F "f" [] [] NoneT /\
  ~function_header_ok External Nonpayable F F "__default__"
    [("a",BaseT (UintT 256))] [] NoneT /\
  ~function_header_ok External Nonpayable F T "f" [] []
    (BaseT (BytesT (Fixed 10))) /\
  ~function_header_ok Internal Nonpayable F T "f" [] []
    (BaseT (BytesT (Dynamic 10))) /\
  function_header_ok External Nonpayable F T "f" [] []
    (BaseT (BytesT (Dynamic 10)))
Proof
  simp[function_header_ok_def]
QED

(* Shared selector collision used by the full checker tests. *)
Theorem external_selector_collision:
  abi_method_id FEMPTY "burn" [BaseT (UintT 256)] =
  abi_method_id FEMPTY "collate_propagate_storage"
    [BaseT (BytesT (Fixed 16))]
Proof
  CONV_TAC cv_eval
QED

Theorem pragma_pure_header:
  effective_decorators T ["external";"pure"] = ["external";"pure"] /\
  effective_decorators T ["external";"view"] =
    ["external";"view";"nonreentrant"] /\
  effective_decorators T ["external";"reentrant"] =
    ["external";"reentrant"]
Proof
  EVAL_TAC
QED
