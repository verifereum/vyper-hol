open HolKernel boolLib bossLib Parse wordsLib
     vyperSmallStepTheory vyperAbiTheory contractABITheory
     vyperTestLib cv_transLib

val () = new_theory "vyperTest";

val sender_addr = “1001w: address”

Definition deploy_tx_def:
  deploy_tx addr args value =
  <| sender := ^sender_addr
   ; target := addr
   ; function_name := "__init__"
   ; args := args
   ; value := value
   |>
End

val () = cv_auto_trans deploy_tx_def;

(* TODO: move *)
val () = cv_auto_trans vyperInterpreterTheory.initial_machine_state_def;

Definition CHR_o_w2n_def:
  CHR_o_w2n (b: byte) = CHR (w2n b)
End

val CHR_o_w2n_pre_def = cv_auto_trans_pre CHR_o_w2n_def;

Theorem CHR_o_w2n_pre[cv_pre]:
  CHR_o_w2n_pre x
Proof
  rw[CHR_o_w2n_pre_def]
  \\ qspec_then`x`mp_tac wordsTheory.w2n_lt
  \\ rw[]
QED

Theorem CHR_o_w2n_eq:
  CHR_o_w2n = CHR o w2n
Proof
  rw[FUN_EQ_THM, CHR_o_w2n_def]
QED

val abi_to_vyper_pre_def =
  vyperAbiTheory.abi_to_vyper_def
  |> REWRITE_RULE[GSYM CHR_o_w2n_eq]
  |> cv_auto_trans_pre;

Theorem abi_to_vyper_pre[cv_pre]:
  (!v0 v. abi_to_vyper_pre v0 v) ∧
  (!v0 v. abi_to_vyper_list_pre v0 v)
Proof
  ho_match_mp_tac vyperAbiTheory.abi_to_vyper_ind
  \\ rw[]
  \\ rw[Once abi_to_vyper_pre_def]
QED
(* -- *)

val json_path = "test_export.py.json";

val named_traces = read_test_json json_path;

val [(test_name, test_traces)] = named_traces;

(* TODO: define these traces in HOL so we can define a test runner? *)

val Deployment { deployedAddress = addr,
                 callData = data,
                 sourceCode = src,
                 abi = abi,
                 value = value, ...} = el 1 test_traces

val [Function {name, inputs, ...}] = abi

val Call { callData, value, target,
           sender, static, expectedOutput, ... } = el 2 test_traces

val abi_type_ty = mk_thy_type{Tyop="abi_type",Thy="contractABI",Args=[]}

val name_tm = stringSyntax.fromMLstring name
val args = listSyntax.mk_list(List.map #2 inputs, abi_type_ty)
val vyargtys = “TupleT [bool]” (* get from src *)

val fsel_thm = cv_eval “TAKE 4 ^callData = function_selector ^name_tm ^args”;

val dec_args_thm = cv_eval “abi_to_vyper ^vyargtys $
                            dec (Tuple ^args) (DROP 4 ^callData)”;

val vyargs = dec_args_thm |> concl |> rhs |> rand |> rand;

(*
cv_eval “
  load_contract initial_machine_state
  (deploy_tx ^addr [] ^value) ^src”
*)

val () = export_theory();
