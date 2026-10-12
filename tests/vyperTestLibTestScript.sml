Theory vyperTestLibTest
Libs vyperTestLib

fun source code = JSON.OBJECT [("source_code", JSON.STRING code)];
fun delegate_call enabled = JSON.OBJECT [
  ("ast_type", JSON.STRING "Call"),
  ("func", JSON.OBJECT [("ast_type", JSON.STRING "Name"),
                        ("id", JSON.STRING "raw_call")]),
  ("keywords", JSON.ARRAY [JSON.OBJECT [
    ("ast_type", JSON.STRING "keyword"),
    ("arg", JSON.STRING "is_delegate_call"),
    ("value", JSON.OBJECT [("ast_type", JSON.STRING "NameConstant"),
                           ("value", JSON.BOOL enabled)])]])];

fun expect label expected jsons =
  if unsupported_source_reason_for jsons = expected then ()
  else raise Fail ("source classification: " ^ label);

val _ = expect "calldata len" NONE [source "return len(msg.data)"];
val _ = expect "calldata slice" NONE [source "return slice(msg.data, 0, 4)"];
val _ = expect "calldata raw_call" NONE
  [source "raw_call(target, msg.data, max_outsize=32)"];
val _ = expect "delegate false" NONE
  [source "raw_call(target, msg.data, is_delegate_call = False)",
   delegate_call false];
val delegate_reason = SOME
  "unsupported feature: delegate raw_call; issue=https://github.com/verifereum/vyper-hol/issues/39";
val _ = expect "delegate independent of source spacing" delegate_reason
  [source "raw_call(target, msg.data, is_delegate_call = True)",
   delegate_call true];
val _ = expect "delegate in fixture" delegate_reason
  [JSON.OBJECT [("traces", JSON.ARRAY [source "proxy", delegate_call true])],
   source "caller"];
val _ = expect "delegate spelling in comment is not a feature" NONE
  [source "# is_delegate_call=True\nreturn len(msg.data)"];
val _ = expect "gas retained" (SOME "unsupported source pattern: msg.gas")
  [source "raw_call(target, msg.data, gas=msg.gas)", delegate_call true];
val _ = expect "explicit gas retained" (SOME "unsupported source pattern: gas=")
  [source "raw_call(target, msg.data, gas=1000)"];
val _ = expect "negative missing source" (SOME "missing source_code") [];
val _ = expect "blank source" (SOME "blank source_code") [source " \n"];
