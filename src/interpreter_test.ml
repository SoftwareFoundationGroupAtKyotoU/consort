open OUnit2

let test1 _test_ctxt =
  assert_equal
    (Interpreter.eval_prog (AstUtil.parse_string "{ 1 + 1 }"))
    (Interpreter.IntV 2)

let suite =
  "suite">:::
    [
      "test1">:: test1
    ]

let () =
  run_test_tt_main suite

