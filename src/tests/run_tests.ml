let tests : unit Alcotest.test list =
  List.flatten
  @@ [
       [ Sidekick_test_simplex.tests ];
       [ Sidekick_test_minicc.tests ];
       Sidekick_test_util.tests;
     ]

let props =
  List.flatten [ Sidekick_test_simplex.props; Sidekick_test_util.props ]

let () =
  (*Sidekick_util.Log.set_debug 10;*)
  match Array.to_list Sys.argv with
  | a0 :: "alcotest" :: tl ->
    let argv = Array.of_list (a0 :: tl) in
    Alcotest.run ~argv ~and_exit:true "arith tests" tests
  | a0 :: "qcheck" :: tl ->
    let argv = Array.of_list (a0 :: tl) in
    CCFormat.set_color_default true;
    QCheck_runner.run_tests_main ~argv props
  | _ -> failwith "expected (qcheck|alcotest) as first arg"
