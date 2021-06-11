
let tests : unit Alcotest.test list = [
  Test_simplex2.tests;
]

let props =
  List.flatten
    [ Test_simplex2.props;
    ]

let () =
  match Array.to_list Sys.argv with
  | a0::"alcotest"::tl ->
    Sidekick_util.Log.set_debug 50;
    let argv= Array.of_list (a0::tl) in
    Alcotest.run ~argv ~and_exit:true "arith tests" tests;
  | a0::"qcheck"::tl ->
    let argv= Array.of_list (a0::tl) in
    CCFormat.set_color_default true;
    QCheck_runner.run_tests_main ~argv props
  | _ -> failwith "expected (qcheck|alcotest) as first arg"
