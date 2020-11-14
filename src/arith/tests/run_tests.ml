
open OUnit

let props =
  List.flatten
    [ Test_simplex.props;
    ]

let () =
  CCFormat.set_color_default true;
  QCheck_runner.run_tests_main props

