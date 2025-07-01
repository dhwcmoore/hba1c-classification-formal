(* Main entrypoint *)

let () =
  let input =
    if Array.length Sys.argv < 2 then (
      print_endline "Usage: ./aqi_check <AQI>";
      exit 1
    ) else int_of_string Sys.argv.(1)
  in
  let category = Aqi_classification.classify_aqi input in
  Printf.printf "AQI %d is classified as: %s\n" input category
